open! IStd

module F = Format
module L = Logging
module Domain = LooperDomain


(* module Payload = SummaryPayload.Make (struct
  type t = Domain.EdgeExp.summary

  let update_payloads summary (payloads : Payloads.t) = {payloads with looper= Some summary}

  let of_payloads (payloads : Payloads.t) = payloads.looper
end) *)

module Payload = SummaryPayload.Make (struct
  type t = Domain.EdgeExp.summary

  let field = Payloads.Fields.looper
end)

let log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.printf fmt

module TransferFunctions (ProcCFG : ProcCfg.S) = struct
  module CFG = ProcCFG
  module Domain = Domain

  type nonrec extras = (Typ.t Domain.PvarMap.t * Typ.t Domain.PvarMap.t * Typ.t Domain.PvarMap.t)

  let pp_session_name node fmt = F.fprintf fmt "looper %a" CFG.Node.pp_id (CFG.Node.id node)

  (* Take an abstract state and instruction, produce a new abstract state *)
  let exec_instr : Domain.t -> extras ProcData.t -> CFG.Node.t -> Sil.instr -> Domain.t =
    fun astate {summary; tenv; extras} node instr ->

    let open Domain in

    let locals, formals, type_map = extras in

    let is_exit_node = match ProcCFG.Node.kind node with
      | Procdesc.Node.Exit_node -> true
      | _ -> false
    in

    let is_start_node = match ProcCFG.Node.kind node with
      | Procdesc.Node.Start_node -> true
      | _ -> false
    in

    let is_decl_node = match ProcCFG.Node.kind node with
    | Procdesc.Node.Stmt_node DeclStmt -> true
    | _ -> false
    in

    (* Extracts all formals as pvars from expression *)
    let rec extract_formals pvar_exp acc = match pvar_exp with
    | Exp.BinOp (op, lexp, rexp) -> (
      let acc = extract_formals lexp acc in
      extract_formals rexp acc
    )
    | Exp.UnOp (_, sub_exp, _) -> (
      extract_formals sub_exp acc
    )
    | Exp.Lvar pvar when PvarMap.mem pvar formals -> PvarSet.add pvar acc
    | _ -> acc
    in

    let equal_if_kind x y = Int.equal 0 (Sil.compare_if_kind x y) in

    let astate = match instr with
    | Prune (cond, loc, branch, kind) -> (
      let pvar_condition = EdgeExp.replace_idents cond astate.ident_map in

      log "[PRUNE] (%a) | %a\n" Location.pp loc EdgeExp.pp pvar_condition;
      let location_cmp : Location.t -> Location.t -> bool = fun loc_a loc_b ->
        loc_a.line > loc_b.line
      in
      
      let prune_node = DCP.Node.Prune (kind, loc) in
      (* let prune_node = DCP.Node.make lts_prune_loc in *)
      let loop_prune = is_loop_prune kind in

      let process_prune astate backedge = 
        let path_end = List.last astate.path in
        let graph_nodes = DCP.NodeSet.add prune_node astate.graph_nodes in
        let edge_data = DCP.EdgeData.add_invariants astate.edge_data (get_unmodified_pvars astate) in
        let edge_data = DCP.EdgeData.set_path_end edge_data path_end in
        let edge_data = if backedge then (
          DCP.EdgeData.set_backedge edge_data
        ) else edge_data
        in
        let new_lts_edge = DCP.E.create astate.last_node edge_data prune_node in
        let graph_edges = DCP.EdgeSet.add new_lts_edge astate.graph_edges in
        { astate with graph_edges = graph_edges; graph_nodes = graph_nodes; }
      in

      let astate, consec_prune = match astate.last_node with
      | DCP.Node.Join (lhs, rhs) -> (
        let edge_data = DCP.EdgeData.add_invariants astate.edge_data (get_unmodified_pvars astate) in
        let graph_nodes = DCP.NodeSet.add prune_node astate.graph_nodes in

        let is_direct_backedge = DCP.Node.equal prune_node lhs || DCP.Node.equal prune_node rhs in
        if is_direct_backedge then (
          (* Discard join node and all edges poiting to it and instead make
           * one direct backedge with variables modified inside the loop *)
          let src, edge_data, _ = List.find_exn (DCP.EdgeSet.elements astate.incoming_edges) ~f:(fun edge ->
            DCP.Node.equal (DCP.E.src edge) prune_node
          )
          in
          let edge_data = DCP.EdgeData.set_backedge edge_data in
          let backedge = DCP.E.create src edge_data prune_node in
          let graph_edges = DCP.EdgeSet.add backedge astate.graph_edges in
          let graph_nodes = DCP.NodeSet.remove astate.last_node graph_nodes in
          { astate with graph_edges = graph_edges; graph_nodes = graph_nodes; }, false
        ) else (
          let is_backedge = match lhs, rhs with
          | DCP.Node.Prune (_, lhs), DCP.Node.Prune (_, rhs) -> (
            location_cmp lhs loc || location_cmp rhs loc
          )
          | DCP.Node.Prune (_, lhs), _ -> location_cmp lhs loc
          | _, DCP.Node.Prune (_, rhs) -> location_cmp rhs loc
          | _ -> false
          in
          (* Add all accumulated edges pointing to aggregated join node and
            * new edge pointing from aggregated join node to this prune node *)
          let edge_count = DCP.EdgeSet.cardinal astate.incoming_edges in
          let is_empty_edge = DCP.EdgeData.equal astate.edge_data DCP.EdgeData.empty in
          let same_origin = match astate.last_node with
          | DCP.Node.Join (lhs, rhs) -> DCP.Node.equal lhs rhs
          | _ -> false
          in
          if not (loop_prune) && same_origin && is_empty_edge then (
            (* LTS simplification, skip simple JOIN node and redirect edges pointing to it *)
            let graph_edges = DCP.EdgeSet.map (fun (src, data, _) ->
              (src, data, prune_node)
            ) astate.incoming_edges
            in
            let graph_nodes = DCP.NodeSet.remove astate.last_node graph_nodes in
            let graph_edges = (DCP.EdgeSet.union astate.graph_edges graph_edges) in
            { astate with graph_edges = graph_edges; graph_nodes = graph_nodes; }, false
          ) else if Int.equal edge_count 1 then (
            (* JOIN node with single incoming edge (useless node).
              * Redirect incoming edge to prune node and delete join node *)
            let graph_edges = DCP.EdgeSet.map (fun (src, edge_data, _) ->
              let edge_data = if is_backedge then DCP.EdgeData.set_backedge edge_data else edge_data in
              (src, edge_data, prune_node)
            ) astate.incoming_edges
            in
            let graph_nodes = DCP.NodeSet.remove astate.last_node graph_nodes in
            let graph_edges = (DCP.EdgeSet.union astate.graph_edges graph_edges) in
            { astate with graph_edges = graph_edges; graph_nodes = graph_nodes; }, false
          ) else (
            let path_end = List.last astate.path in
            let edge_data = DCP.EdgeData.set_path_end edge_data path_end in
            let edge_data = if is_backedge then DCP.EdgeData.set_backedge edge_data else edge_data in
            let new_lts_edge = DCP.E.create astate.last_node edge_data prune_node in
            let graph_edges = DCP.EdgeSet.add new_lts_edge astate.graph_edges in
            let graph_edges = DCP.EdgeSet.union astate.incoming_edges graph_edges in
            { astate with graph_edges = graph_edges; graph_nodes = graph_nodes; }, false
          )
        )
      )
      | DCP.Node.Prune (last_prune_kind, last_loc) -> (
        if not loop_prune && location_cmp last_loc loc then (
          (* ----Does not seem to occur in current version of Infer----
           * Do not create a backedge from single branch of "if" and 
           * wait for backedge from joined node *)
          assert(false)
        ) else if loop_prune && (equal_if_kind last_prune_kind kind) && PvarSet.is_empty astate.edge_modified then (
          astate, true
        ) else (
          let is_backedge = location_cmp last_loc loc in
          let astate = process_prune astate is_backedge in
          { astate with 
            edge_data = DCP.EdgeData.empty; 
            edge_modified = PvarSet.empty;
          }, false
        )
      )
      | DCP.Node.Start _ -> (
        process_prune astate false, false
      )
      | DCP.Node.Exit -> (
        assert(false)
      )
      in

      let normalized_cond = EdgeExp.normalize_condition pvar_condition in

      let astate = if EdgeExp.is_int normalized_cond type_map then (
        let astate = if branch && (loop_prune || Path.in_loop astate.path) then (
          (* Derive norm from prune condition.
          * [x > y] -> [x - y] > 0
          * [x >= y] -> [x - y + 1] > 0 *)
          match normalized_cond with
          | EdgeExp.BinOp (op, lexp, rexp) -> (
            let process_gt lhs rhs =
              let lhs_is_zero = EdgeExp.is_zero lhs in
              let rhs_is_zero = EdgeExp.is_zero rhs in
              if lhs_is_zero && rhs_is_zero then EdgeExp.zero
              else if lhs_is_zero then EdgeExp.UnOp (Unop.Neg, rhs, None)
              else if rhs_is_zero then lhs
              else EdgeExp.BinOp (Binop.MinusA None, lhs, rhs)
            in

            let process_op op = match op with
              | Binop.Gt -> Some (process_gt lexp rexp)
              | Binop.Ge -> Some (EdgeExp.BinOp (Binop.PlusA None, (process_gt lexp rexp), EdgeExp.one))
              | _ -> None
            in
            match process_op op with
            | Some new_norm -> (
              let is_modified = match new_norm with
              | EdgeExp.Var pvar -> PvarSet.mem pvar astate.loop_modified
              | _ -> false
              in
              if not loop_prune && not is_modified then (
                (* Prune on loop path but not loop head. Norm is only potential,
                * must be confirmed by increment/decrement on this loop path *)
                { astate with potential_norms = EdgeExp.Set.add new_norm astate.potential_norms; }
              ) else (
                { astate with initial_norms = EdgeExp.Set.add new_norm astate.initial_norms; }
              )
            ) 
            | None -> astate
          )
          | _ -> L.(die InternalError)"Unsupported PRUNE expression!"
        ) else (
          astate
        )
        in
        let edge_data = if consec_prune then (
          DCP.EdgeData.add_condition astate.edge_data normalized_cond
        ) else DCP.EdgeData.add_condition DCP.EdgeData.empty normalized_cond
        in
        { astate with edge_data = edge_data }
        
      ) else (
        if consec_prune then astate 
        else { astate with edge_data = DCP.EdgeData.empty } 
      )
      in
      { astate with
        path = if consec_prune then astate.path else astate.path @ [(kind, branch, loc)];
        edge_modified = PvarSet.empty;
        (* edge_data = edge_data; *)
        last_node = if consec_prune then astate.last_node else prune_node;
        incoming_edges = DCP.EdgeSet.empty;
      }
    )
    | Store {e1=Exp.Lvar assigned; e2=rexp; loc} -> (
      let pvar_rexp = EdgeExp.replace_idents rexp astate.ident_map in
      let pvar_rexp = match pvar_rexp with
      | EdgeExp.Call (_, _, _, summary) -> (
        match summary.return_bound with
        | Some ret_bound -> ret_bound
        | None -> pvar_rexp
      )
      | _ -> pvar_rexp
      in
      log "[STORE] (%a) | %a = %a | %B\n" Location.pp loc Pvar.pp_value assigned
      EdgeExp.pp pvar_rexp is_decl_node;

      (* Substitute rexp based on previous assignments,
       * eg. [beg = i; end = beg;] becomes [beg = i; end = i] *)
      let pvar_rexp = match pvar_rexp with
      | EdgeExp.BinOp (Binop.PlusA _, EdgeExp.Var lexp, EdgeExp.Const (Const.Cint c1)) -> (
        (* [BINOP] PVAR + CONST *)
        match (DCP.EdgeData.get_assignment_rhs astate.edge_data lexp) with
        | EdgeExp.BinOp (Binop.PlusA _, lexp, EdgeExp.Const (Const.Cint c2)) -> (
          (* [BINOP] (PVAR + C1) + C2 -> PVAR + (C1 + C2) *)
          let const = EdgeExp.Const (Const.Cint (IntLit.add c1 c2)) in
          EdgeExp.BinOp (Binop.PlusA None, lexp, const)
        )
        | _ -> pvar_rexp
      )
      | EdgeExp.Var rhs_pvar -> (
        DCP.EdgeData.get_assignment_rhs astate.edge_data rhs_pvar
      )
      | _ -> pvar_rexp
      in
      let is_plus_minus_op op = match op with
      | Binop.PlusA _ | Binop.MinusA _ -> true | _ -> false
      in

      let astate = match pvar_rexp with 
      | EdgeExp.BinOp (op, EdgeExp.Var pvar, EdgeExp.Const (Const.Cint _)) when Pvar.equal assigned pvar -> (
        let assigned_exp = EdgeExp.Var assigned in
        if is_plus_minus_op op && EdgeExp.Set.mem assigned_exp astate.potential_norms then (
          { astate with
            potential_norms = EdgeExp.Set.remove assigned_exp astate.potential_norms;
            initial_norms = EdgeExp.Set.add assigned_exp astate.potential_norms;
          }
        ) else (
          astate
        )
      )
      | _ -> astate
      in
      let loop_modified = if Path.in_loop astate.path then (
        PvarSet.add assigned astate.loop_modified
      ) else astate.loop_modified 
      in
      let edge_data = DCP.EdgeData.add_assignment astate.edge_data assigned pvar_rexp in
      let astate = if Pvar.is_return assigned then (
        edge_data.exit_edge <- true;
        { astate with 
          initial_norms = EdgeExp.Set.add (EdgeExp.Var assigned) astate.potential_norms;
          edge_data = edge_data;
        }
      ) else astate
      in
      let locals = if is_decl_node then PvarSet.add assigned astate.locals
      else astate.locals in
      { astate with
        locals = locals;
        edge_data = edge_data;
        edge_modified = PvarSet.add assigned astate.edge_modified;
        loop_modified = loop_modified;
      }
    )
    | Load {id=ident; e=lexp; loc} -> (
      log "[LOAD] (%a) | %a = %a\n" Location.pp loc Ident.pp ident Exp.pp lexp;
      let ident_map = match lexp with
      | Exp.Lvar pvar -> Ident.Map.add ident (EdgeExp.Var pvar) astate.ident_map
      | Exp.Var id -> (
        let pvar = Ident.Map.find id astate.ident_map in
        Ident.Map.add ident pvar astate.ident_map
      )
      | _ -> L.(die InternalError)"Unsupported LOAD lhs-expression type!"
      in
      { astate with ident_map = ident_map }
    )
    | Call ((ret_id, ret_type), Exp.Const (Const.Cfun callee_pname), args, loc, _) -> (
      log "[CALL] (%a) | %a\n" Location.pp loc Typ.Procname.pp callee_pname;
      let new_summary = match Payload.read ~caller_summary:summary ~callee_pname:callee_pname with
      | Some new_summary -> new_summary
      | None -> L.(die InternalError)"Missing summary!"
      in
      let args = List.map args ~f:(fun (arg, typ) ->
        (EdgeExp.replace_idents arg astate.ident_map, typ)) 
      in
      log "   FormalMap: %a\n" FormalMap.pp new_summary.formal_map;
      log "   Formal Bound: %a\n" EdgeExp.pp new_summary.bound;
      let subst_bound = EdgeExp.subst new_summary.bound args new_summary.formal_map in
      let subst_ret_bound = match new_summary.return_bound with
      | Some ret_bound -> Some (EdgeExp.subst ret_bound args new_summary.formal_map)
      | None -> None
      in
      log "   Instantiated Bound: %a\n" EdgeExp.pp subst_bound;
      let new_summary = { new_summary with 
        bound = subst_bound;
        return_bound = subst_ret_bound;
      } 
      in
      let call = EdgeExp.Call (ret_type, callee_pname, args, new_summary) in
      let edge_data = { astate.edge_data with 
        calls = CallSiteSet.add (call, loc) astate.edge_data.calls
      }
      in
      { astate with 
        ident_map = Ident.Map.add ret_id call astate.ident_map;
        edge_data = edge_data;
      }
    )
    | Metadata metadata -> (
      log "[METADATA]\n";
      if is_decl_node then log "  Decl node\n";
      if is_start_node then (
        let instrs = CFG.instrs node in
        log "  Start node\n";
        let count = Instrs.count instrs in
        log "  Instr count: %d\n" count;
      );

      let astate = if is_exit_node then (
        log "  Exit node\n";
        let exit_node = DCP.Node.Exit in
        let path_end = List.last astate.path in
        let edge_data = DCP.EdgeData.set_path_end astate.edge_data path_end in
        let new_lts_edge = DCP.E.create astate.last_node edge_data exit_node in
        let graph_edges = DCP.EdgeSet.add new_lts_edge astate.graph_edges in
        { astate with
          graph_nodes = DCP.NodeSet.add exit_node astate.graph_nodes;
          graph_edges = DCP.EdgeSet.union astate.incoming_edges graph_edges;
        }
      ) else (
        astate
      )
      in

      match metadata with
      | Nullify (_, loc) -> (
        log "  [NULLIFY] %a\n" Location.pp loc;
        astate
      )
      | Abstract loc -> (
        log "  [ABSTRACT] %a\n" Location.pp loc;
        astate
      )
      | ExitScope (_, loc) -> (
        log "  [ExitScope] %a\n" Location.pp loc;
        astate
      )
      | Skip -> (
        log "  [Skip]\n"; 
        astate
      )
      | VariableLifetimeBegins (pvar, _, _) -> (
        log "  [DECLARE] %a\n" Pvar.pp_value pvar;
        astate
      )
    )
    | _ -> (
      log "[UNKNOWN INSTRUCTION]\n";
      astate
    )
    in
    astate
 end


module CFG = ProcCfg.NormalOneInstrPerNode
(* module CFG = ProcCfg.Normal *)

(* module Analyzer = AbstractInterpreter.Make (CFG) (TransferFunctions) *)
module Analyzer = AbstractInterpreter.MakeWTO (TransferFunctions (CFG))
  module DCP_SCC = Graph.Components.Make(Domain.DCP)
  module VFG_SCC = Graph.Components.Make(Domain.VFG)

  module Increments = Caml.Set.Make(struct
    type nonrec t = Domain.DCP.E.t * IntLit.t
    [@@deriving compare]
  end)
  
  module Resets = Caml.Set.Make(struct
    type nonrec t = Domain.DCP.E.t * Domain.EdgeExp.t * IntLit.t
    [@@deriving compare]
  end)

  type cache = {
    updates: (Increments.t * Resets.t) Domain.EdgeExp.Map.t;
    variable_bounds: Domain.EdgeExp.t Domain.EdgeExp.Map.t;
    reset_chains: Domain.RG.Chain.Set.t Domain.EdgeExp.Map.t;
  }

  let empty_cache = { 
    updates = Domain.EdgeExp.Map.empty; 
    variable_bounds = Domain.EdgeExp.Map.empty;
    reset_chains = Domain.EdgeExp.Map.empty;
  }

  let checker {Callbacks.exe_env; summary; get_procs_in_file} : Summary.t =
    let open Domain in
    let proc_desc = Summary.get_proc_desc summary in

    let beginLoc = Procdesc.get_loc proc_desc in
    let proc_name = Procdesc.get_proc_name proc_desc in
    let tenv = Exe_env.get_tenv exe_env proc_name in
    let proc_name_str = Typ.Procname.to_simplified_string proc_name in
    log "\n\n---------------------------------";
    log "\n- ANALYZING %s" proc_name_str;
    log "\n---------------------------------\n";
    log " Begin location: %a\n" Location.pp beginLoc;
    let formals = Procdesc.get_pvar_formals proc_desc in
    let formals = List.fold formals ~init:PvarMap.empty ~f:(fun acc (pvar, typ) ->
      PvarMap.add pvar typ acc
    )
    in
    let locals = Procdesc.get_locals proc_desc in
    let locals = List.fold locals ~init:PvarMap.empty ~f:(fun acc (local : ProcAttributes.var_data) ->
      log "%a\n" Procdesc.pp_local local;
      let pvar = Pvar.mk local.name proc_name in
      PvarMap.add pvar local.typ acc
    )
    in

    let type_map = PvarMap.union (fun _ ->
      L.(die InternalError)"Type map pvar clash!"
    ) locals formals
    in
    let extras = (locals, formals, type_map) in
    let proc_data = ProcData.make summary tenv extras in
    (* let begin_loc = DCP.Node.Start beginLoc in *)
    let entry_point = DCP.Node.Start beginLoc in
    let initial_state = initial entry_point in
    match Analyzer.compute_post proc_data ~initial:initial_state with
    | Some post -> (
      log "\n---------------------------------";
      log "\n------- [ANALYSIS REPORT] -------";
      log "\n---------------------------------\n";
      log "%a" pp post;

      (* Draw dot graph, use nodes and edges stored in post state *)
      let lts = DCP.create () in
      DCP.NodeSet.iter (fun node ->
        log "%a\n" DCP.Node.pp node;
        DCP.add_vertex lts node;
      ) post.graph_nodes;
      DCP.EdgeSet.iter (fun edge ->
        DCP.add_edge_e lts edge;
      ) post.graph_edges;

      (* let out_folder = "./Graphs/" in
      (try Unix.mkdir out_folder with _ -> ()); *)

      let out_folder = "./Graphs/" ^ proc_name_str ^ "/" in
      (try Unix.mkdir out_folder with _ -> ());

      let file = Out_channel.create (out_folder ^ "LTS.dot") in
      active_graph_type := LTS;
      DCPDot.output_graph file lts;
      Out_channel.close file;

      log "[INITIAL NORMS]\n";
      EdgeExp.Set.iter (fun norm -> log "  %a\n" EdgeExp.pp norm) post.initial_norms;
      let dcp = DCP.create () in
      DCP.NodeSet.iter (fun node ->
        DCP.add_vertex dcp node;
      ) post.graph_nodes;

      (* Much easier to implement and more readable in imperative style.
       * Derive difference constraints for each edge for each norm and
       * add newly created norms unprocessed_norms set during the process *)
      let unprocessed_norms = ref post.initial_norms in
      let processed_norms = ref EdgeExp.Set.empty in
      while not (EdgeExp.Set.is_empty !unprocessed_norms) do (
        let norm = EdgeExp.Set.min_elt !unprocessed_norms in
        unprocessed_norms := EdgeExp.Set.remove norm !unprocessed_norms;
        processed_norms := EdgeExp.Set.add norm !processed_norms;
        DCP.EdgeSet.iter (fun (_, edge_data, _) ->
          let new_norms = DCP.EdgeData.derive_constraint edge_data norm formals in

          (* Remove already processed norms and add new norms to unprocessed set *)
          let new_norms = EdgeExp.Set.diff new_norms !processed_norms in
          unprocessed_norms := EdgeExp.Set.union new_norms !unprocessed_norms;
        ) post.graph_edges;
      ) done;

      log "[FINAL NORMS]\n";
      EdgeExp.Set.iter (fun norm -> log "  %a\n" EdgeExp.pp norm) !processed_norms;

      (* All DCs and norms are derived, now derive guards.
        * Use Z3 SMT solver to check which norms on which
        * transitions are guaranted to be greater than 0
        * based on conditions that hold on specified transition.
        * For example if transition is guarded by conditions
        * [x >= 0] and [y > x] then we can prove that
        * norm [x + y] > 0 thus it is a guard on this transition *)
      let cfg = [("model", "true"); ("proof", "true")] in
      let ctx = (Z3.mk_context cfg) in
      let solver = (Z3.Solver.mk_solver ctx None) in
      let zero_const = Z3.Arithmetic.Integer.mk_numeral_i ctx 0 in
      let possible_guards = EdgeExp.Set.fold (fun norm acc -> match norm with
        | EdgeExp.BinOp _ | EdgeExp.Var _ -> (
          let z3_norm = exp_to_z3_expr ctx norm in
          let guard_expr = Z3.Arithmetic.mk_gt ctx z3_norm zero_const in
          acc @ [guard_expr]
        )
        | EdgeExp.Const Const.Cint _ -> acc
        | _ -> (
          L.(die InternalError)"[Guards] Norm expression %a is not supported!" EdgeExp.pp norm
        )
      ) !processed_norms []
      in
      DCP.EdgeSet.iter (fun (src, edge_data, dst) ->
        DCP.EdgeData.derive_guards edge_data !processed_norms solver ctx;
        DCP.add_edge_e dcp (src, edge_data, dst);
      ) post.graph_edges;

      let guarded_nodes = DCP.fold_edges_e (fun (_, edge_data, dst) acc ->
        if EdgeExp.Set.is_empty edge_data.guards then acc 
        else (log "GUARDED NODE: %a\n" DCP.Node.pp dst; DCP.NodeSet.add dst acc)
      ) dcp DCP.NodeSet.empty
      in

      (* Propagate guard to all outgoing edges if all incoming edges
        * are guarded by this guard and the guard itself is not decreased
        * on any of those incoming edges (guard is a norm) *)
      let rec propagate_guards : DCP.NodeSet.t -> unit = fun nodes -> (
        if not (DCP.NodeSet.is_empty nodes) then (
          let rec get_shared_guards : EdgeExp.Set.t -> DCP.edge list -> EdgeExp.Set.t =
          fun guards edges -> match edges with
          | (_, edge_data, _) :: edges -> (
            if edge_data.backedge then (
              get_shared_guards guards edges
            ) else (
              (* Get edge guards that are not decreased on this edge *)
              let guards = DCP.EdgeData.active_guards edge_data in
              EdgeExp.Set.inter guards (get_shared_guards guards edges)
            )
          )
          | [] -> guards
          in

          let node = DCP.NodeSet.min_elt nodes in
          let nodes = DCP.NodeSet.remove node nodes in
          let incoming_edges = DCP.pred_e dcp node in
          let guards = get_shared_guards EdgeExp.Set.empty incoming_edges in
          let out_edges = DCP.succ_e dcp node in
          let guards, out_edges = match node with
          | DCP.Node.Prune (kind, _) when is_loop_prune kind -> (
            let true_branch, out_edges = List.partition_tf out_edges ~f:(fun (_, edge_data, _) -> 
              match edge_data.path_prefix_end with
              | Some (_, branch, _) when branch -> true
              | _ -> false
            )
            in
            let (src, true_branch, dst) = List.hd_exn true_branch in
            true_branch.guards <- EdgeExp.Set.union guards true_branch.guards;
            if not (DCP.Node.equal src dst) then propagate_guards (DCP.NodeSet.add dst nodes);
            let (_, backedge, _) = List.find_exn incoming_edges ~f:(fun (_, edge_data, _) -> edge_data.backedge) in
            let backedge_guards = DCP.EdgeData.active_guards backedge in
            let guards = EdgeExp.Set.inter guards backedge_guards in
            guards, out_edges
          )
          | _ -> guards, out_edges
          in
          let nodes = if EdgeExp.Set.is_empty guards then nodes else (
            (* Propagate guards to all outgoing edges and add
              * destination nodes of those edges to the processing queue *)
            List.fold out_edges ~init:nodes ~f:(fun acc (_, (edge_data : DCP.EdgeData.t), dst) ->
              edge_data.guards <- EdgeExp.Set.union guards edge_data.guards;
              if edge_data.backedge then acc else DCP.NodeSet.add dst acc
            )
          )
          in
          propagate_guards nodes
        )
      )
      in
      propagate_guards guarded_nodes;

      (* Output Guarded DCP over integers *)
      let file = Out_channel.create (out_folder ^ "DCP_guarded.dot") in
      active_graph_type := GuardedDCP;
      DCPDot.output_graph file dcp;
      Out_channel.close file;

      (* Convert DCP with guards to DCP without guards over natural numbers *)
      let to_natural_numbers : DCP.EdgeSet.t -> unit = fun edges -> (
        DCP.EdgeSet.iter (fun (_, edge_data, _) ->
          let constraints = DC.Map.fold (fun lhs (rhs, const) acc ->
            let dc_rhs = if IntLit.isnegative const then (
              (* lhs != rhs hack for now, abstraction algorithm presented in the thesis
               * doesn't add up in the example 'SingleLinkSimple' where they have [i]' <= [n]-1
               * which is indeed right if we want to get valid bound but their abstraction algorithm
               * leads to [i]' <= [n] because there's no guard for n on the transition *)
              let const = if EdgeExp.Set.mem rhs edge_data.guards || not (EdgeExp.equal lhs rhs) then IntLit.minus_one 
              else IntLit.zero in
              rhs, const
            ) else (
              rhs, const
            )
            in
            DC.Map.add lhs dc_rhs acc
          ) edge_data.constraints DC.Map.empty
          in
          edge_data.constraints <- constraints;
        ) edges
      )
      in
      to_natural_numbers post.graph_edges;

      let file = Out_channel.create (out_folder ^ "DCP.dot") in
      active_graph_type := DCP;
      DCPDot.output_graph file dcp;
      Out_channel.close file;

      (* Create variable flow graph which is necessary for
       * DCP preprocessing which renames variables and consequently
       * ensures that we get an acyclic reset DAG *)
      let vf_graph = VFG.create () in
      DCP.EdgeSet.iter (fun (src, edge_data, dst) -> 
        DC.Map.iter (fun lhs_norm (rhs_norm, _) ->
          if 
          (norm_is_variable lhs_norm formals) && 
          (norm_is_variable rhs_norm formals) then (
            let vfg_add_node node = if not (VFG.mem_vertex vf_graph node) then (
              VFG.add_vertex vf_graph node
            )
            in
            let dst_node = (lhs_norm, dst) in
            let src_node = (rhs_norm, src) in
            vfg_add_node dst_node; vfg_add_node src_node;
            VFG.add_edge_e vf_graph (VFG.E.create src_node (VFG.Edge.default) dst_node);
          );
        ) edge_data.constraints;
      ) post.graph_edges;

      let file = Out_channel.create (out_folder ^ "VFG.dot") in
      VFG_Dot.output_graph file vf_graph;
      Out_channel.close file;

      (* Create VFG mapping, create fresh variable 'v' for each SCC
       * and map each VFG node to this fresh variable. *)
      let vfg_components = VFG_SCC.scc_list vf_graph in
      let vfg_map = List.foldi vfg_components ~init:VFG.Map.empty ~f:(fun idx map component ->
        let pvar_name = Mangled.from_string ("var_" ^ string_of_int idx) in
        let aux_norm = EdgeExp.Var (Pvar.mk pvar_name proc_name) in
        List.fold component ~init:map ~f:(fun map ((exp, dcp_node as node) : VFG.Node.t) ->
          let aux_norm = match exp with
          | EdgeExp.Var pvar when Pvar.is_return pvar -> exp
          | _ -> aux_norm
          in
          processed_norms := EdgeExp.Set.add aux_norm !processed_norms;
          VFG.Map.add node aux_norm map
        )
      )
      in
      log "[VFG Mapping]\n";
      VFG.Map.iter (fun (norm, dcp_node) aux_norm -> 
        log "  (%a, %a) --> %a\n" DCP.Node.pp dcp_node EdgeExp.pp norm EdgeExp.pp aux_norm;
      ) vfg_map;

      (* Apply VFG mapping and rename DCP variables to ensure acyclic reset DAG *)
      DCP.EdgeSet.iter (fun (dcp_src, edge_data, dcp_dst) -> 
        let constraints = DC.Map.fold (fun lhs_norm (rhs_norm, const) map -> 
          let lhs_norm = match VFG.Map.find_opt (lhs_norm, dcp_dst) vfg_map with
          | Some norm -> norm
          | None -> lhs_norm
          in
          let rhs_norm = match VFG.Map.find_opt (rhs_norm, dcp_src) vfg_map with
          | Some norm -> norm
          | None -> rhs_norm
          in
          DC.Map.add lhs_norm (rhs_norm, const) map
        ) edge_data.constraints DC.Map.empty
        in
        edge_data.constraints <- constraints;
      ) post.graph_edges;

      let file = Out_channel.create (out_folder ^ "DCP_renamed.dot") in
      active_graph_type := DCP;
      DCPDot.output_graph file dcp;
      Out_channel.close file;

      let reset_graph = RG.create () in
      DCP.EdgeSet.iter (fun (src, edge_data, dst) -> 
        (* Search for resets *)
        DC.Map.iter (fun lhs_norm (rhs_norm, const) ->
          if not (EdgeExp.equal lhs_norm rhs_norm) then (
            let rg_add_node node = if not (RG.mem_vertex reset_graph node) then (
              RG.add_vertex reset_graph node;
            )
            in
            rg_add_node rhs_norm; rg_add_node lhs_norm;
            let edge = RG.E.create rhs_norm (RG.Edge.make (src, edge_data, dst) const) lhs_norm in
            RG.add_edge_e reset_graph edge;
          )
        ) edge_data.constraints;
      ) post.graph_edges;

      let file = Out_channel.create (out_folder ^ "RG.dot") in
      RG_Dot.output_graph file reset_graph;
      Out_channel.close file;

      (* Suboptimal way to find all SCC edges, the ocamlgraph library for some
       * reason does not have a function that returns edges of SCCs.  *)
      let get_scc_edges dcp =
        let components = DCP_SCC.scc_list dcp in
        List.fold components ~init:DCP.EdgeSet.empty ~f:(fun acc component ->
          (* Iterate over all combinations of SCC nodes and check if there
          * are edges between them in both directions *)
          List.fold component ~init:acc ~f:(fun acc node ->
            List.fold component ~init:acc ~f:(fun acc node2 ->
              let edges = DCP.EdgeSet.of_list (DCP.find_all_edges dcp node node2) in
              DCP.EdgeSet.union acc edges
            )
          )
        )
      in

      (* Edges that are not part of any SCC can be executed only once,
       * thus their local bound mapping is 1 and consequently their
       * transition bound TB(t) is 1 *)
      let scc_edges = get_scc_edges dcp in
      let non_scc_edges = DCP.EdgeSet.diff post.graph_edges scc_edges in
      DCP.EdgeSet.iter (fun (_, edge_data, _) ->
        edge_data.bound_norm <- Some EdgeExp.one;
      ) non_scc_edges;

      (* For each variable norm construct a E(v) set of edges where it is decreased
       * and assign each edge from this set local bound of v *)
      let norm_edge_sets, processed_edges = EdgeExp.Set.fold (fun norm (sets, processed_edges) ->
        let get_edge_set norm = DCP.EdgeSet.filter (fun (_, edge_data, _) ->
          match DC.Map.get_dc norm edge_data.constraints with
          | Some dc when DC.same_norms dc && DC.is_decreasing dc-> (
            edge_data.bound_norm <- Some norm;
            true
          )
          | _ -> false
        ) scc_edges
        in
        match norm with
        | EdgeExp.Var pvar -> (
          if PvarMap.mem pvar formals then sets, processed_edges
          else (
            let bounded_edges = get_edge_set norm in
            let sets = EdgeExp.Map.add norm bounded_edges sets in
            sets, DCP.EdgeSet.union processed_edges bounded_edges
          )
        )
        | EdgeExp.BinOp _ -> (
          (* [TODO] Validate that norm is not purely built over symbolic constants *)
          let bounded_edges = get_edge_set norm in
          let sets = EdgeExp.Map.add norm bounded_edges sets in
          sets, DCP.EdgeSet.union processed_edges bounded_edges
        )
        | EdgeExp.Const _ -> sets, processed_edges
        | _ -> L.(die InternalError)"[Norm edge sets] Invalid norm expression!"
      ) !processed_norms (EdgeExp.Map.empty, DCP.EdgeSet.empty)
      in
      EdgeExp.Map.iter (fun norm edge_set ->
        log "E(%a):\n" EdgeExp.pp norm;
        DCP.EdgeSet.iter (fun (src, edge_data, dst) ->
          let local_bound = match edge_data.bound_norm with
          | Some bound -> bound
          | None -> L.(die InternalError)""
          in
          log "  %a -- %a -- %a\n" DCP.Node.pp src EdgeExp.pp local_bound DCP.Node.pp dst;
        ) edge_set
      ) norm_edge_sets;

      (* Find local bounds for remaining edges that were not processed by
       * the first or second step. Use previously constructed E(v) sets
       * and for each set try to remove edges from the DCP graph. If some
       * unprocessed edges cease to be part of any SCC after the removal,
       * assign variable v as local bound of those edges *)
      let remaining_edges = EdgeExp.Map.fold (fun norm edges remaining_edges ->
        if DCP.EdgeSet.is_empty remaining_edges then (
          remaining_edges
        ) else (
          if not (DCP.EdgeSet.is_empty edges) then (
            (* Remove edges of E(v) set from DCP *)
            DCP.EdgeSet.iter (fun edge -> DCP.remove_edge_e dcp edge) edges;

            (* Calculate SCCs for modified graph *)
            let scc_edges = get_scc_edges dcp in
            let non_scc_edges = DCP.EdgeSet.diff remaining_edges scc_edges in
            DCP.EdgeSet.iter (fun (_, edge_data, _) -> 
              edge_data.bound_norm <- Some norm
            ) non_scc_edges;

            (* Restore DCP *)
            DCP.EdgeSet.iter (fun edge -> DCP.add_edge_e dcp edge) edges;
            DCP.EdgeSet.diff remaining_edges non_scc_edges
          ) else (
            remaining_edges
          )
        )
      ) norm_edge_sets (DCP.EdgeSet.diff scc_edges processed_edges)
      in

      let get_update_map norm edges cache =
        if EdgeExp.Map.mem norm cache.updates then (
          cache
        ) else (
          (* Create missing increments and resets sets for this variable norm *)
          let updates = DCP.EdgeSet.fold (fun edge (increments, resets) ->
            let _, edge_data, _ = edge in
            match DC.Map.get_dc norm edge_data.constraints with
            | Some dc -> (
              (* Variable norm is used on this edge *)
              let _, rhs_norm, const = dc in
              if not (DC.same_norms dc) then (
                (* Must be a reset *)
                let resets = Resets.add (edge, rhs_norm, const) resets in
                increments, resets
              ) else if DC.is_increasing dc then (
                (* Must be a increment *)
                let increments = Increments.add (edge, const) increments in
                (increments, resets)
              ) else (increments, resets)
            )
            | None -> (increments, resets)
          ) edges (Increments.empty, Resets.empty)
          in
          { cache with updates = EdgeExp.Map.add norm updates cache.updates }
        )
      in

      let rec calculate_increment_sum norms cache = EdgeExp.Set.fold (fun norm (total_sum, cache) -> 
        (* Calculates increment sum based on increments of variable norm:
         * SUM(TB(t) * const) for all edges where norm is incremented, 0 if nowhere *)
        let cache = get_update_map norm post.graph_edges cache in
        let increments, _ = EdgeExp.Map.find norm cache.updates in
        let sum, cache = Increments.fold (fun (dcp_edge, const) (sum, cache) ->
          let edge_bound, cache = transition_bound dcp_edge cache in
          let increment_exp = if EdgeExp.is_zero edge_bound then (
            None
          ) else (
            if IntLit.isone const then (
              Some edge_bound
            ) else (
              let const_exp = EdgeExp.Const (Const.Cint const) in
              if EdgeExp.is_one edge_bound then Some const_exp
              else Some (EdgeExp.BinOp (Binop.Mult None, edge_bound, const_exp))
            )
          )
          in
          let sum = match sum with
          | Some sum -> (
            match increment_exp with
            | Some exp -> Some (EdgeExp.BinOp (Binop.PlusA None, sum, exp))
            | None -> Some sum
          )
          | None -> increment_exp
          in
          sum, cache
        ) increments (None, cache)
        in
        let total_sum = match total_sum, sum with
        | Some total_sum, Some sum -> Some (EdgeExp.BinOp (Binop.PlusA None, total_sum, sum))
        | Some sum, None | None, Some sum -> Some sum
        | None, None -> None
        in
        total_sum, cache
      ) norms (None, cache)

      and calculate_reset_sum chains cache = RG.Chain.Set.fold (fun chain (sum, cache) ->
        (* Calculates reset sum based on possible reset chains of reseted norm:
          * SUM( TB(trans(chain)) * max( VB(in(chain)) + value(chain), 0)) for all reset chains,
          * where: trans(chain) = all transitions of a reset chain
          * in(chain) = norm of initial transition of a chain
          * value(chain) = sum of constants on edges along a chain *)
        let norm = RG.Chain.origin chain in
        let chain_value = RG.Chain.value chain in
        let var_bound, cache = variable_bound norm cache in
        let max_exp, cache = if IntLit.isnegative chain_value then (
          (* result can be negative, wrap bound expression in the max function *)
          let const_bound = EdgeExp.Const (Const.Cint (IntLit.neg chain_value)) in
          let binop_bound = match var_bound with
          | EdgeExp.Max args -> (
            (* max(max(x, 0) - 1, 0) == max(x - 1, 0) *)
            EdgeExp.BinOp (Binop.MinusA None, (List.hd_exn args), const_bound)
          )
          | _ -> EdgeExp.BinOp (Binop.MinusA None, var_bound, const_bound)
          in
          EdgeExp.Max [binop_bound], cache
        ) else if IntLit.iszero chain_value then (
          var_bound, cache
        ) else (
          (* const > 0 => result must be positive, max function is useless *)
          let const_bound = EdgeExp.Const (Const.Cint chain_value) in
          let binop_bound = EdgeExp.BinOp (Binop.PlusA None, var_bound, const_bound) in
          binop_bound, cache
        )
        in
        (* Creates a list of arguments for min(args) function. Arguments are
         * transition bounds of each transition of a reset chain. Zero TB stops
         * the fold as we cannot get smaller value. *)
        let fold_aux (args, cache) (dcp_edge : DCP.E.t) =
          let open Base.Continue_or_stop in
          let edge_bound, cache = transition_bound dcp_edge cache in
          if EdgeExp.is_zero edge_bound then Stop ([EdgeExp.zero], cache) 
          else (
            match List.hd args with
            | Some arg when EdgeExp.is_one arg -> Continue (args, cache)
            | _ -> (
              if EdgeExp.is_one edge_bound then Continue ([edge_bound], cache) 
              else Continue (args @ [edge_bound], cache)
            )
          )
        in
        let reset_exp, cache = if EdgeExp.is_zero max_exp then (
            None, cache
          ) else (
            let chain_transitions = DCP.EdgeSet.elements (RG.Chain.transitions chain) in
            let args, cache = List.fold_until chain_transitions ~init:([], cache) ~f:fold_aux ~finish:(fun acc -> acc) in
            let args = List.dedup_and_sort ~compare:EdgeExp.compare args in
            let edge_bound = if Int.equal (List.length args) 1 then List.hd_exn args else EdgeExp.Min (args) in
            if EdgeExp.is_one edge_bound then Some max_exp, cache
            else Some (EdgeExp.BinOp (Binop.Mult None, edge_bound, max_exp)), cache
          )
        in
        let calculate_sum e1 e2 = match e1, e2 with
        | Some e1, Some e2 -> Some (EdgeExp.BinOp (Binop.PlusA None, e1, e2))
        | Some e, None | None, Some e -> Some e
        | None, None -> None
        in
        let sum = calculate_sum sum reset_exp in
        let _, chain_norms = RG.Chain.norms chain reset_graph in
        let increment_sum, cache = calculate_increment_sum chain_norms cache in
        (calculate_sum sum increment_sum), cache
      ) chains (None, cache)

      and variable_bound norm cache =
        let bound, cache = match EdgeExp.Map.find_opt norm cache.variable_bounds with
        | Some bound -> bound, cache
        | None -> (
          let norm_bound = norm in
          let var_bound, cache = match norm with
          | EdgeExp.Var pvar -> (
            if PvarMap.mem pvar formals then (
              match PvarMap.find_opt pvar type_map with
              | Some typ -> (match typ.desc with
                | Typ.Tint ikind -> if Typ.ikind_is_unsigned ikind then (
                    (* for unsigned x: max(x, 0) => x *)
                    norm_bound, cache
                  ) else (
                    (* for signed x: max(x, 0) *)
                    EdgeExp.Max [norm_bound], cache
                  )
                | _ -> L.(die InternalError)"[VB] Unexpected Lvar type!"
              )
              | None -> L.(die InternalError)"[VB] Lvar [%a] is not a local variable!" Pvar.pp_value pvar
            ) else (
              let cache = get_update_map norm post.graph_edges cache in
              let _, resets = EdgeExp.Map.find norm cache.updates in
              let increment_sum, cache = calculate_increment_sum (EdgeExp.Set.singleton norm) cache in
              let max_args, cache = Resets.fold (fun (_, norm, const) (args, cache) -> 
                let var_bound, cache = variable_bound norm cache in
                let max_arg = if IntLit.isnegative const then (
                  let const = EdgeExp.Const (Const.Cint (IntLit.neg const)) in
                  [EdgeExp.BinOp (Binop.MinusA None, var_bound, const)]
                ) else if IntLit.iszero const then (
                  [var_bound]
                ) else (
                  let const = EdgeExp.Const (Const.Cint const) in
                  [EdgeExp.BinOp (Binop.PlusA None, var_bound, const)]
                )
                in
                args @ max_arg, cache
              ) resets ([], cache)
              in
              let max_args = List.dedup_and_sort ~compare:EdgeExp.compare max_args in
              let max = if Int.equal (List.length max_args) 1 
              then List.hd_exn max_args
              else EdgeExp.Max max_args
              in
              let var_bound = match increment_sum with
              | Some increments -> if EdgeExp.is_zero max then (
                increments
              ) else EdgeExp.BinOp (Binop.PlusA None, increments, max)
              | None -> max
              in
              var_bound, cache
            )
          )
          | EdgeExp.Const Const.Cint const_norm -> (
            if IntLit.isnegative const_norm then EdgeExp.Max [norm_bound], cache
            else norm_bound, cache
          )
          | _ -> L.(die InternalError)"[VB] Unsupported norm expression [%a]!" EdgeExp.pp norm
          in
          let vb_cache = EdgeExp.Map.add norm var_bound cache.variable_bounds in
          let cache = { cache with variable_bounds = vb_cache } in
          var_bound, cache
        )
        in
        log "   [VB(%a)] %a\n" EdgeExp.pp norm EdgeExp.pp bound;
        bound, cache

      and transition_bound (src, (edge_data : DCP.EdgeData.t), dst) cache =
        (* For variable norms: TB(t) = IncrementSum + ResetSum 
         * For constant norms: TB(t) = constant *)
        log "[TB] %a -- %a\n" DCP.Node.pp src DCP.Node.pp dst;
        let function_calls = edge_data.calls in
        CallSiteSet.iter (fun (call_exp, loc) -> match call_exp with
          | EdgeExp.Call (_, proc_name, _, call_summary) -> (
            log "   [Call] %a : %a | %a\n" Typ.Procname.pp proc_name Domain.pp_summary call_summary Location.pp loc;
          )
          | _ -> assert(false)
        ) function_calls;
        match edge_data.bound_cache with
        | Some bound_cache -> bound_cache, cache 
        | None -> (
          if edge_data.computing then (
            raise Exit
          ) else (
            (* Infinite recursion guard *)
            edge_data.computing <- true;

            match edge_data.bound_norm with
            | Some norm -> (
              log "   [Local bound] %a\n" EdgeExp.pp norm;
              let bound, cache = match norm with
              | EdgeExp.Var pvar when not (PvarMap.mem pvar formals) -> (

                (* Get reset chains for local bound *)
                let reset_chains, cache = match EdgeExp.Map.find_opt norm cache.reset_chains with
                | Some chains -> chains, cache
                | None -> (
                  let chains = RG.get_reset_chains norm reset_graph dcp in
                  let cache = { cache with reset_chains = EdgeExp.Map.add norm chains cache.reset_chains } in
                  chains, cache
                )
                in
                RG.Chain.Set.iter (fun chain ->
                  log "   [Reset Chain] %a\n" RG.Chain.pp chain;
                ) reset_chains;

                let norms = RG.Chain.Set.fold (fun chain acc ->
                  let norms, _ = RG.Chain.norms chain reset_graph in
                  EdgeExp.Set.union acc norms
                ) reset_chains EdgeExp.Set.empty
                in
                let increment_sum, cache = calculate_increment_sum norms cache in
                let reset_sum, cache = calculate_reset_sum reset_chains cache in

                let edge_bound = match increment_sum, reset_sum with
                | Some increments, Some resets -> EdgeExp.BinOp (Binop.PlusA None, increments, resets)
                | Some bound, None | None, Some bound -> bound
                | None, None -> EdgeExp.zero
                in
                edge_bound, cache
              )
              | EdgeExp.Const (Const.Cint _) -> (
                (* Non-loop edge, can be executed only once, const is always 1 *)
                norm, cache
              )
              | _ -> L.(die InternalError)"[Bound] Unsupported norm expression [%a]!" EdgeExp.pp norm
              in
              log "[Edge bound (%a)] %a\n" EdgeExp.pp norm EdgeExp.pp bound;
              edge_data.bound_cache <- Some bound;
              bound, cache
            )
            | None -> L.(die InternalError)"[Bound] edge has no bound norm!"
          )
        )
      in

      let bound, cache = if not (DCP.EdgeSet.is_empty remaining_edges) then (
        L.internal_error "[Looper] Local bounds could not be determined for all edges. \
        Returning [Infinity]\n";
        EdgeExp.Inf, empty_cache
      ) else (
        log "[Local bounds]\n";
        DCP.EdgeSet.iter (fun (src, edge_data, dst) ->
          let local_bound = match edge_data.bound_norm with
          | Some bound -> bound
          | None -> L.(die InternalError)""
          in
          log "  %a -- %a -- %a\n" DCP.Node.pp src EdgeExp.pp local_bound DCP.Node.pp dst
        ) post.graph_edges;

        (* Calculate bound for all backedeges and sum them to get the total bound *)
        let final_bound, cache =  try
          DCP.EdgeSet.fold (fun edge (final_bound, cache) ->
            let _, edge_data, _ = edge in
            if edge_data.backedge then (
              let edge_bound, cache = transition_bound edge cache in
              if EdgeExp.is_zero edge_bound then final_bound, cache else (
                let final_bound = match final_bound with
                | Some sum -> EdgeExp.BinOp (Binop.PlusA None, sum, edge_bound)
                | None -> edge_bound
                in
                Some final_bound, cache
              )
            ) else (
              final_bound, cache
            )
          ) post.graph_edges (None, empty_cache)
        with Exit -> (Some EdgeExp.Inf, empty_cache)
        in
        match final_bound with
        | Some bound -> bound, cache
        | None -> EdgeExp.zero, cache
      )
      in
      log "\n[Final bound] %a\n" EdgeExp.pp bound;
      
      let ret_type = Procdesc.get_ret_type proc_desc in
      let return_bound = match ret_type.desc with
      | Tint _ -> (
        log "[Return type] %a\n" Typ.(pp Pp.text) ret_type;
        let edge_list = DCP.EdgeSet.elements post.graph_edges in
        let _, return_edge, _ = List.find_exn edge_list ~f:(fun (_, edge, _) -> DCP.EdgeData.is_exit_edge edge) in
        let ret_pvar = Procdesc.get_ret_var proc_desc in
        let norm, _ = DC.Map.find (EdgeExp.Var ret_pvar) return_edge.constraints in
        let return_bound, _ = variable_bound norm cache in
        log "[Return bound] %a\n" EdgeExp.pp return_bound;
        Some return_bound
      )
      | _ -> None
      in

      log "Description:\n  signed x: max(x, 0) == [x]\n";
      let payload : EdgeExp.summary = {
        formal_map = FormalMap.make proc_desc;
        globals = PvarMap.empty;
        bound = bound;
        return_bound = return_bound;
      }
      in
      Payload.update_summary payload summary
    )
    | None ->
      L.(die InternalError)
      "[Looper] Failed to compute post for %a" Typ.Procname.pp
      (Procdesc.get_proc_name proc_desc)