open! IStd

module F = Format
module L = Logging
module Domain = LoopusDomain


module Payload = SummaryPayload.Make (struct
  type t = Domain.astate

  let update_payloads astate (payloads : Payloads.t) = {payloads with loopus= Some astate}

  let of_payloads (payloads : Payloads.t) = payloads.loopus
end)

let log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> L.stdout_cond true fmt
 
module TransferFunctions (ProcCFG : ProcCfg.S) = struct
  module CFG = ProcCFG
  module Domain = Domain

  type nonrec extras = (Domain.PvarSet.t * Domain.PvarSet.t)

  let pp_session_name node fmt = F.fprintf fmt "loopus %a" CFG.Node.pp_id (CFG.Node.id node)

  (* Take an abstract state and instruction, produce a new abstract state *)
  let exec_instr : Domain.astate -> 'a ProcData.t -> CFG.Node.t -> Sil.instr -> Domain.astate =
    fun astate {pdesc; tenv; extras} node instr ->

    let open Domain in

    let locals, formals = fst extras, snd extras in

    let is_exit_node = match ProcCFG.Node.kind node with 
      | Procdesc.Node.Exit_node -> true 
      | _ -> false 
    in

    let is_start_node = match ProcCFG.Node.kind node with
      | Procdesc.Node.Start_node -> true
      | _ -> false
    in

    let is_pvar_decl_node = match ProcCFG.Node.kind node with
    | Procdesc.Node.Stmt_node DeclStmt -> true
    | _ -> false
    in

    let rec substitute_pvars exp = match exp with
    | Exp.BinOp (op, lexp, rexp) -> (
      let lexp = substitute_pvars lexp in
      let rexp = substitute_pvars rexp in
      Exp.BinOp (op, lexp, rexp)
    )
    | Exp.UnOp (op, sub_exp, typ) -> (
      let sub_exp = substitute_pvars sub_exp in
      Exp.UnOp (op, sub_exp, typ)
    )
    | Exp.Var ident -> (
      let referenced_pvar = Ident.Map.find ident astate.ident_map in
      Exp.Lvar referenced_pvar
    )
    | _ -> exp
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
    | Exp.Lvar pvar when PvarSet.mem pvar formals -> PvarSet.add pvar acc
    | _ -> acc
    in


    let astate = match instr with
    | Prune (cond, loc, branch, kind) -> 
      ( 
        log "[PRUNE] (%a) | %a\n" Location.pp loc Exp.pp cond;

        let lts_loc = LTSLocation.PruneLoc (kind, loc) in
        let newLocSet = LocSet.add loc astate.branchLocs in
        let newEdge = Edge.set_end astate.current_edge lts_loc in

        let edge_data = GraphEdge.add_invariants astate.edge_data (get_unmodified_pvars astate) in
        (* let missing_formulas = generate_missing_assignments astate in *)
        (* let formulas = Assignment.Set.union astate.edge_assignments missing_formulas in *)

        let prune_node = GraphNode.make lts_loc in
        let lhs = astate.aggregate_join.lhs in
        let rhs = astate.aggregate_join.rhs in
        let graph_nodes = LTS.NodeSet.add prune_node astate.graph_nodes in

        let is_direct_backedge = LTSLocation.equal lts_loc lhs || LTSLocation.equal lts_loc rhs in
        let graph_edges, graph_nodes = if is_direct_backedge then (
          (* Discard join node and all edges poiting to it and instead make
           * one direct backedge with variables modified inside the loop *)
          let join_edges =  astate.aggregate_join.edges in
          let edge = List.find_exn (LTS.EdgeSet.elements join_edges) ~f:(fun edge -> 
            let backedge_origin = LTS.E.src edge in
            GraphNode.equal backedge_origin prune_node
          ) in
          let backedge = LTS.E.create (LTS.E.src edge) (LTS.E.label edge) prune_node in
          let graph_edges = LTS.EdgeSet.add backedge astate.graph_edges in
          let graph_nodes = LTS.NodeSet.remove astate.last_node graph_nodes in
          graph_edges, graph_nodes
        ) else (
          (* Add all accumulated edges pointing to aggregated join node and
           * new edge pointing from aggregated join node to this prune node *)
          let edge_count = AggregateJoin.edge_count astate.aggregate_join in
          let is_empty_edge = GraphEdge.equal astate.edge_data GraphEdge.empty in
          if not (is_loop_prune kind) && Int.equal edge_count 2 && is_empty_edge then (
            (* LTS simplification, skip simple JOIN node and redirect edges pointing to it *)
            let graph_edges = LTS.EdgeSet.map (fun (src, data, dst) -> 
              (src, data, prune_node)
            ) astate.aggregate_join.edges
            in
            let graph_nodes = LTS.NodeSet.remove astate.last_node graph_nodes in
            (LTS.EdgeSet.union astate.graph_edges graph_edges), graph_nodes
          ) else if Int.equal edge_count 1 then (
            (* JOIN node with single incoming edge (useless node).
             * Redirect incoming edge to prune node and delete join node *)
            let graph_edges = LTS.EdgeSet.map (fun (src, data, dst) -> 
              (src, data, prune_node)
            ) astate.aggregate_join.edges
            in
            let graph_nodes = LTS.NodeSet.remove astate.last_node graph_nodes in
            (LTS.EdgeSet.union astate.graph_edges graph_edges), graph_nodes
          ) else (
            let path_end = List.last astate.branchingPath in
            let edge_data = GraphEdge.set_path_end edge_data path_end in
            let new_lts_edge = LTS.E.create astate.last_node edge_data prune_node in
            let graph_edges = LTS.EdgeSet.add new_lts_edge astate.graph_edges in
            let graph_edges = LTS.EdgeSet.union astate.aggregate_join.edges graph_edges in
            graph_edges, graph_nodes
          );
        )
        in

        let zero_exp = Exp.Const (Const.Cint IntLit.zero) in
        let pvar_condition = substitute_pvars cond in
        let prune_condition = match pvar_condition with
        | Exp.BinOp _ -> pvar_condition
        | Exp.UnOp (LNot, exp, _) -> (
          (* Currently handles only "!exp" *)
          match exp with
          | Exp.BinOp (op, lexp, rexp) -> (
            (* Handles "!(lexp BINOP rexp)" *)
            let negate_binop = match op with
            | Binop.Lt -> Binop.Ge
            | Binop.Gt -> Binop.Le
            | Binop.Le -> Binop.Gt
            | Binop.Ge -> Binop.Lt
            | Binop.Eq -> Binop.Ne
            | Binop.Ne -> Binop.Eq
            | _ -> L.(die InternalError)"Unsupported prune condition type!"
            in
            Exp.BinOp (negate_binop, lexp, rexp)
          )
          | Exp.Const const -> Exp.BinOp (Binop.Eq, Exp.Const const, zero_exp)
          | _ -> L.(die InternalError)"Unsupported prune condition type!"
        )
        | Exp.Const const -> Exp.BinOp (Binop.Ne, Exp.Const const, zero_exp)
        | _ -> L.(die InternalError)"Unsupported prune condition type!"
        in

        (* We're tracking formals which are used in
         * loop header conditions inside the loop body *)
        let tracked_formals = if is_loop_prune kind then (
          let cond_formals = extract_formals pvar_condition PvarSet.empty in
          if branch then (
            PvarSet.union astate.tracked_formals cond_formals
          ) else (
            (* Remove formals from false branch of loop *)
            PvarSet.diff astate.tracked_formals cond_formals
          )
        ) else astate.tracked_formals
        in

        (* Derive norm from prune condition.
         * [x > y] -> [x - y] > 0
         * [x >= y] -> [x - y + 1] > 0 *)
        let norms = if branch && is_loop_prune kind then (
          match prune_condition with
          | Exp.BinOp (op, lexp, rexp) -> (
            match op with
            | Binop.Lt -> Exp.Set.add (Exp.BinOp (Binop.MinusA, rexp, lexp)) astate.initial_norms
            | Binop.Le -> (
              let subexp = Exp.BinOp (Binop.MinusA, rexp, lexp) in
              let norm = Exp.BinOp (Binop.PlusA, subexp, Exp.Const (Const.Cint IntLit.one)) in
              Exp.Set.add norm astate.initial_norms
            )
            | Binop.Gt -> Exp.Set.add (Exp.BinOp (Binop.MinusA, lexp, rexp)) astate.initial_norms
            | Binop.Ge -> (
              let subexp = Exp.BinOp (Binop.MinusA, lexp, rexp) in
              let norm = Exp.BinOp (Binop.PlusA, subexp, Exp.Const (Const.Cint IntLit.one)) in
              Exp.Set.add norm astate.initial_norms
            )
            | _ -> astate.initial_norms
          )
          | _ -> astate.initial_norms
        ) else (
          astate.initial_norms
        )
        in

        let edge_data = GraphEdge.add_condition GraphEdge.empty prune_condition in
        (* let formulas = Formula.Set.add (prune_formula) Formula.Set.empty in *)
        { astate with
          branchingPath = astate.branchingPath @ [(kind, branch, loc)];
          branchLocs = newLocSet; 
          edges = Edge.Set.add newEdge astate.edges;
          current_edge = Edge.initial lts_loc;
          lastLoc = lts_loc;

          initial_norms = norms;
          tracked_formals = tracked_formals;
          modified_pvars = PvarSet.empty;
          edge_data = edge_data;
          last_node = prune_node;
          graph_nodes = graph_nodes;
          graph_edges = graph_edges;
          aggregate_join = AggregateJoin.initial;
        }
      )  
      
    | Nullify (_, loc) -> 
      (
        log "[NULLIFY] %a\n" Location.pp loc;
        astate
      )

    | Abstract loc -> 
      (
        log "[ABSTRACT] %a\n" Location.pp loc;
        astate
      )

    | Remove_temps (ident_list, loc) -> 
      (
        log "[REMOVE_TEMPS] %a\n" Location.pp loc;

        if is_pvar_decl_node then log "  Decl node\n";
        if is_start_node then (
          let instrs = CFG.instrs node in
          log "  Start node\n";
          let count = Instrs.count instrs in
          log "  Instr count: %d\n" count;
          (* log "  %a\n" (Instrs.pp Pp.text) instrs; *)
        );

        if is_exit_node then (
          log "  Exit node\n";
          (* let missing_formulas = generate_missing_formulas astate in
          let formulas = Formula.Set.union astate.edge_formulas missing_formulas in *)

          let exit_node = GraphNode.make LTSLocation.Exit in
          let path_end = List.last astate.branchingPath in
          let edge_data = GraphEdge.set_path_end astate.edge_data path_end in
          let new_lts_edge = LTS.E.create astate.last_node edge_data exit_node in
          let graph_edges = LTS.EdgeSet.add new_lts_edge astate.graph_edges in
          { astate with
            graph_nodes = LTS.NodeSet.add exit_node astate.graph_nodes;
            graph_edges = LTS.EdgeSet.union astate.aggregate_join.edges graph_edges;
          }
        ) else (
          astate
        )  
      )

    | Store (Exp.Lvar assigned, _expType, rexp, loc) ->
      (
        log "[STORE] (%a) | %a = %a | %B\n" 
        Location.pp loc Pvar.pp_value assigned Exp.pp rexp is_pvar_decl_node;


        (* Substitute rexp based on previous assignments, 
         * eg. [beg = i; end = beg;] becomes [beg = i; end = i] *)
        let pvar_rexp = substitute_pvars rexp in
        let pvar_rexp = match pvar_rexp with
        | Exp.BinOp (Binop.PlusA, Exp.Lvar lexp, Exp.Const (Const.Cint c1)) -> (
          (* [BINOP] PVAR + CONST *)
          match (GraphEdge.get_assignment_rhs astate.edge_data lexp) with
          | Exp.BinOp (Binop.PlusA, lexp, Exp.Const (Const.Cint c2)) -> (
            (* [BINOP] (PVAR + C1) + C2 -> PVAR + (C1 + C2) *)
            let const = Exp.Const (Const.Cint (IntLit.add c1 c2)) in
            Exp.BinOp (Binop.PlusA, lexp, const)
          )
          | _ -> pvar_rexp
        )
        | Exp.Lvar rhs_pvar -> (
          GraphEdge.get_assignment_rhs astate.edge_data rhs_pvar
        )
        | _ -> pvar_rexp
        in

        (* Check if set already contains assignment with specified
         * lhs and replace it with updated formulas if so. Needed
         * when one edge contains multiple assignments to single variable *)
        let edge_data = GraphEdge.add_assignment astate.edge_data assigned pvar_rexp in
        let astate = {astate with edge_data = edge_data} in
        let locals = if is_pvar_decl_node then (
          PvarSet.add assigned astate.locals
        ) else (
          astate.locals
        )
        in
        let pvars = Sequence.shift_right (Exp.program_vars rexp) assigned in
        let edge = Edge.add_modified astate.current_edge pvars in
        { astate with 
          current_edge = edge;
          locals = locals;
          edge_data = edge_data;
          modified_pvars = PvarSet.add assigned astate.modified_pvars;
        }
      )

    | Load (ident, lexp, _typ, loc) ->
      (
        log "[LOAD] (%a) | %a = %a\n" Location.pp loc Ident.pp ident Exp.pp lexp;
        let ident_map = match lexp with
        | Exp.Lvar pvar -> Ident.Map.add ident pvar astate.ident_map
        | Exp.Var id -> (
          let pvar = Ident.Map.find id astate.ident_map in
          Ident.Map.add ident pvar astate.ident_map
        )
        | _ -> L.(die InternalError)"Unsupported LOAD lhs-expression type!"
        in
        (* let pvars = Exp.program_vars lexp in
        let edge = Domain.Edge.add_modified astate.current_edge pvars in
        log "  Modified: [%a]\n" Domain.PvarSet.pp edge.modified_vars;
        {astate with current_edge = edge} *)
        { astate with ident_map = ident_map }
      )
    | Call (_retValue, Const Cfun callee_pname, _actuals, loc, _) ->
      ( 
        let _fun_name = Typ.Procname.to_simplified_string callee_pname in
        log "[CALL] (%a)\n" Location.pp loc;
        astate
      )

    (* Rest of SIL instruction possibilites *)
    | _ -> 
      (
        log "[UNKNOWN INSTRUCTION]\n";
        astate
      )
    in
    astate
 end



let basic_tests ( ctx : Z3.context ) =
  let open Z3 in
  let open Z3.Symbol in
  let open Z3.Boolean in
  let open Z3.Arithmetic in
  log "BasicTests\n" ;
  (* let fname = mk_string ctx "f" in *)
  let int_sort = Integer.mk_sort ctx in
  let len = Expr.mk_const_s ctx "len" int_sort in
  let idx = Expr.mk_const_s ctx "idx" int_sort in
  let bs = Boolean.mk_sort ctx in
  let domain = [ bs; bs ] in
  (* let f = (FuncDecl.mk_func_decl ctx fname domain bs) in *)
  (* let fapp = (mk_app ctx f 
		[ (Expr.mk_const ctx x bs); (Expr.mk_const ctx y bs) ]) in *)
  (* let rhs = mk_gt ctx (mk_sub ctx len idx) (Integer.mk_numeral_i ctx 0) in *)
  let zero_const = Integer.mk_numeral_i ctx 0 in
  let lhs = Arithmetic.mk_gt ctx len idx in
  let rhs = Arithmetic.mk_gt ctx (Arithmetic.mk_sub ctx [len; idx]) zero_const in
  let formula = mk_not ctx (mk_implies ctx lhs rhs) in
  (* let g = (Goal.mk_goal ctx true false false) in
  (Goal.add g [ formula ]) ;
  log "%s\n" ("Goal: " ^ (Goal.to_string g)) ; *)
  let solver = (Solver.mk_solver ctx None) in
  (* let formulas = Goal.get_formulas g in *)
  Solver.add solver [formula];
  (* (List.iter (fun a -> (Solver.add solver [ a ])) (get_formulas g)) ; *)
  let solve_status = Solver.check solver [] in
  if phys_equal solve_status Solver.SATISFIABLE then
    log "Satisfiable\n"
  else (
    let proof = Solver.get_proof solver in
    log "Not satisfiable\n";
    (* match proof with
    | Some expr -> log "PROOF: %s\n" (Expr.to_string expr)
    | _ -> (); *)
  )


module CFG = ProcCfg.NormalOneInstrPerNode
(* module CFG = ProcCfg.Normal *)

module Analyzer = AbstractInterpreter.Make (CFG) (TransferFunctions)
  let checker {Callbacks.tenv; proc_desc; summary} : Summary.t =
    let open Domain in

    let beginLoc = Procdesc.get_loc proc_desc in
    let proc_name = Procdesc.get_proc_name proc_desc in 
    log "\n\n---------------------------------";
    log "\n- ANALYZING %s" (Typ.Procname.to_simplified_string proc_name);
    log "\n---------------------------------\n";
    log " Begin location: %a\n" Location.pp beginLoc;
    (* Procdesc.pp_local locals; *)

    (* let reportBugs : Domain.astate -> unit = fun post ->
      LocationMap.iter (fun loopLoc bugSet ->
      let msg = F.asprintf "Redundant traversal of %a detected in loop" Domain.pp_footprint bugSet in
      (* let msg = F.asprintf "Redundant traversal bug detected\n" in *)
      let localised_msg = Localise.verbatim_desc msg in
      let issue = IssueType.redundant_traversal in
      let exn = Exceptions.Checkers (issue, localised_msg) in
      Reporting.log_warning summary ~loc:loopLoc IssueType.redundant_traversal msg
      ) post.bugLocs; 
    in *)

    let proc_name = Procdesc.get_proc_name proc_desc in
    let formals_mangled = Procdesc.get_formals proc_desc in
    let formals = List.fold formals_mangled ~init:PvarSet.empty ~f:(fun acc (name, _) ->
      let formal_pvar = Pvar.mk name proc_name in
      PvarSet.add formal_pvar acc
    )
    in
    let locals = Procdesc.get_locals proc_desc in
    let locals = List.fold locals ~init:PvarSet.empty ~f:(fun acc (local : ProcAttributes.var_data) ->
      log "%a\n" Procdesc.pp_local local;
      let pvar = Pvar.mk local.name proc_name in
      PvarSet.add pvar acc
    )
    in
    let extras = (locals, formals) in
    let proc_data = ProcData.make proc_desc tenv extras in
    let begin_loc = LTSLocation.Start beginLoc in
    let entry_point = GraphNode.make begin_loc in
    let initial_state = initial entry_point in
    match Analyzer.compute_post proc_data ~initial:initial_state with
    | Some post -> (
      log "\n---------------------------------";
      log "\n------- [ANALYSIS REPORT] -------";
      log "\n---------------------------------\n";
      log "%a" pp post;

      (* Draw dot graph, use nodes and edges stored in post state *)
      let lts = LTS.create () in
      LTS.NodeSet.iter (fun node -> 
        log "%a = %d\n" LTSLocation.pp node.location node.id;
        LTS.add_vertex lts node;
      ) post.graph_nodes;
      LTS.EdgeSet.iter (fun edge -> 
        LTS.add_edge_e lts edge;
      ) post.graph_edges;

      let file = Out_channel.create "test_graph.dot" in
      let () = Dot.output_graph file lts in
      Out_channel.close file;

      log "[INITIAL NORMS]\n";
      Exp.Set.iter (fun norm -> log "  %a\n" Exp.pp norm) post.initial_norms;
      let dcp = LTS.create () in
      LTS.NodeSet.iter (fun node -> 
        LTS.add_vertex dcp node;
      ) post.graph_nodes;


      (* Much easier to implement and more readable in imperative style.
        * Derive difference constraints for each edge for each norm and
        * add newly created norms unprocessed_norms set during the process *)
      let unprocessed_norms = ref post.initial_norms in
      let processed_norms = ref Exp.Set.empty in
      let graph_edges = ref post.graph_edges in
      while not (Exp.Set.is_empty !unprocessed_norms) do (
        let norm = Exp.Set.min_elt !unprocessed_norms in
        unprocessed_norms := Exp.Set.remove norm !unprocessed_norms;
        processed_norms := Exp.Set.add norm !processed_norms;
        match norm with
        | Exp.BinOp _ -> (
          graph_edges := LTS.EdgeSet.map (fun (src, edge_data, dst) -> 
            let edge_data, new_norms = GraphEdge.derive_constraints edge_data norm formals in

            (* Remove duplicate norms and add new norms to unprocessed set *)
            let new_norms = Exp.Set.diff new_norms (Exp.Set.inter new_norms !processed_norms) in
            unprocessed_norms := Exp.Set.union new_norms !unprocessed_norms;
            (src, edge_data, dst)
          ) !graph_edges;
        )
        | _ -> () (* Ignore other norms for now *)
      ) done;

      log "[FINAL NORMS]\n";
      Exp.Set.iter (fun norm -> log "  %a\n" Exp.pp norm) !processed_norms;

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
      LTS.EdgeSet.iter (fun (src, data, dst) -> 
        GraphEdge.derive_guards data !processed_norms solver ctx;
        LTS.add_edge_e dcp (src, data, dst);
      ) !graph_edges;
      
      let guarded_nodes = LTS.fold_edges_e (fun (_, edge_data, dst) acc -> 
        if Exp.Set.is_empty edge_data.guards then acc else LTS.NodeSet.add dst acc
      ) dcp LTS.NodeSet.empty
      in

      (* Propagate guard to all outgoing edges if all incoming edges
        * are guarded by this guard and the guard itself is not decreased
        * on any of those incoming edges (guard is a norm) *)
      let rec propagate_guards : LTS.NodeSet.t -> unit = fun nodes -> (
        if not (LTS.NodeSet.is_empty nodes) then (
          let node = LTS.NodeSet.min_elt nodes in
          let nodes = LTS.NodeSet.remove node nodes in
          let incoming_edges = LTS.pred_e dcp node in
          let rec aux : Exp.Set.t -> LTS.edge list -> Exp.Set.t =
          fun acc edges -> match edges with
          | (_, edge_data, _) :: edges -> (
            (* Get edge guards that are not decreased on this edge *)
            let acc = Exp.Set.fold (fun guard acc -> 
              match DC.Map.get_dc guard edge_data.constraints with
              | Some dc -> 
                if DC.is_decreasing dc && DC.same_norms dc then acc 
                else Exp.Set.add guard acc
              | _ -> Exp.Set.add guard acc
            ) edge_data.guards Exp.Set.empty
            in
            Exp.Set.inter acc (aux acc edges)
          )
          | [] -> acc
          in
          
          (* Get guards that are used on all incoming
            * edges and which are not decreased *)
          let guards = aux Exp.Set.empty incoming_edges in
          let nodes = if Exp.Set.is_empty guards then (
            nodes
          ) else (
            (* Propagate guards to all outgoing edges and add
              * destination nodes of those edges to the processing queue *)
            let out_edges = LTS.succ_e dcp node in
            List.fold out_edges ~init:nodes ~f:(fun acc (_, (edge_data : GraphEdge.t), dst) -> 
              Exp.Set.iter (fun guard -> 
                edge_data.guards <- Exp.Set.add guard edge_data.guards;
              ) guards;
              LTS.NodeSet.add dst acc
            )
          )
          in
          propagate_guards nodes
        ) else (
          ()
        )
      )
      in
      propagate_guards guarded_nodes;

      (* Convert DCP with guards to DCP without guards over natural numbers *)
      let to_natural_numbers : LTS.EdgeSet.t -> unit = fun edges -> (
        LTS.EdgeSet.iter (fun (_, edge_data, _) -> 
          let constraints = DC.Map.map (fun (rhs, const) -> 
            if IntLit.isnegative const then (
              let const = if Exp.Set.mem rhs edge_data.guards then IntLit.minus_one else IntLit.zero in
              rhs, const
            ) else (
              rhs, const
            )
          ) edge_data.constraints
          in
          edge_data.constraints <- constraints
        ) edges
      )
      in
      to_natural_numbers !graph_edges;

      let file = Out_channel.create "test_dcp.dot" in
      let () = Dot.output_graph file dcp in
      Out_channel.close file;

      Payload.update_summary post summary
    ) 
    | None -> 
      L.(die InternalError)
      "Analyzer failed to compute post for %a" Typ.Procname.pp
      (Procdesc.get_proc_name proc_data.pdesc)