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

        let missing_formulas = generate_missing_formulas astate in
        let formulas = Formula.Set.union astate.edge_formulas missing_formulas in

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

          let path_end = List.last astate.branchingPath in
          let edge_data = GraphEdge.make formulas path_end in
          let new_lts_edge = LTS.E.create astate.last_node edge_data prune_node in
          let graph_edges = LTS.EdgeSet.add new_lts_edge astate.graph_edges in
          let graph_edges = LTS.EdgeSet.union astate.aggregate_join.edges graph_edges in
          graph_edges, graph_nodes
        )
        in

        let pvar_condition = substitute_pvars cond in
        let prune_formula = match pvar_condition with
        | Exp.BinOp (op, lexp, rexp) -> (lexp, Formula.Binop op, rexp)
        | Exp.UnOp (LNot, exp, _) -> (
          (* Currently handles only "!exp" *)
          match exp with
          | Exp.BinOp (op, lexp, rexp) -> (
            (* Handles "!(lexp BINOP rexp)" *)
            let negate_binop binop = match binop with
            | Binop.Lt -> Binop.Ge
            | Binop.Gt -> Binop.Le
            | Binop.Le -> Binop.Gt
            | Binop.Ge -> Binop.Lt
            | Binop.Eq -> Binop.Ne
            | Binop.Ne -> Binop.Eq
            | _ -> L.(die InternalError)"Unsupported prune condition type!"
            in
            (lexp, Formula.Binop (negate_binop op), rexp)
          )
          | Exp.Const const -> (
            (* Handles "!CONST" *)
            (Exp.Const const, Formula.Binop Binop.Eq, Exp.Const (Const.Cint IntLit.zero))
          )
          | _ -> L.(die InternalError)"Unsupported prune condition type!"
        )
        | Exp.Const _ -> (cond, Formula.Binop Binop.Ne, Exp.Const (Const.Cint IntLit.zero))
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

        let norms = if branch && is_loop_prune kind then (
          match prune_formula with
          | (lexp, Formula.Binop op, rexp) -> (
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


        let formulas = Formula.Set.add (prune_formula) Formula.Set.empty in
        { astate with
          branchingPath = astate.branchingPath @ [(kind, branch, loc)];
          branchLocs = newLocSet; 
          edges = Edge.Set.add newEdge astate.edges;
          current_edge = Edge.initial lts_loc;
          lastLoc = lts_loc;

          initial_norms = norms;
          tracked_formals = tracked_formals;
          modified_pvars = PvarSet.empty;
          edge_formulas = formulas;
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
          let edge_data = GraphEdge.make astate.edge_formulas path_end in
          let new_lts_edge = LTS.E.create astate.last_node edge_data exit_node in
          let graph_edges = LTS.EdgeSet.add new_lts_edge astate.graph_edges in
          let graph_edges = LTS.EdgeSet.union astate.aggregate_join.edges graph_edges in
          let graph_nodes = LTS.NodeSet.add exit_node astate.graph_nodes in
          { astate with
            graph_nodes = graph_nodes;
            graph_edges = graph_edges;
          }
        ) else (
          astate
        )  
      )

    | Store (lexp, _expType, rexp, loc) ->
      (
        log "[STORE] (%a) | %a = %a | %B\n" Location.pp loc Exp.pp lexp Exp.pp rexp is_pvar_decl_node;
        (* let find_formula_rhs lhs_pvar = 
          let rhs_set = Formula.Set.filter (fun formula -> 
            match formula with 
            | (Exp.Lvar lexp_pvar, Formula.Assignment, rexp) when Pvar.equal lhs_pvar lexp_pvar -> true
            | _ -> false
          ) astate.edge_formulas
          in
          Formula.Set.min_elt_opt rhs_set
        in *)

        let find_formula_rhs lexp = Formula.Set.fold (fun formula acc -> 
            match formula with 
            | (lhs, Formula.Assignment, rexp) when Exp.equal lexp lhs -> rexp
            | _ -> acc
          ) astate.edge_formulas lexp 
        in

        let pvar_rexp = substitute_pvars rexp in

        (* Substitute rexp based on previous assignments, 
         * eg. [beg = i; end = beg;] becomes [beg = i; end = i] *)
        let pvar_rexp = match pvar_rexp with
        | Exp.BinOp (Binop.PlusA, Exp.Lvar lexp, Exp.Const (Const.Cint c1)) -> (
          (* [BINOP] PVAR + CONST *)
          let formula_rhs = find_formula_rhs (Exp.Lvar lexp) in
          match formula_rhs with
          | Exp.BinOp (Binop.PlusA, lexp, Exp.Const (Const.Cint c2)) -> (
            (* [BINOP] (PVAR + C1) + C2 -> PVAR + (C1 + C2) *)
            let const = Exp.Const (Const.Cint (IntLit.add c1 c2)) in
            Exp.BinOp (Binop.PlusA, lexp, const)
          )
          | _ -> pvar_rexp
        )
        | Exp.Lvar rhs_pvar -> (
          let rhs_pvar = Formula.Set.fold (fun formula acc -> 
            match formula with 
            | (Exp.Lvar lexp_pvar, Formula.Assignment, Exp.Lvar rexp_pvar) when Pvar.equal rhs_pvar lexp_pvar -> rexp_pvar
            | _ -> acc
          ) astate.edge_formulas rhs_pvar in
          Exp.Lvar rhs_pvar
        )
        | _ -> pvar_rexp
        in

        (* Check if set already contains assignment formula
         * with specified lhs and replace it with updated formulas if so *)
        let formulas = Formula.Set.filter (function
          | (lhs, Formula.Assignment, _) when Exp.equal lexp lhs -> false
          | _ -> true
        ) astate.edge_formulas
        in
        let formulas = Formula.Set.add (lexp, Formula.Assignment, pvar_rexp) formulas in

        let modified_pvars = match lexp with
        | Exp.Lvar pvar -> PvarSet.add pvar astate.modified_pvars
        | _ -> astate.modified_pvars
        in
        let pvars = Sequence.append (Exp.program_vars lexp) (Exp.program_vars rexp) in
        let edge = Edge.add_modified astate.current_edge pvars in
        { astate with 
          current_edge = edge; 
          edge_formulas = formulas; 
          modified_pvars = modified_pvars;
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


module CFG = ProcCfg.NormalOneInstrPerNode
(* module CFG = ProcCfg.Normal *)
  module Analyzer = AbstractInterpreter.Make (CFG) (TransferFunctions)
    let checker {Callbacks.tenv; proc_desc; summary} : Summary.t =
      let beginLoc = Procdesc.get_loc proc_desc in
      let proc_name = Procdesc.get_proc_name proc_desc in 
      log "\n\n---------------------------------";
      log "\n- ANALYZING %s" (Typ.Procname.to_simplified_string proc_name);
      log "\n---------------------------------\n";
      log " Begin location: %a\n" Location.pp beginLoc;

      let locals = Procdesc.get_locals proc_desc in
      List.iter locals ~f:(fun local -> log "%a\n" Procdesc.pp_local local);
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
      let formals = List.fold formals_mangled ~init:Domain.PvarSet.empty ~f:(fun acc (name, _) ->
        let formal_pvar = Pvar.mk name proc_name in
        Domain.PvarSet.add formal_pvar acc
      )
      in
      let locals_list = Procdesc.get_locals proc_desc in
      let locals = List.fold locals ~init:Domain.PvarSet.empty ~f:(fun acc (local : ProcAttributes.var_data) ->
        let pvar = Pvar.mk local.name proc_name in
        Domain.PvarSet.add pvar acc
      )
      in
      let extras = (locals, formals) in
      let proc_data = ProcData.make proc_desc tenv extras in
      let begin_loc = Domain.LTSLocation.Start beginLoc in
      let initial_state = Domain.initial begin_loc locals in
      match Analyzer.compute_post proc_data ~initial:initial_state with
      | Some post ->
        (
          log "\n---------------------------------";
          log "\n------- [ANALYSIS REPORT] -------";
          log "\n---------------------------------\n";
          log "%a" Domain.pp post;

          (* Draw dot graph, use nodes and edges stored in post state *)
          let lts = Domain.LTS.create () in
          Domain.LTS.NodeSet.iter (fun node -> 
            log "%a = %d\n" Domain.LTSLocation.pp node.location node.id;
            Domain.LTS.add_vertex lts node;
          ) post.graph_nodes;
          Domain.LTS.EdgeSet.iter (fun edge -> 
            Domain.LTS.add_edge_e lts edge;
          ) post.graph_edges;

          let file = Out_channel.create "test_graph.dot" in
          let () = Domain.Dot.output_graph file lts in
          Out_channel.close file;

          log "[INITIAL NORMS]\n";
          Exp.Set.iter (fun norm -> log "  %a\n" Exp.pp norm) post.initial_norms;
          let dcp = Domain.LTS.create () in
          Domain.LTS.NodeSet.iter (fun node -> 
            Domain.LTS.add_vertex dcp node;
          ) post.graph_nodes;


          (* Much easier to implement and more readable in imperative style *)
          let unprocessed_norms = ref post.initial_norms in
          let processed_norms = ref Exp.Set.empty in
          let graph_edges = ref post.graph_edges in
          while not (Exp.Set.is_empty !unprocessed_norms) do (
            let norm = Exp.Set.min_elt !unprocessed_norms in
            unprocessed_norms := Exp.Set.remove norm !unprocessed_norms;
            processed_norms := Exp.Set.add norm !processed_norms;
            graph_edges := Domain.LTS.EdgeSet.map (fun edge -> 
              let test = norm in
              edge
            ) !graph_edges;
            ()
          ) done;
          (* let final_norms = Domain.LTS.EdgeSet.fold (fun (src, edge_data, dst) acc ->
            let edge_data, norms = Exp.Set.fold (fun norm acc -> 
              Domain.GraphEdge.derive_constraints acc norm
            ) post.initial_norms (edge_data, Exp.Set.empty)
            in
            Domain.LTS.add_edge_e dcp (src, edge_data, dst);
            Exp.Set.union acc norms
          ) post.graph_edges post.initial_norms
          in

          log "[FINAL NORMS]\n";
          Exp.Set.iter (fun norm -> log "  %a\n" Exp.pp norm) final_norms; *)

          let file = Out_channel.create "test_dcp.dot" in
          let () = Domain.Dot.output_graph file dcp in
          Out_channel.close file;

          Payload.update_summary post summary
        ) 
      | None -> 
        L.(die InternalError)
        "Analyzer failed to compute post for %a" Typ.Procname.pp
        (Procdesc.get_proc_name proc_data.pdesc)