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

  type nonrec extras = string

  let pp_session_name node fmt = F.fprintf fmt "loopus %a" CFG.Node.pp_id (CFG.Node.id node)

  (* Take an abstract state and instruction, produce a new abstract state *)
  let exec_instr : Domain.astate -> 'a ProcData.t -> CFG.Node.t -> Sil.instr -> Domain.astate =
    fun astate _ node instr ->

    let open Domain in

    let is_exit_node = match ProcCFG.Node.kind node with 
      | Procdesc.Node.Exit_node -> true 
      | _ -> false 
    in

    let astate = match instr with
    | Prune (_exp, loc, branch, kind) -> 
      ( 
        log "[PRUNE] (%a)\n" Location.pp loc;
        let lts_loc = LTSLocation.PruneLoc (kind, loc) in
        let newLocSet = LocSet.add loc astate.branchLocs in
        let newEdge = Edge.set_end astate.current_edge lts_loc in

        let prune_node = GraphNode.make lts_loc in
        let lhs = astate.aggregateJoin.lhs in
        let rhs = astate.aggregateJoin.rhs in
        let graph_nodes = LTSNodeSet.add prune_node astate.graphNodes in

        let is_direct_backedge = LTSLocation.equal lts_loc lhs || LTSLocation.equal lts_loc rhs in
        let graph_edges, graph_nodes = if is_direct_backedge then (
          (* Discard join node and all edges poiting to it and instead make
           * one direct backedge with variables modified inside the loop *)
          let join_edges =  astate.aggregateJoin.edges in
          let edge = List.find_exn (LTSEdgeSet.elements join_edges) ~f:(fun edge -> 
            let backedge_origin = LTS.E.src edge in
            GraphNode.equal backedge_origin prune_node
          ) in
          let backedge = LTS.E.create (LTS.E.src edge) (LTS.E.label edge) prune_node in
          let graph_edges = LTSEdgeSet.add backedge astate.graphEdges in
          let graph_nodes = LTSNodeSet.remove astate.lastNode graph_nodes in
          graph_edges, graph_nodes
        ) else (
          (* Add all accumulated edges pointing to aggregated join node and
           * new edge pointing from aggregated join node to this prune node *)
          (* let edge_label = get_edge_label astate.branchingPath in
          let edge_label = F.sprintf "%s\n%s" edge_label modified_vars in *)
          let path_end = List.last astate.branchingPath in
          let edge_data = GraphEdge.make astate.edgeFormulas path_end in
          let new_lts_edge = LTS.E.create astate.lastNode edge_data prune_node in
          let graph_edges = LTSEdgeSet.add new_lts_edge astate.graphEdges in
          let graph_edges = LTSEdgeSet.union astate.aggregateJoin.edges graph_edges in
          graph_edges, graph_nodes
        )
        in
        { astate with
          (* pruneLocs = prune_locs; *)
          branchingPath = astate.branchingPath @ [(kind, branch, loc)];
          branchLocs = newLocSet; 
          edges = EdgeSet.add newEdge astate.edges;
          current_edge = Edge.initial lts_loc;
          lastLoc = lts_loc;

          edgeFormulas = Exp.Set.empty;
          lastNode = prune_node;
          graphNodes = graph_nodes;
          graphEdges = graph_edges;
          aggregateJoin = AggregateJoin.initial;
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

    | Remove_temps (_, loc) -> 
      (
        log "[REMOVE_TEMPS] %a\n" Location.pp loc;
        if is_exit_node then (
          log "  Exit node\n";
          let exit_node = GraphNode.make LTSLocation.Exit in
          (* let modified_vars = Edge.modified_to_string astate.current_edge in
          let edge_label = get_edge_label astate.branchingPath in
          let edge_label = F.sprintf "%s\n%s" edge_label modified_vars in *)
          let path_end = List.last astate.branchingPath in
          let edge_data = GraphEdge.make astate.edgeFormulas path_end in
          let new_lts_edge = LTS.E.create astate.lastNode edge_data exit_node in
          let graph_edges = LTSEdgeSet.add new_lts_edge astate.graphEdges in
          let graph_nodes = LTSNodeSet.add exit_node astate.graphNodes in
          { astate with
            graphNodes = graph_nodes;
            graphEdges = graph_edges;
          }
        ) else (
          astate
        )  
      )

    | Store (lexp, _expType, rexp, loc) ->
      (
        log "[STORE] (%a) | %a = %a\n" Location.pp loc Exp.pp lexp Exp.pp rexp;
        let formula = match rexp with
        | Exp.Const _ -> Exp.eq lexp rexp
        | _ -> lexp (* TODO *)
        in
        let formulas = Exp.Set.add formula astate.edgeFormulas in
        let pvars = Sequence.append (Exp.program_vars lexp) (Exp.program_vars rexp) in
        let edge = Edge.add_modified astate.current_edge pvars in
        { astate with current_edge = edge; edgeFormulas = formulas; }
      )

    | Load (_ident, _lexp, _typ, loc) ->
      (
        log "[LOAD] (%a)\n" Location.pp loc;
        (* let pvars = Exp.program_vars lexp in
        let edge = Domain.Edge.add_modified astate.current_edge pvars in
        log "  Modified: [%a]\n" Domain.PvarSet.pp edge.modified_vars;
        {astate with current_edge = edge} *)
        astate
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
      let procName = Procdesc.get_proc_name proc_desc in 
      let procNameStr = Typ.Procname.to_simplified_string procName in
      log "\n\n---------------------------------";
      log "\n- ANALYZING %s" procNameStr;
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

      let extras = "extras test" in
      let proc_data = ProcData.make proc_desc tenv extras in
      let begin_loc = Domain.LTSLocation.Start beginLoc in
      match Analyzer.compute_post proc_data ~initial:(Domain.initial begin_loc) with
      | Some post ->
        (
          log "\n---------------------------------";
          log "\n------- [ANALYSIS REPORT] -------";
          log "\n---------------------------------\n";
          log "%a" Domain.pp post;

          (* Draw dot graph, use nodes and edges stored in post state *)
          let lts = Domain.LTS.create () in
          Domain.LTSNodeSet.iter (fun node -> 
            log "%a = %d\n" Domain.LTSLocation.pp node.location node.id;
            Domain.LTS.add_vertex lts node;
          ) post.graphNodes;
          Domain.LTSEdgeSet.iter (fun edge -> 
            Domain.LTS.add_edge_e lts edge;
          ) post.graphEdges;

          let file = Out_channel.create "test_graph.dot" in
          let () = Domain.Dot.output_graph file lts in
          Out_channel.close file;

          Payload.update_summary post summary
        ) 
      | None -> 
        L.(die InternalError)
        "Analyzer failed to compute post for %a" Typ.Procname.pp
        (Procdesc.get_proc_name proc_data.pdesc)