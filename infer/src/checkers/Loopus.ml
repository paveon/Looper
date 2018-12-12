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
    fun astate {ProcData.pdesc; tenv; extras} node instr ->
    let open Domain in
    let is_loop_head = CFG.is_loop_head pdesc node in
    let (shouldLog, loc) = match instr with
    | Prune (_, loc, _, _) | Load (_,_,_,loc) | Store (_,_,_,loc) | Call (_,_,_,loc,_) -> (true, loc)
    | _ -> (false, Location.dummy) in

    (* log "Loop head: %B\n" is_loop_head; *)
    (* if shouldLog then log "\n[State info] %a\n" pp_path astate.branchingPath; *)

    let astate = match instr with
    | Prune (exp, loc, branch, kind) -> 
      ( 
        let is_loop_prune = match kind with
          | Ik_dowhile | Ik_for | Ik_while -> true
          | _ -> false
        in

        log "[PRUNE] (%a)\n" Location.pp loc;
        let lts_loc = LTSLocation.PruneLoc loc in
        let newLocSet = LocSet.add loc astate.branchLocs in
        let newEdge = Edge.set_end astate.current_edge lts_loc in
        let modifiedVars = Edge.modified_to_string astate.current_edge in

        let prune_label = F.sprintf "%s\n%s" (Sil.if_kind_to_string kind) (Location.to_string loc) in 
        let prune_node = GraphNode.make lts_loc prune_label in
        let lhs = astate.joinNode.lhs in
        let rhs = astate.joinNode.rhs in
        let graph_nodes = NodeSet.add prune_node astate.graphNodes in

        let is_direct_backedge = LTSLocation.equal lts_loc lhs || LTSLocation.equal lts_loc rhs in
        let graph_edges, graph_nodes = if is_direct_backedge then (
          (* Discard join node and all edges poiting to it and instead make
           * one direct backedge with variables modified inside the loop *)
          let join_edges =  astate.joinNode.edges in
          let edge = List.find_exn (GEdgeSet.elements join_edges) ~f:(fun edge -> 
            let backedge_origin = LTS.E.src edge in
            GraphNode.equal backedge_origin prune_node
          ) in
          let backedge = LTS.E.create (LTS.E.src edge) (LTS.E.label edge) prune_node in
          let graph_edges = GEdgeSet.add backedge astate.graphEdges in
          let graph_nodes = NodeSet.remove astate.lastNode graph_nodes in
          graph_edges, graph_nodes
        ) else (
          (* Add all accumulated edges pointing to aggregated join node and
           * new edge pointing from aggregated join node to this prune node *)
          let edge_label = get_edge_label astate.branchingPath in
          let edge_label = F.sprintf "%s\n%s" edge_label modifiedVars in
          let new_edge = LTS.E.create astate.lastNode edge_label prune_node in
          let graph_edges = GEdgeSet.add new_edge astate.graphEdges in
          let graph_edges = GEdgeSet.union astate.joinNode.edges graph_edges in
          graph_edges, graph_nodes
        )
        in

        let astate = { astate with
          (* pruneLocs = prune_locs; *)
          branchingPath = astate.branchingPath @ [(kind, branch, loc)];
          branchLocs = newLocSet; 
          edges = EdgeSet.add newEdge astate.edges;
          current_edge = Edge.initial (LTSLocation.PruneLoc loc);
          lastLoc = LTSLocation.PruneLoc loc;

          lastNode = prune_node;
          graphNodes = graph_nodes;
          graphEdges = graph_edges;
          joinNode = JoinNode.initial;
        } in

        (* (
          match kind with
          | Ik_dowhile | Ik_for | Ik_while -> log "    Loop header location\n"
          | _ -> log "    Branching\n"
        ); *)

        (* log "    Edges:\n";
        EdgeSet.iter (fun edge -> 
          log "      %a\n" Edge.pp edge
        ) astate.edges; *)

        astate
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
        (* log "[REMOVE_TEMPS] %a\n" Location.pp loc; *)
        astate
      )

    | Store (lexp, expType, rexp, loc) ->
      (
        (* log "  [STORE] (%a)\n" Location.pp loc; *)
        let pvars = Sequence.append (Exp.program_vars lexp) (Exp.program_vars rexp) in
        let edge = Edge.add_modified astate.current_edge pvars in
        (* log "  Modified: [%a]\n" Domain.PvarSet.pp edge.modified_vars; *)
        {astate with current_edge = edge}
      )

    | Load (ident, lexp, typ, loc) ->
      (
        (* log "  [LOAD] (%a)\n" Location.pp loc; *)
        (* let pvars = Exp.program_vars lexp in
        let edge = Domain.Edge.add_modified astate.current_edge pvars in
        log "  Modified: [%a]\n" Domain.PvarSet.pp edge.modified_vars;
        {astate with current_edge = edge} *)
        astate
      )
    | Call (retValue, Const Cfun callee_pname, actuals, loc, _) ->
      ( 
        let fun_name = Typ.Procname.to_simplified_string callee_pname in
        log "  [CALL] (%a)\n" Location.pp loc;
        astate
      )

    (* Rest of SIL instruction possibilites *)
    | _ -> 
      (
        log "[UNKNOWN INSTRUCTION]\n";
        astate
      )
    in
    (* if shouldLog then log "  Last prune location: %a\n" Location.pp astate.lastLoc; *)
    (* if shouldLog then log "  Current edge start: %a\n" LTSLocation.pp astate.current_edge.loc_begin; *)
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

      let reportBugs : Domain.astate -> unit = fun post ->
        ()
        (* LocationMap.iter (fun loopLoc bugSet ->
        let msg = F.asprintf "Redundant traversal of %a detected in loop" Domain.pp_footprint bugSet in
        (* let msg = F.asprintf "Redundant traversal bug detected\n" in *)
        let localised_msg = Localise.verbatim_desc msg in
        let issue = IssueType.redundant_traversal in
        let exn = Exceptions.Checkers (issue, localised_msg) in
        Reporting.log_warning summary ~loc:loopLoc IssueType.redundant_traversal msg
        ) post.bugLocs;  *)
      in

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

          let lts = Domain.LTS.create () in
          Domain.NodeSet.iter (fun node -> 
            log "%a = %d\n" Domain.LTSLocation.pp node.location node.id;
            Domain.LTS.add_vertex lts node;
          ) post.graphNodes;
          Domain.GEdgeSet.iter (fun edge -> 
            Domain.LTS.add_edge_e lts edge;
          ) post.graphEdges;

          (* Domain.PruneLocations.iter (fun _ prune_node -> 
            Domain.LTS.add_vertex lts prune_node
          ) post.pruneLocs;
          Domain.JoinLocations.iter (fun key value -> 
            let label = F.sprintf "JOIN (%d)" value in
            let loc = Domain.LTSLocation.Join value in
            let join_node = Domain.GraphNode.make loc label in
            Domain.LTS.add_vertex lts join_node
          ) post.joinLocs; *)

          let file = Out_channel.create "test_graph.dot" in
          let () = Domain.Dot.output_graph file lts in
          Out_channel.close file;

          Payload.update_summary post summary
        ) 
      | None -> 
        L.(die InternalError)
        "Analyzer failed to compute post for %a" Typ.Procname.pp
        (Procdesc.get_proc_name proc_data.pdesc)