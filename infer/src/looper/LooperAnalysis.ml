(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
open LooperUtils
module F = Format
module L = Logging
module DC = DifferenceConstraint
module LTS = LabeledTransitionSystem
module DCP = DifferenceConstraintProgram
module RG = ResetGraph
module VFG = VariableFlowGraph

let console_log : ('a, F.formatter, unit) format -> 'a = fun fmt -> F.printf fmt

module LTS_Dot = Graph.Graphviz.Dot (LTS)
module DCP_Dot = Graph.Graphviz.Dot (DCP)
module RG_Dot = Graph.Graphviz.Dot (RG)
module VFG_Dot = Graph.Graphviz.Dot (VFG)
module DCP_SCC = Graph.Components.Make (DCP)
module VFG_SCC = Graph.Components.Make (VFG)

module UnprocessedNormSet = Caml.Set.Make (struct
  type nonrec t = EdgeExp.T.t * EdgeExp.AssignmentSet.t [@@deriving compare]
end)

(* TODO: This is not very efficient solution. Figure out a better way *)
module NormSetMap = Caml.Map.Make (struct
  type nonrec t = EdgeExp.Set.t list

  let compare = List.compare (fun x y -> EdgeExp.Set.compare x y)
end)

let lts_fname = "LTS.dot"

let dcp_fname = "DCP.dot"

let g_dcp_fname = "DCP_guarded.dot"

let vfg_fname = "VFG.dot"

let rg_fname = "RG.dot"

let dcp_sccs_fname = "DCP_SCCs.dot"

let vfg_sccs_fname = "VFG_SCCs.dot"

let ssa_dcp_fname = "SSA_DCP.dot"

let summary_graph_fname = "SummaryGraph.dot"

let looper_dir = Config.(results_dir ^/ "../Looper/")

let graphs_dir = looper_dir ^/ "Graphs/"

let mk_outfile fname =
  match Utils.create_outfile fname with
  | None ->
      L.die InternalError "Could not create '%s'." fname
  | Some outf ->
      outf


let analyze_procedure ({InterproceduralAnalysis.proc_desc; exe_env} as analysis_data) =
  (* clang_initializer_prefix *)
  (* Config.clang_initializer_prefix *)
  let begin_loc = Procdesc.get_loc proc_desc in
  let proc_name = Procdesc.get_proc_name proc_desc in
  let proc_name_str = String.drop_suffix (Procname.to_simplified_string proc_name) 2 in
  let is_initializer_proc =
    String.is_prefix proc_name_str ~prefix:Config.clang_initializer_prefix
  in
  if is_initializer_proc then (* Ignore clang initializers *)
    None
  else
    let report_issue =
      Reporting.log_issue analysis_data.proc_desc analysis_data.err_log
        ~loc:(Procdesc.get_loc proc_desc) Looper
    in
    let prover_map = Provers.get_prover_map analysis_data in
    let active_prover = Provers.ProverMap.find Z3 prover_map in
    active_prover.idents <- StringMap.empty ;
    active_prover.vars <- StringMap.empty ;
    let source_file_str = SourceFile.to_string begin_loc.file in
    let source_file_str =
      (String.rstrip ~drop:(fun x -> not (Char.equal x '.')) source_file_str |> String.drop_suffix)
        1
    in
    let proc_graph_dir = graphs_dir ^/ source_file_str ^/ proc_name_str in
    Utils.create_dir (F.asprintf "%s/Logs/%s/" looper_dir source_file_str) ;
    (* Utils.create_dir (F.asprintf "%s/%s/" looper_dir proc_graph_dir) ; *)
    let debug_log_fname = looper_dir ^/ "Logs" ^/ source_file_str ^/ proc_name_str ^ ".log" in
    let log_file = mk_outfile debug_log_fname in
    debug_fmt := log_file.fmt :: !debug_fmt ;
    let debug_log format = F.fprintf log_file.fmt format in
    try
      debug_log "@[<v>[LOOPER] Source: %s, Procedure '%s' [%a]@,@," source_file_str proc_name_str
        Location.pp (Procdesc.get_loc proc_desc) ;
      debug_log "---------------------------------@," ;
      debug_log "- LTS CONSTRUCTION@," ;
      debug_log "---------------------------------@," ;
      let tenv = Exe_env.get_proc_tenv exe_env proc_name in
      let graph_data = GraphConstructor.construct analysis_data in
      let formals = graph_data.formals in
      output_graph (proc_graph_dir ^/ lts_fname) graph_data.lts LTS_Dot.output_graph ;
      debug_log
        "@,\
         ---------------------------------@,\
         - PERFORMING ANALYSIS @,\
         ---------------------------------@," ;
      (* Draw dot graph, use nodes and edges stored in graph_data *)
      debug_log "@[<v2>[INITIAL NORMS]@," ;
      EdgeExp.Set.iter (fun norm -> debug_log "%a@," EdgeExp.pp norm) graph_data.norms ;
      debug_log "@]@," ;
      let edge_pairs =
        LTS.EdgeSet.fold
          (fun ((_, edge_data, _) as lts_edge) edge_pairs ->
            let dcp_edge_data = DCP.EdgeData.from_lts_edge edge_data in
            (lts_edge, dcp_edge_data) :: edge_pairs )
          graph_data.edges []
      in
      (* let rec compute_norm_set unprocessed processed =
           if UnprocessedNormSet.is_empty unprocessed then processed
           else
             let ((norm, norm_history) as unprocessed_norm) = UnprocessedNormSet.min_elt unprocessed in
             let unprocessed = UnprocessedNormSet.remove unprocessed_norm unprocessed in
             debug_log "@[<v4>[DC derivation] Processing norm: %a@," EdgeExp.pp norm ;
             let unprocessed =
               if EdgeExp.is_variable norm formals tenv && not (EdgeExp.Set.mem norm processed) then
                 List.fold edge_pairs
                   ~f:(fun unprocessed (((src, lts_edge_data, dst) as lts_edge), dcp_edge_data) ->
                     debug_log "@[<v2>Deriving for edge: %a  ---->  %a@," LTS.Node.pp src LTS.Node.pp dst ;
                     let used_assignments =
                       match LTS.EdgeMap.find_opt lts_edge norm_history with
                       | Some set ->
                           set
                       | None ->
                           AccessExpressionSet.empty
                     in
                     debug_log "Used assignments before: " ;
                     AccessExpressionSet.iter
                       (fun access -> debug_log "%a " HilExp.AccessExpression.pp access)
                       used_assignments ;
                     debug_log "@," ;
                     let substituted_accesses, dc_rhs_opt, new_norms =
                       LTS.EdgeData.derive_constraint lts_edge_data norm used_assignments formals tenv
                         proc_name
                     in
                     let used_assignments =
                       AccessExpressionSet.union used_assignments substituted_accesses
                     in
                     ( match dc_rhs_opt with
                     | Some dc_rhs ->
                         let dc = (norm, dc_rhs) in
                         debug_log "Adding new DC: %a@," DC.pp dc ;
                         DCP.EdgeData.add_constraint dcp_edge_data dc
                     | None ->
                         debug_log
                           "DC could not be derived (undefined variable of norm expression at source or \
                            destination LTS location)@," ) ;
                     let unprocessed =
                       EdgeExp.Set.fold
                         (fun new_norm unprocessed ->
                           (* Remember used assignments on this specific edge to avoid infinite recursive
                            * loop when generating new norms from assignments such as [i = i * n] *)
                           debug_log "Used assignments after: " ;
                           AccessExpressionSet.iter
                             (fun access -> debug_log "%a " HilExp.AccessExpression.pp access)
                             used_assignments ;
                           debug_log "@," ;
                           let new_norm_history =
                             LTS.EdgeMap.add lts_edge used_assignments norm_history
                           in
                           if EdgeExp.Set.mem new_norm processed then unprocessed
                           else (
                             debug_log "Adding new norm: %a@," EdgeExp.pp new_norm ;
                             UnprocessedNormSet.add (new_norm, new_norm_history) unprocessed ) )
                         new_norms unprocessed
                     in
                     debug_log "@]@," ;
                     unprocessed )
                   ~init:unprocessed
               else unprocessed
             in
             debug_log "@]@," ;
             let processed = EdgeExp.Set.add norm processed in
             compute_norm_set unprocessed processed
         in *)
      let print_used_assignments assignments =
        debug_log "@[<v2>[Used assignments]@," ;
        EdgeExp.AssignmentSet.iter
          (fun (access, rhs) ->
            debug_log "%a = %a@," HilExp.AccessExpression.pp access EdgeExp.pp rhs )
          assignments ;
        debug_log "@]@,"
      in
      let derive_constraints_for_norm (norm, used_assignments) processed =
        List.fold edge_pairs
          ~f:(fun unprocessed ((src, lts_edge_data, dst), dcp_edge_data) ->
            debug_log "@[<v2>Deriving for edge: %a  ---->  %a@," LTS.Node.pp src LTS.Node.pp dst ;
            print_used_assignments used_assignments ;
            let substituted_accesses, dc_rhs_opt, new_norms =
              LTS.EdgeData.derive_constraint lts_edge_data (norm, used_assignments) formals tenv
                proc_name
            in
            let used_assignments =
              EdgeExp.AssignmentSet.union used_assignments substituted_accesses
            in
            ( match dc_rhs_opt with
            | Some dc_rhs ->
                let dc = (norm, dc_rhs) in
                debug_log "Adding new DC: %a@," DC.pp dc ;
                DCP.EdgeData.add_constraint dcp_edge_data dc
            | None ->
                debug_log
                  "DC could not be derived (undefined variable of norm expression at source or \
                   destination LTS location)@," ) ;
            let unprocessed =
              EdgeExp.Set.fold
                (fun new_norm unprocessed ->
                  (* Remember used assignments on this specific edge to avoid infinite recursive
                   * loop when generating new norms from assignments such as [i = i * n] *)
                  print_used_assignments used_assignments ;
                  if EdgeExp.Set.mem new_norm processed then unprocessed
                  else (
                    debug_log "Adding new norm: %a@," EdgeExp.pp new_norm ;
                    UnprocessedNormSet.add (new_norm, used_assignments) unprocessed ) )
                new_norms unprocessed
            in
            debug_log "@]@," ;
            unprocessed )
          ~init:UnprocessedNormSet.empty
      in
      let rec compute_norm_set unprocessed processed =
        if UnprocessedNormSet.is_empty unprocessed then processed
        else
          let ((norm, used_assignments) as unprocessed_norm) =
            UnprocessedNormSet.min_elt unprocessed
          in
          let unprocessed = UnprocessedNormSet.remove unprocessed_norm unprocessed in
          debug_log "@[<v4>[DC derivation] Processing norm: %a@," EdgeExp.pp norm ;
          let unprocessed =
            if EdgeExp.is_variable norm formals tenv && not (EdgeExp.Set.mem norm processed) then
              let new_unprocessed =
                derive_constraints_for_norm (norm, used_assignments) processed
              in
              UnprocessedNormSet.union unprocessed new_unprocessed
            else unprocessed
          in
          debug_log "@]@," ;
          let processed = EdgeExp.Set.add norm processed in
          compute_norm_set unprocessed processed
      in
      debug_log "@,==========[Deriving constraints]==================@," ;
      let unprocessed_norms =
        EdgeExp.Set.fold
          (fun norm acc -> UnprocessedNormSet.add (norm, EdgeExp.AssignmentSet.empty) acc)
          graph_data.norms UnprocessedNormSet.empty
      in
      let final_norm_set = compute_norm_set unprocessed_norms EdgeExp.Set.empty in
      debug_log "@[<v2>[FINAL NORMS]@," ;
      EdgeExp.Set.iter (fun norm -> debug_log "%a@," EdgeExp.pp norm) final_norm_set ;
      debug_log "@]@," ;
      (* All DCs and norms are derived, now derive guards.
       * Use SMT solver to check which norms on which
       * transitions are guaranted to be greater than 0
       * based on conditions that hold on specified transition.
       * For example if transition is guarded by conditions
       * [x >= 0] and [y > x] then we can prove that
       * norm [x + y] > 0 thus it is a guard on this transition *)
      debug_log "@,@[<v2>==========[Deriving guards]=======================@," ;
      let why3_norms =
        EdgeExp.Set.fold
          (fun norm norms_acc ->
            if EdgeExp.is_const norm then norms_acc
            else
              try
                let why3_exp =
                  EdgeExp.to_why3_expr norm tenv ~selected_theory:active_prover.real_data
                    active_prover
                  |> fst
                in
                (norm, why3_exp) :: norms_acc
              with _ ->
                debug_log "Failed to transform norm '%a' to Why3 expr@," EdgeExp.pp norm ;
                norms_acc )
          final_norm_set []
      in
      let dcp = DCP.create () in
      LTS.NodeSet.iter (fun node -> DCP.add_vertex dcp node) graph_data.nodes ;
      List.iter edge_pairs ~f:(fun ((src, (lts_edge_data : LTS.EdgeData.t), dst), dcp_edge_data) ->
          debug_log "@[<v2>[Guard Derivation] %a ---> %a@," LTS.Node.pp src LTS.Node.pp dst ;
          DCP.EdgeData.set_edge_output_type dcp_edge_data GuardedDCP ;
          let condition_str =
            EdgeExp.output_exp_dnf lts_edge_data.conditions ~and_sep:" && " ~or_sep:" || "
          in
          debug_log "@[<v2>Conditions:@,%s@]@," condition_str ;
          (* debug_log "(%s) ||@," and_term_str *)
          (* debug_log "@]@," ; *)
          (* debug_log "%a@,"
             EdgeExp.(pp_list "Conditions" EdgeExp.pp)
             (EdgeExp.Set.elements lts_edge_data.conditions) ; *)
          let guards = LTS.EdgeData.derive_guards lts_edge_data why3_norms tenv active_prover in
          DCP.EdgeData.add_guards dcp_edge_data guards ;
          debug_log "%a@]@," EdgeExp.(pp_list "Guards" EdgeExp.pp) (EdgeExp.Set.elements guards) ;
          DCP.add_edge_e dcp (src, dcp_edge_data, dst) ) ;
      debug_log "@[<v2>Guarded nodes:@," ;
      let guarded_nodes =
        DCP.fold_edges_e
          (fun (_, edge_data, dst) acc ->
            if EdgeExp.Set.is_empty edge_data.guards then acc
            else (
              debug_log "%a@," LTS.Node.pp dst ;
              LTS.NodeSet.add dst acc ) )
          dcp LTS.NodeSet.empty
      in
      debug_log "@]" ;
      (* Propagate guard to all outgoing edges if all incoming edges
         * are guarded by this guard and the guard itself is not decreased
         * on any of those incoming edges (guard is a norm) *)
      debug_log "@,==========[Propagating guards]====================@," ;
      let rec propagate_guards : LTS.NodeSet.t -> unit =
       fun nodes ->
        if not (LTS.NodeSet.is_empty nodes) then (
          let get_shared_guards incoming_edges =
            if List.is_empty incoming_edges then EdgeExp.Set.empty
            else
              (* let dowhile_guards, edge_guards =
                   List.fold incoming_edges ~init:(EdgeExp.Set.empty, [])
                     ~f:(fun (dowhile_guards, edge_guards) (src, (edge_data : DCP.EdgeData.t), _) ->
                       debug_log "Processing incoming edge from: %a, backedge: %B@," LTS.Node.pp src
                         edge_data.backedge ;
                       let dowhile_guards =
                         match src with
                         | LTS.Node.Prune (Sil.Ik_dowhile, _, _) when edge_data.backedge ->
                             (* dowhile back-edge, exempt any guards. This is a hack for now before we
                                figure out a proper "sound" solution *)
                             EdgeExp.Set.union dowhile_guards edge_data.guards
                         | _ ->
                             dowhile_guards
                       in
                       let edge_guards = DCP.EdgeData.active_guards edge_data :: edge_guards in
                       (dowhile_guards, edge_guards) )
                 in *)
              let shared_guards =
                List.map incoming_edges ~f:(fun (_, edge_data, _) ->
                    DCP.EdgeData.active_guards edge_data )
                |> List.reduce_exn ~f:(fun g1 g2 -> EdgeExp.Set.inter g1 g2)
              in
              shared_guards
            (* let _, head_edge_data, _ = List.hd_exn incoming_edges in
               let acc = DCP.EdgeData.active_guards head_edge_data in
               List.fold (List.tl_exn incoming_edges) ~init:acc
                 ~f:(fun shared_guards (_, edge_data, _) ->
                   (* Get edge guards that are not decreased on this edge *)
                   let guards = DCP.EdgeData.active_guards edge_data in
                   EdgeExp.Set.inter guards shared_guards ) *)
          in
          (* Pop one node from set of unprocessed nodes *)
          let node = LTS.NodeSet.min_elt nodes in
          let nodes = LTS.NodeSet.remove node nodes in
          debug_log "Processing: %a@," LTS.Node.pp node ;
          let backedge_in_edges, in_edges =
            List.partition_tf (DCP.pred_e dcp node) ~f:(fun (_, edge_data, _) ->
                DCP.EdgeData.is_backedge edge_data )
          in
          (* Exempt any guards from dowhile and goto simulated loop back-edges.
             This is a hack for now before we figure out a proper "sound" solution *)
          let exempt_guards =
            List.fold backedge_in_edges ~init:EdgeExp.Set.empty
              ~f:(fun guards_acc (src, (edge_data : DCP.EdgeData.t), dst) ->
                match (src, dst) with
                | LTS.Node.Prune _, LTS.Node.Join _ ->
                    let guards =
                      List.reduce edge_data.condition_norms ~f:(fun g1 g2 ->
                          EdgeExp.Set.union g1 g2 )
                      |> Option.value ~default:EdgeExp.Set.empty
                    in
                    EdgeExp.Set.union guards_acc guards
                | _ ->
                    guards_acc )
          in
          let guards = EdgeExp.Set.union exempt_guards (get_shared_guards in_edges) in
          let out_edges = DCP.succ_e dcp node in
          let nodes =
            List.fold out_edges ~init:nodes
              ~f:(fun nodes_acc (_, (edge_data : DCP.EdgeData.t), dst) ->
                let updated_guards = EdgeExp.Set.union guards edge_data.guards in
                let old_count = EdgeExp.Set.cardinal edge_data.guards in
                let new_count = EdgeExp.Set.cardinal updated_guards in
                if new_count > old_count then (
                  edge_data.guards <- EdgeExp.Set.union guards edge_data.guards ;
                  LTS.NodeSet.add dst nodes_acc )
                else nodes_acc )
          in
          propagate_guards nodes )
      in
      propagate_guards guarded_nodes ;
      (* Output Guarded DCP over integers *)
      output_graph (proc_graph_dir ^/ g_dcp_fname) dcp DCP_Dot.output_graph ;
      debug_log "@.@[<v2>==========[Converting Integer DCP to Natural Numbers]==========@," ;
      (* Convert DCP with guards to DCP without guards over natural numbers *)
      let wrap_norm norm =
        match norm with
        | EdgeExp.T.Strlen _ ->
            norm
        | EdgeExp.T.Access access -> (
            let access_typ = HilExp.AccessExpression.get_typ access tenv in
            match access_typ with
            | Some typ -> (
                if Typ.is_pointer typ then norm
                else
                  match Typ.get_ikind_opt typ with
                  | Some ikind when Typ.ikind_is_unsigned ikind ->
                      norm
                  | _ ->
                      EdgeExp.T.Max (EdgeExp.Set.singleton norm) )
            | _ ->
                EdgeExp.T.Max (EdgeExp.Set.singleton norm) )
        | _ ->
            EdgeExp.T.Max (EdgeExp.Set.singleton norm)
      in
      let to_natural_numbers : DCP.t -> unit =
       fun dcp ->
        DCP.iter_edges_e
          (fun (_, edge_data, _) ->
            let constraints =
              List.fold edge_data.constraints
                ~f:(fun acc (lhs, dc_rhs) ->
                  let convert_dc (rhs_norm, op, rhs_const) =
                    match EdgeExp.evaluate_const_exp rhs_norm with
                    | Some rhs_norm_value ->
                        let const_value =
                          IntLit.max (EdgeExp.eval_consts op rhs_norm_value rhs_const) IntLit.zero
                        in
                        let dc_rhs = (EdgeExp.zero, Binop.PlusA None, const_value) in
                        dc_rhs
                    | None ->
                        let rhs_const =
                          match op with
                          | Binop.PlusA _ ->
                              if IntLit.isnegative rhs_const then
                                if
                                  (* lhs != rhs hack for now, abstraction algorithm presented in the thesis
                                     * doesn't add up in the example 'SingleLinkSimple' where they have [i]' <= [n]-1
                                     * which is indeed right if we want to get valid bound but their abstraction algorithm
                                     * leads to [i]' <= [n] because there's no guard for n on the transition *)
                                  EdgeExp.Set.mem rhs_norm edge_data.guards
                                  || not (EdgeExp.equal lhs rhs_norm)
                                then IntLit.minus_one
                                else IntLit.zero
                              else rhs_const
                          | Binop.Shiftrt ->
                              (* We should be able to transform (e1 <= e2 >> c) into ([e1] <= [e2] >> c) directly,
                                 * because shifting to the right can never result in a negative number, thus abstraction
                                 * ([e1] <= [e2] >> c) should be sound for any positive value of 'c'. We regard
                                 * shifting to the right with negative literal values to be a bug (undefined behaviour
                                 * in most of the languages, usually caught by compilers) *)
                              assert (IntLit.isnegative rhs_const |> not) ;
                              rhs_const
                          | _ ->
                              assert false
                        in
                        (* TODO: Do this more robustly *)
                        (* Try to determine whether the norm needs to be wrapped in Max(x, 0)
                           Do not wrap if exp >= 0 is guaranteed *)
                        (wrap_norm rhs_norm, op, rhs_const)
                  in
                  let lhs = wrap_norm lhs in
                  match dc_rhs with
                  | DC.Value rhs_value ->
                      let rhs_value = convert_dc rhs_value in
                      acc @ [(lhs, DC.Value rhs_value)]
                  | DC.Pair (lb_rhs, ub_rhs) ->
                      let lb_rhs_value = convert_dc lb_rhs in
                      let ub_rhs_value = convert_dc ub_rhs in
                      acc @ [(lhs, DC.Pair (lb_rhs_value, ub_rhs_value))] )
                ~init:[]
            in
            edge_data.constraints <- constraints ;
            DCP.EdgeData.set_edge_output_type edge_data DCP )
          dcp
      in
      to_natural_numbers dcp ;
      output_graph (proc_graph_dir ^/ dcp_fname) dcp DCP_Dot.output_graph ;
      let reset_graph_test = RG.create () in
      DCP.iter_edges_e
        (fun (src, edge_data, dst) ->
          (* Search for resets *)
          List.iter edge_data.constraints ~f:(fun (lhs_norm, dc_rhs) ->
              let check_value_rhs lhs_norm (rhs_norm, op, rhs_const) =
                if not (EdgeExp.equal lhs_norm rhs_norm) then (
                  debug_log "[Reset] %a' <= %a %a %a@," EdgeExp.pp lhs_norm EdgeExp.pp rhs_norm
                    Binop.pp op IntLit.pp rhs_const ;
                  let dst_node = (lhs_norm, EdgeExp.is_symbolic_const lhs_norm formals tenv) in
                  let src_node = (rhs_norm, EdgeExp.is_symbolic_const rhs_norm formals tenv) in
                  RG.add_vertex reset_graph_test dst_node ;
                  RG.add_vertex reset_graph_test src_node ;
                  let const_part = (op, rhs_const) in
                  let edge =
                    RG.E.create src_node (RG.Edge.make (src, edge_data, dst) const_part) dst_node
                  in
                  RG.add_edge_e reset_graph_test edge )
              in
              match dc_rhs with
              | DC.Value dc_rhs_value ->
                  check_value_rhs lhs_norm dc_rhs_value
              | DC.Pair (lb_dc_rhs, ub_dc_rhs) ->
                  check_value_rhs lhs_norm lb_dc_rhs ;
                  check_value_rhs lhs_norm ub_dc_rhs ) )
        dcp ;
      debug_log "@]@," ;
      output_graph (proc_graph_dir ^/ "RG_before_renaming.dot") reset_graph_test RG_Dot.output_graph ;
      (* debug_log "@[<v>"; *)
      let norm_set, formals_vfg_map, terminal_norms_map =
        if not Config.disable_vfg_renaming then (
          (* Create variable flow graph which is necessary for
           * DCP preprocessing which renames variables and consequently
           * ensures that we get an acyclic reset graph *)
          debug_log "@.@[<v2>==========[Creating Variable Flow Graph]==========@," ;
          let variables =
            EdgeExp.Set.fold
              (fun norm acc ->
                (* The subsequent code using these variables is a bit messy and there is
                   no consistent/standard way of determining which norms will be wrapped
                   or won't be wrapped so add both forms as variables *)
                if EdgeExp.is_variable norm formals tenv then EdgeExp.Set.add (wrap_norm norm) acc
                  (* let acc = EdgeExp.Set.add norm acc in
                     EdgeExp.Set.add (EdgeExp.T.Max (EdgeExp.Set.singleton norm)) acc *)
                else acc )
              final_norm_set EdgeExp.Set.empty
          in
          (* EdgeExp.Set.filter_map
                 (fun norm ->
                   if EdgeExp.is_variable norm formals tenv then
                     Some (EdgeExp.T.Max (EdgeExp.Set.singleton norm))
                   else None )
                 final_norm_set
             in *)
          let vfg = VFG.create () in
          let used_variables =
            DCP.fold_edges_e
              (fun (src, edge_data, dst) acc ->
                List.fold edge_data.constraints ~init:acc
                  ~f:(fun used_variables_acc (lhs_norm, dc_rhs) ->
                    let dst_node = (lhs_norm, dst) in
                    let lhs_is_var = EdgeExp.Set.mem lhs_norm variables in
                    let vfg_add_node node =
                      if not (VFG.mem_vertex vfg node) then VFG.add_vertex vfg node
                    in
                    let process_value_rhs used_variables_acc (rhs_norm, _, _) =
                      let rhs_is_var = EdgeExp.Set.mem rhs_norm variables in
                      if lhs_is_var && rhs_is_var then (
                        let src_node = (rhs_norm, src) in
                        vfg_add_node dst_node ;
                        vfg_add_node src_node ;
                        VFG.add_edge_e vfg (VFG.E.create src_node VFG.Edge.default dst_node) ;
                        EdgeExp.Set.add lhs_norm used_variables_acc )
                      else used_variables_acc
                      (* EdgeExp.Set.add rhs_norm (EdgeExp.Set.add lhs_norm used_variables_acc) *)
                      (* if EdgeExp.equal lhs_norm rhs_norm then used_variables_acc
                         else EdgeExp.Set.add lhs_norm used_variables_acc *)
                    in
                    match dc_rhs with
                    | DC.Value dc_rhs_value ->
                        process_value_rhs used_variables_acc dc_rhs_value
                    | DC.Pair (lb_dc_rhs, ub_dc_rhs) ->
                        (process_value_rhs used_variables_acc lb_dc_rhs |> process_value_rhs)
                          ub_dc_rhs ) )
              dcp EdgeExp.Set.empty
          in
          let ssa_variables = EdgeExp.Set.diff variables used_variables in
          debug_log "@[<v2>[SSA VARIABLES]@," ;
          EdgeExp.Set.iter (fun norm -> debug_log "%a@," EdgeExp.pp norm) ssa_variables ;
          debug_log "@]@," ;
          (* Store initializations of SSA variables *)
          let ssa_var_initialization_map =
            EdgeExp.Set.fold
              (fun ssa_var mapping ->
                if EdgeExp.is_return ssa_var then mapping
                else
                  (* This terrible API doesn't provide more suitable
                     function so we have to iterate over all edges *)
                  let reset_opt =
                    DCP.fold_edges_e
                      (fun (_, edge_data, _) reset_opt ->
                        match (reset_opt, DCP.EdgeData.get_reset edge_data ssa_var) with
                        | Some existing_reset, Some new_reset ->
                            if EdgeExp.ValuePair.equal existing_reset new_reset then reset_opt
                            else
                              L.die InternalError
                                "Multiple resets of supposed SSA variable: %a = %a | %a" EdgeExp.pp
                                ssa_var EdgeExp.ValuePair.pp existing_reset EdgeExp.ValuePair.pp
                                new_reset
                        | None, Some new_reset ->
                            Some new_reset
                        | _ ->
                            reset_opt )
                      dcp None
                  in
                  match reset_opt with
                  | Some reset ->
                      EdgeExp.Map.add ssa_var reset mapping
                  | None ->
                      debug_log "Missing initialization of SSA variable '%a'. Adding '%a = %a'@."
                        EdgeExp.pp ssa_var EdgeExp.pp ssa_var EdgeExp.pp ssa_var ;
                      EdgeExp.Map.add ssa_var (EdgeExp.ValuePair.V ssa_var) mapping )
              ssa_variables EdgeExp.Map.empty
          in
          debug_log "@[<v2>[SSA VARIABLES INITIALIZATION]@," ;
          EdgeExp.Map.iter
            (fun lhs pair -> debug_log "%a = %a@," EdgeExp.pp lhs EdgeExp.ValuePair.pp pair)
            ssa_var_initialization_map ;
          debug_log "@]@," ;
          output_graph (proc_graph_dir ^/ vfg_fname) vfg VFG_Dot.output_graph ;
          (* Construct VFG name map, create fresh variable 'v' for each SCC
           * and map each VFG node to this fresh variable. *)
          debug_log "@[<v2>[Creating VFG mapping]@," ;
          let vfg_components = VFG_SCC.scc_list vfg in
          let get_vfg_scc_edges vfg vfg_components scc_graph =
            List.fold vfg_components ~init:VFG.EdgeSet.empty ~f:(fun acc component ->
                (* Iterate over all combinations of SCC nodes and check if there
                 * are edges between them in both directions *)
                List.fold component ~init:acc ~f:(fun acc node ->
                    VFG.add_vertex scc_graph node ;
                    List.fold component ~init:acc ~f:(fun acc node2 ->
                        let edges = VFG.EdgeSet.of_list (VFG.find_all_edges vfg node node2) in
                        VFG.EdgeSet.union acc edges ) ) )
          in
          let vfg_scc_graph = VFG.create () in
          let scc_edges = get_vfg_scc_edges vfg vfg_components vfg_scc_graph in
          VFG.EdgeSet.iter
            (fun (src, edge_data, dst) -> VFG.add_edge_e vfg_scc_graph (src, edge_data, dst))
            scc_edges ;
          output_graph (proc_graph_dir ^/ vfg_sccs_fname) vfg_scc_graph VFG_Dot.output_graph ;
          debug_log "SCC count: %d@," (List.length vfg_components) ;
          let vfg_map, vfg_norm_set =
            List.foldi vfg_components
              ~f:(fun idx (map, norm_set) component ->
                let pvar = Pvar.mk (Mangled.from_string ("var_" ^ string_of_int idx)) proc_name in
                let pvar_access =
                  HilExp.AccessExpression.base (AccessPath.base_of_pvar pvar (Typ.mk (Tint IUInt)))
                in
                let aux_norm = EdgeExp.T.Access pvar_access in
                List.fold component
                  ~init:(map, EdgeExp.Set.add aux_norm norm_set)
                  ~f:(fun (map, norm_set) ((exp, _) as node : VFG.Node.t) ->
                    if EdgeExp.is_return exp then
                      (VFG.Map.add node exp map, EdgeExp.Set.add exp norm_set)
                    else (VFG.Map.add node aux_norm map, norm_set) ) )
              ~init:(VFG.Map.empty, EdgeExp.Set.empty)
          in
          debug_log "@[<v2>[Mapping]@," ;
          let formals_vfg_map, terminal_norms_map =
            VFG.Map.fold
              (fun (norm, dcp_node) aux_norm (formals_acc, terminals_acc) ->
                debug_log "(%a, %a)   --->   %a@," LTS.Node.pp dcp_node EdgeExp.pp norm EdgeExp.pp
                  aux_norm ;
                let formals_acc =
                  if EdgeExp.is_formal_variable norm formals tenv then
                    let exit_aux_norm = match dcp_node with LTS.Node.Exit -> true | _ -> false in
                    EdgeExp.Map.add aux_norm (norm, exit_aux_norm) formals_acc
                  else formals_acc
                in
                let terminals_acc =
                  if EdgeExp.is_chain_terminal_norm norm formals then
                    EdgeExp.Map.add aux_norm norm terminals_acc
                  else terminals_acc
                in
                (formals_acc, terminals_acc) )
              vfg_map
              (EdgeExp.Map.empty, EdgeExp.Map.empty)
          in
          debug_log "@]@," ;
          (* Apply VFG mapping and rename DCP variables to ensure acyclic reset DAG *)
          DCP.iter_edges_e
            (fun (dcp_src, edge_data, dcp_dst) ->
              (* Rename condition norms *)
              let condition_norms =
                List.map edge_data.condition_norms ~f:(fun norm_set ->
                    EdgeExp.Set.map
                      (fun norm ->
                        if EdgeExp.is_chain_terminal_norm norm formals then norm
                        else
                          let wrapped_norm = wrap_norm norm in
                          let vfg_node = (wrapped_norm, dcp_src) in
                          debug_log "FINDING VFG NODE: (%a, %a)@," EdgeExp.pp wrapped_norm
                            LTS.Node.pp dcp_src ;
                          match VFG.Map.find_opt vfg_node vfg_map with
                          | Some vfg_norm ->
                              vfg_norm
                          | None -> (
                            (* This case should occur only for SSA variables which are constant after initialization *)
                            match EdgeExp.Map.find_opt wrapped_norm ssa_var_initialization_map with
                            | Some (EdgeExp.ValuePair.V value) ->
                                value
                            | Some (EdgeExp.ValuePair.P _) ->
                                L.die InternalError "Not implemented: %d@," __LINE__
                            | _ ->
                                wrapped_norm ) )
                      norm_set )
              in
              let constraints =
                List.fold edge_data.constraints ~init:[] ~f:(fun acc (lhs_norm, dc_rhs) ->
                    let lhs_node = (lhs_norm, dcp_dst) in
                    let lhs_vfg_norm = VFG.Map.find_opt lhs_node vfg_map in
                    let map_value_rhs (rhs_norm, op, rhs_const) =
                      let rhs_node = (rhs_norm, dcp_src) in
                      let rhs_vfg_node = VFG.Map.find_opt rhs_node vfg_map in
                      debug_log "@[<v2>[map_value_rhs]@," ;
                      debug_log "LHS VFG Mapping: %a --> %s@," EdgeExp.pp lhs_norm
                        (Option.value_map lhs_vfg_norm ~default:"None" ~f:(fun v ->
                             EdgeExp.to_string v ) ) ;
                      debug_log "RHS VFG Mapping: %a --> %s@," EdgeExp.pp rhs_norm
                        (Option.value_map rhs_vfg_node ~default:"None" ~f:(fun v ->
                             EdgeExp.to_string v ) ) ;
                      debug_log "@]@," ;
                      match (lhs_vfg_norm, VFG.Map.find_opt rhs_node vfg_map) with
                      | Some lhs_mapped, Some rhs_mapped ->
                          (lhs_mapped, (rhs_mapped, op, rhs_const))
                      | None, Some rhs_mapped ->
                          (lhs_norm, (rhs_mapped, op, rhs_const))
                          (* if EdgeExp.is_variable lhs_norm formals tenv then None
                             else Some (lhs_norm, (rhs_mapped, op, rhs_const)) *)
                      | Some lhs_mapped, None ->
                          (lhs_mapped, (rhs_norm, op, rhs_const))
                          (* if EdgeExp.is_variable rhs_norm formals tenv then None
                             else Some (lhs_mapped, (rhs_norm, op, rhs_const)) *)
                      | None, None ->
                          (lhs_norm, (rhs_norm, op, rhs_const))
                      (* if EdgeExp.is_return lhs_norm then
                           if EdgeExp.is_variable rhs_norm formals tenv then None
                           else Some (lhs_norm, (rhs_norm, op, rhs_const))
                         else if
                           EdgeExp.is_variable rhs_norm formals tenv
                           || EdgeExp.is_variable lhs_norm formals tenv
                         then None
                         else Some (lhs_norm, (rhs_norm, op, rhs_const)) *)
                    in
                    (* TODO: This whole part is kinda weird, need to figure out if it would
                     * be better to change the VFG definition to work with DC.value_pair nodes instead? *)
                    match dc_rhs with
                    | DC.Value value_rhs ->
                        let lhs_norm_mapped, rhs_mapped = map_value_rhs value_rhs in
                        acc @ [(lhs_norm_mapped, DC.Value rhs_mapped)]
                    | DC.Pair (lb_rhs, ub_rhs) ->
                        let lb_norm, lb_op, lb_c = lb_rhs in
                        let ub_norm, ub_op, ub_c = ub_rhs in
                        debug_log "Mapping pair: %a %a, %a %a@," EdgeExp.pp lb_norm DC.pp_const_part
                          (lb_op, lb_c) EdgeExp.pp ub_norm DC.pp_const_part (ub_op, ub_c) ;
                        let lb_lhs_mapped, lb_rhs_mapped = map_value_rhs lb_rhs in
                        let ub_lhs_mapped, ub_rhs_mapped = map_value_rhs ub_rhs in
                        if EdgeExp.equal lb_lhs_mapped ub_lhs_mapped then
                          acc @ [(lb_lhs_mapped, DC.Pair (lb_rhs_mapped, ub_rhs_mapped))]
                        else (
                          debug_log "[Unhandled] Not implemented: %d@," __LINE__ ;
                          assert false
                          (* acc @ [(lb_lhs_mapped, DC.Pair (lb_rhs_mapped, ub_rhs_mapped))] *) )
                    (* match (map_value_rhs lb_rhs, map_value_rhs ub_rhs) with
                       | Some (lb_lhs, lb_rhs), Some (ub_lhs, ub_rhs) ->
                           debug_log "[Unhandled] Not implemented: %d@," __LINE__ ;
                           assert (EdgeExp.equal lb_lhs ub_lhs) ;
                           acc @ [(lhs_norm, DC.Pair (lb_rhs, ub_rhs))]
                       | Some (lhs, rhs), None | None, Some (lhs, rhs) ->
                           debug_log "[Unhandled] Not implemented: %d@," __LINE__ ;
                           (* TODO: not sure about this, figure out later *)
                           acc @ [(lhs, DC.Value rhs)]
                       | None, None ->
                           debug_log "[Unhandled] Not implemented: %d@," __LINE__ ;
                           acc *) )
              in
              let calls_renamed_args =
                EdgeExp.CallPair.Set.map
                  (fun call_pair ->
                    let rename_call_value (ret_typ, proc_name, args, loc) =
                      let lb_args, ub_args, lb_ub_equal =
                        List.fold args ~init:([], [], true)
                          ~f:(fun (lb_args, ub_args, lb_ub_equal) (arg, typ) ->
                            if EdgeExp.is_integer_type typ then (
                              debug_log "RENAMING ARG: %a@," EdgeExp.pp arg ;
                              let renamed_arg_pair =
                                EdgeExp.ValuePair.map_accesses arg ~f:(fun access ->
                                    let access = EdgeExp.T.Access access in
                                    if EdgeExp.is_symbolic_const access formals tenv then
                                      EdgeExp.ValuePair.V access
                                    else
                                      (* A little hack-around, need to figure out how to deal with this later *)
                                      let possible_keys =
                                        [ (EdgeExp.T.Max (EdgeExp.Set.singleton access), dcp_dst)
                                        ; (EdgeExp.T.Max (EdgeExp.Set.singleton access), dcp_src)
                                        ; (access, dcp_dst)
                                        ; (access, dcp_src) ]
                                      in
                                      let vfg_var_opt =
                                        List.find_map possible_keys ~f:(fun vfg_node ->
                                            VFG.Map.find_opt vfg_node vfg_map )
                                      in
                                      match vfg_var_opt with
                                      | Some v ->
                                          EdgeExp.ValuePair.V v
                                      | None -> (
                                          (* This case should occur only for SSA variables which are constant after initialization *)
                                          let possible_ssa_map_keys =
                                            [EdgeExp.T.Max (EdgeExp.Set.singleton access); access]
                                          in
                                          let ssa_map_key_opt =
                                            List.find possible_ssa_map_keys ~f:(fun key ->
                                                EdgeExp.Map.mem key ssa_var_initialization_map )
                                          in
                                          match ssa_map_key_opt with
                                          | Some key ->
                                              EdgeExp.Map.find key ssa_var_initialization_map
                                          | None ->
                                              L.die InternalError "MAPPING ACCESS: %a@," EdgeExp.pp
                                                access ) )
                              in
                              match renamed_arg_pair with
                              | EdgeExp.ValuePair.V renamed_arg ->
                                  ( lb_args @ [(renamed_arg, typ)]
                                  , ub_args @ [(renamed_arg, typ)]
                                  , lb_ub_equal )
                              | EdgeExp.ValuePair.P (lb, ub) ->
                                  ( lb_args @ [(lb, typ)]
                                  , ub_args @ [(ub, typ)]
                                  , lb_ub_equal && EdgeExp.equal lb ub ) )
                            else (lb_args @ [(arg, typ)], ub_args @ [(arg, typ)], lb_ub_equal) )
                      in
                      if lb_ub_equal then EdgeExp.CallPair.V (ret_typ, proc_name, lb_args, loc)
                      else
                        EdgeExp.CallPair.P
                          ((ret_typ, proc_name, lb_args, loc), (ret_typ, proc_name, ub_args, loc))
                    in
                    match call_pair with
                    | EdgeExp.CallPair.V call_value ->
                        rename_call_value call_value
                    | EdgeExp.CallPair.P (lb_call, ub_call) -> (
                      (* TODO: This is HORRIBLY wrong and incorrect, just a proof of concept.
                       * Figure this out later, how to deal with this without branching explosion *)
                      match (rename_call_value lb_call, rename_call_value ub_call) with
                      | EdgeExp.CallPair.V renamed_lb_call, EdgeExp.CallPair.V renamed_ub_call ->
                          EdgeExp.CallPair.P (renamed_lb_call, renamed_ub_call)
                      | EdgeExp.CallPair.P (renamed_lb_call, _), EdgeExp.CallPair.V renamed_ub_call
                        ->
                          EdgeExp.CallPair.P (renamed_lb_call, renamed_ub_call)
                      | EdgeExp.CallPair.V renamed_lb_call, EdgeExp.CallPair.P (_, renamed_ub_call)
                        ->
                          EdgeExp.CallPair.P (renamed_lb_call, renamed_ub_call)
                      | ( EdgeExp.CallPair.P (renamed_lb_call, _)
                        , EdgeExp.CallPair.P (_, renamed_ub_call) ) ->
                          EdgeExp.CallPair.P (renamed_lb_call, renamed_ub_call) ) )
                  edge_data.calls
              in
              edge_data.condition_norms <- condition_norms ;
              edge_data.calls <- calls_renamed_args ;
              edge_data.constraints <- constraints ;
              DCP.EdgeData.set_edge_output_type edge_data DCP )
            dcp ;
          debug_log "@]@," ;
          output_graph (proc_graph_dir ^/ ssa_dcp_fname) dcp DCP_Dot.output_graph ;
          (vfg_norm_set, formals_vfg_map, terminal_norms_map) )
        else
          let formals_vfg_map, terminal_norms_map =
            EdgeExp.Set.fold
              (fun norm (formals_acc, terminals_acc) ->
                let formals_acc =
                  if EdgeExp.is_formal_variable norm formals tenv then
                    EdgeExp.Map.add norm (norm, true) formals_acc
                  else formals_acc
                in
                let terminals_acc =
                  if EdgeExp.is_chain_terminal_norm norm formals then
                    EdgeExp.Map.add norm norm terminals_acc
                  else terminals_acc
                in
                (formals_acc, terminals_acc) )
              final_norm_set
              (EdgeExp.Map.empty, EdgeExp.Map.empty)
          in
          (final_norm_set, formals_vfg_map, terminal_norms_map)
      in
      (* Reset graph construction, must be performed after VFG renaming phase *)
      debug_log "@,@[<v2>==========[Creating Reset Graph]==================@," ;
      let reset_graph = RG.create () in
      DCP.iter_edges_e
        (fun (src, edge_data, dst) ->
          (* Search for resets *)
          List.iter edge_data.constraints ~f:(fun (lhs_norm, dc_rhs) ->
              let process_rhs_value (rhs_norm, op, rhs_const) =
                if not (EdgeExp.equal lhs_norm rhs_norm) then (
                  debug_log "%a' <= %a %a %a@," EdgeExp.pp lhs_norm EdgeExp.pp rhs_norm Binop.pp op
                    IntLit.pp rhs_const ;
                  let dst_node = (lhs_norm, EdgeExp.is_symbolic_const lhs_norm formals tenv) in
                  let src_node = (rhs_norm, EdgeExp.is_symbolic_const rhs_norm formals tenv) in
                  RG.add_vertex reset_graph_test dst_node ;
                  RG.add_vertex reset_graph_test src_node ;
                  let const_part = (op, rhs_const) in
                  let edge =
                    RG.E.create src_node (RG.Edge.make (src, edge_data, dst) const_part) dst_node
                  in
                  RG.add_edge_e reset_graph edge )
              in
              match dc_rhs with
              | DC.Value rhs_value ->
                  process_rhs_value rhs_value
              | DC.Pair (lb_rhs, ub_rhs) ->
                  process_rhs_value lb_rhs ;
                  process_rhs_value ub_rhs ) )
        dcp ;
      debug_log "@]@," ;
      output_graph (proc_graph_dir ^/ rg_fname) reset_graph RG_Dot.output_graph ;
      (* Suboptimal way to find all SCC edges, the ocamlgraph library for some
       * reason does not have a function that returns edges of SCCs. *)
      let get_scc_edges dcp scc_graph =
        let components = DCP_SCC.scc_list dcp in
        List.fold components ~init:DCP.EdgeSet.empty ~f:(fun acc component ->
            (* Iterate over all combinations of SCC nodes and check if there
               * are edges between them in both directions *)
            List.fold component ~init:acc ~f:(fun acc node ->
                DCP.add_vertex scc_graph node ;
                List.fold component ~init:acc ~f:(fun acc node2 ->
                    let edges = DCP.EdgeSet.of_list (DCP.find_all_edges dcp node node2) in
                    DCP.EdgeSet.union acc edges ) ) )
      in
      debug_log "@,==========[Determining Local Bounds]==============@," ;
      let dcp_edge_set =
        DCP.fold_edges_e (fun edge acc -> DCP.EdgeSet.add edge acc) dcp DCP.EdgeSet.empty
      in
      let dcp_scc_graph = DCP.create () in
      let scc_edges = get_scc_edges dcp dcp_scc_graph in
      (* Create SCC graph *)
      DCP.EdgeSet.iter
        (fun (src, edge_data, dst) -> DCP.add_edge_e dcp_scc_graph (src, edge_data, dst))
        scc_edges ;
      output_graph (proc_graph_dir ^/ dcp_sccs_fname) dcp_scc_graph DCP_Dot.output_graph ;
      (* Edges that are not part of any SCC can be executed only once,
       * thus their local bound mapping is 1 and consequently their
       * transition bound TB(t) is 1 *)
      let non_scc_edges = DCP.EdgeSet.diff dcp_edge_set scc_edges in
      DCP.EdgeSet.iter
        (fun (_, edge_data, _) -> edge_data.bound_norms <- [EdgeExp.Set.singleton EdgeExp.one])
        non_scc_edges ;
      let condition_norms_decreasing norms (edge_data : DCP.EdgeData.t) =
        List.exists norms ~f:(fun norm_set ->
            (* It is enough if at least one norm from the compound norm is decreased *)
            EdgeExp.Set.exists
              (fun condition_norm ->
                match DC.get_dc condition_norm edge_data.constraints with
                | Some dc ->
                    DC.same_norms dc && DC.is_decreasing dc
                | _ ->
                    false )
              norm_set )
      in
      let get_decreased_edge_set condition_norms =
        DCP.EdgeSet.filter
          (fun (_, edge_data, _) -> condition_norms_decreasing condition_norms edge_data)
          scc_edges
      in
      debug_log "@[<v2>[Constructing E(cv)]@," ;
      (* For each condition norm cv construct a E(cv) set of edges where it is decreased
         * and assign each edge from this set local bound of cv *)
      let condition_norms_edge_sets =
        DCP.EdgeSet.fold
          (fun (src, edge_data, dst) sets ->
            if List.is_empty edge_data.condition_norms then sets
            else (
              debug_log "[CHECKING] %a ----> %a@," LTS.Node.pp src LTS.Node.pp dst ;
              let bounded_edges = get_decreased_edge_set edge_data.condition_norms in
              debug_log "Bounded edges size: %d@," (DCP.EdgeSet.cardinal bounded_edges) ;
              let sets = NormSetMap.add edge_data.condition_norms bounded_edges sets in
              sets ) )
          scc_edges NormSetMap.empty
      in
      debug_log "@]@,@[<v2>[Removing E(cv) edges]@," ;
      let remaining_edges =
        NormSetMap.fold
          (fun condition_norms norms_edge_set remaining_edges ->
            debug_log "Norm edge set lengths: %d@," (DCP.EdgeSet.cardinal norms_edge_set) ;
            if DCP.EdgeSet.is_empty remaining_edges then remaining_edges
            else if not (DCP.EdgeSet.is_empty norms_edge_set) then (
              (* Apply cv local bound to all E(cv) edges *)
              DCP.EdgeSet.iter
                (fun (_, edge_data, _) ->
                  assert (List.is_empty edge_data.bound_norms) ;
                  debug_log "[1] Assigning condition norm@," ;
                  edge_data.bound_norms <- condition_norms )
                (DCP.EdgeSet.inter norms_edge_set remaining_edges) ;
              let remaining_edges = DCP.EdgeSet.diff remaining_edges norms_edge_set in
              (* Remove edges of E(v) set from DCP *)
              DCP.EdgeSet.iter (fun edge -> DCP.remove_edge_e dcp edge) norms_edge_set ;
              (* Calculate SCCs for modified graph *)
              let scc_edges = get_scc_edges dcp dcp in
              let non_scc_edges = DCP.EdgeSet.diff remaining_edges scc_edges in
              DCP.EdgeSet.iter
                (fun (_, edge_data, _) ->
                  assert (List.is_empty edge_data.bound_norms) ;
                  debug_log "[2] Assigning condition norm@," ;
                  edge_data.bound_norms <- condition_norms )
                non_scc_edges ;
              (* Restore DCP *)
              DCP.EdgeSet.iter (fun edge -> DCP.add_edge_e dcp edge) norms_edge_set ;
              DCP.EdgeSet.diff remaining_edges non_scc_edges )
            else remaining_edges )
          condition_norms_edge_sets scc_edges
      in
      debug_log "@]@," ;
      (* For each variable norm construct a E(v) set of edges where it is decreased
         * and assign each edge from this set local bound of v *)
      let norm_edge_sets =
        DCP.EdgeSet.fold
          (fun ((_, edge_data, _) as edge) sets ->
            List.fold edge_data.constraints ~init:sets ~f:(fun sets ((lhs_norm, _) as dc) ->
                if EdgeExp.Set.mem lhs_norm norm_set && DC.same_norms dc && DC.is_decreasing dc then
                  EdgeExp.Map.update lhs_norm
                    (fun set_opt ->
                      match set_opt with
                      | Some edge_set ->
                          Some (DCP.EdgeSet.add edge edge_set)
                      | None ->
                          Some (DCP.EdgeSet.singleton edge) )
                    sets
                else sets ) )
          scc_edges EdgeExp.Map.empty
      in
      debug_log "@[<v>" ;
      EdgeExp.Map.iter
        (fun norm edge_set ->
          if not (DCP.EdgeSet.is_empty edge_set) then (
            debug_log "@[<v2>E(%a):@," EdgeExp.pp norm ;
            DCP.EdgeSet.iter (fun edge -> debug_log "%a@," DCP.pp_edge edge) edge_set ;
            debug_log "@]@," ) )
        norm_edge_sets ;
      debug_log "@]@," ;
      (* Find local bounds for remaining edges that were not processed by
         * the first or second step. Use previously constructed E(v) sets
         * and for each set try to remove edges from the DCP graph. If some
         * unprocessed edges cease to be part of any SCC after the removal,
         * assign variable v as local bound of those edges *)
      let remaining_edges =
        EdgeExp.Map.fold
          (fun norm norm_edge_set remaining_edges ->
            if DCP.EdgeSet.is_empty remaining_edges then remaining_edges
            else if not (DCP.EdgeSet.is_empty norm_edge_set) then (
              (* Apply v local bound to all E(v) edges *)
              DCP.EdgeSet.iter
                (fun (_, edge_data, _) ->
                  assert (List.is_empty edge_data.bound_norms) ;
                  edge_data.bound_norms <- [EdgeExp.Set.singleton norm] )
                (DCP.EdgeSet.inter norm_edge_set remaining_edges) ;
              let remaining_edges = DCP.EdgeSet.diff remaining_edges norm_edge_set in
              (* Remove edges of E(v) set from DCP *)
              DCP.EdgeSet.iter (fun edge -> DCP.remove_edge_e dcp edge) norm_edge_set ;
              (* Calculate SCCs for modified graph *)
              let scc_edges = get_scc_edges dcp dcp in
              let non_scc_edges = DCP.EdgeSet.diff remaining_edges scc_edges in
              DCP.EdgeSet.iter
                (fun (_, edge_data, _) ->
                  assert (List.is_empty edge_data.bound_norms) ;
                  edge_data.bound_norms <- [EdgeExp.Set.singleton norm] )
                non_scc_edges ;
              (* Restore DCP *)
              DCP.EdgeSet.iter (fun edge -> DCP.add_edge_e dcp edge) norm_edge_set ;
              DCP.EdgeSet.diff remaining_edges non_scc_edges )
            else remaining_edges )
          norm_edge_sets remaining_edges
      in
      (* Re-output DCP graph with local bounds  *)
      output_graph (proc_graph_dir ^/ ssa_dcp_fname) dcp DCP_Dot.output_graph ;
      let get_update_map norm edges (cache : LooperSummary.cache) =
        if EdgeExp.Map.mem norm cache.updates then cache
        else
          ( (* Create missing increments and resets sets for this variable norm *)
            let updates =
              DCP.EdgeSet.fold
                (fun ((_, edge_data, _) as edge) (updates : LooperSummary.norm_updates) ->
                  match DC.get_dc norm edge_data.constraints with
                  | Some ((_, dc_rhs) as dc) -> (
                      let process_value_rhs (rhs_norm, _, rhs_const)
                          (updates : LooperSummary.norm_updates) =
                        (* Variable norm is used on this edge *)
                        if DC.is_reset dc then
                          let resets =
                            LooperSummary.Resets.add (edge, rhs_norm, rhs_const) updates.resets
                          in
                          {updates with resets}
                        else if DC.is_decreasing dc then
                          let decrements =
                            LooperSummary.Decrements.add (edge, rhs_const) updates.decrements
                          in
                          {updates with decrements}
                        else if not (IntLit.iszero rhs_const) then
                          let increments =
                            LooperSummary.Increments.add (edge, rhs_const) updates.increments
                          in
                          {updates with increments}
                        else updates
                      in
                      match dc_rhs with
                      | DC.Value value_rhs ->
                          process_value_rhs value_rhs updates
                      | DC.Pair (lb_rhs, ub_rhs) ->
                          process_value_rhs lb_rhs updates |> process_value_rhs ub_rhs )
                  | None ->
                      updates )
                edges LooperSummary.empty_updates
            in
            {cache with updates= EdgeExp.Map.add norm updates cache.updates}
            : LooperSummary.cache )
      in
      let is_terminal_norm norm =
        (* TODO: More robust solution, should we terminate on globals?
           Should we at least check that the global is not updated in the analyzed function? *)
        match norm with
        | EdgeExp.T.Access access ->
            let base_var, _ = HilExp.AccessExpression.get_base access in
            Var.is_global base_var || not (EdgeExp.is_variable norm formals tenv)
        | _ ->
            not (EdgeExp.is_variable norm formals tenv)
      in
      let rec calculate_increment_sum norms cache =
        debug_log "@[<v2>[Increment Sum]@," ;
        let sum, cache =
          EdgeExp.Set.fold
            (fun norm (total_sum, cache) ->
              (* Calculates increment sum based on increments of variable norm:
                 * SUM(TB(t) * const) for all edges where norm is incremented, 0 if nowhere *)
              let cache = get_update_map norm dcp_edge_set cache in
              let norm_updates = EdgeExp.Map.find norm cache.updates in
              let increment_sum, cache =
                LooperSummary.Increments.fold
                  (fun (edge, const) (increment_sum, cache) ->
                    let bound, cache = transition_bound edge cache in
                    let const = EdgeExp.mult bound (EdgeExp.T.Const (Const.Cint const)) in
                    (EdgeExp.add increment_sum const, cache) )
                  norm_updates.increments (EdgeExp.zero, cache)
              in
              debug_log "%a: %a@," EdgeExp.pp norm EdgeExp.pp increment_sum ;
              (EdgeExp.add total_sum increment_sum, cache) )
            norms (EdgeExp.zero, cache)
        in
        debug_log "Final Increment Sum: %a@]@," EdgeExp.pp sum ;
        (sum, cache)
      and calculate_decrement_sum norms cache =
        debug_log "@[<v2>[Decrement Sum]@," ;
        let sum, cache =
          EdgeExp.Set.fold
            (fun norm (total_sum, cache) ->
              (* Calculates decrement sum based on decrements of variable norm:
                 * SUM(TB(t) * const) for all edges where norm is decremented, 0 if nowhere *)
              let cache = get_update_map norm dcp_edge_set cache in
              let norm_updates = EdgeExp.Map.find norm cache.updates in
              let decrement_sum, cache =
                LooperSummary.Decrements.fold
                  (fun (edge, const) (decrement_sum, cache) ->
                    let bound, cache = transition_bound edge cache in
                    let const = EdgeExp.mult bound (EdgeExp.T.Const (Const.Cint const)) in
                    (EdgeExp.add decrement_sum const, cache) )
                  norm_updates.decrements (EdgeExp.zero, cache)
              in
              debug_log "%a: %a@," EdgeExp.pp norm EdgeExp.pp decrement_sum ;
              (EdgeExp.add total_sum decrement_sum, cache) )
            norms (EdgeExp.zero, cache)
        in
        debug_log "Final Decrement Sum: %a@]@," EdgeExp.pp sum ;
        (sum, cache)
      and calculate_reset_sum chains cache =
        debug_log "@[<v2>[Reset Sum]@," ;
        let sum, cache =
          RG.Chain.Set.fold
            (fun chain (sum, cache) ->
              (* Calculates reset sum based on possible reset chains of reseted norm:
                 * SUM( TB(trans(chain)) * max( VB(in(chain)) + value(chain), 0)) for all reset chains,
                 * where: trans(chain) = all transitions of a reset chain
                 * in(chain) = norm of initial transition of a chain
                 * value(chain) = sum of constants on edges along a chain *)
              let chain_origin_node = RG.Chain.origin chain in
              let chain_value = RG.Chain.value chain in
              let norm = fst chain_origin_node in
              let var_bound, cache = variable_bound ~bound_type:BoundType.Upper norm cache in
              let max_exp, cache =
                if IntLit.isnegative chain_value then
                  (* result can be negative, wrap bound expression in the max function *)
                  let const_bound = EdgeExp.T.Const (Const.Cint (IntLit.neg chain_value)) in
                  let binop_bound =
                    match var_bound with
                    (* max(max(x, 0) - 1, 0) --> max(x - 1, 0) *)
                    | EdgeExp.T.Max args ->
                        EdgeExp.sub (EdgeExp.Set.min_elt args) const_bound
                    | _ ->
                        EdgeExp.sub var_bound const_bound
                  in
                  (EdgeExp.T.Max (EdgeExp.Set.singleton binop_bound), cache)
                else if IntLit.iszero chain_value then (var_bound, cache)
                else
                  (* const > 0 => result must be positive, max function is useless *)
                  let const_bound = EdgeExp.T.Const (Const.Cint chain_value) in
                  let binop_bound = EdgeExp.add var_bound const_bound in
                  (binop_bound, cache)
              in
              debug_log "Calculating TBs of reset chain transitions@," ;
              let reset_exp, cache =
                if EdgeExp.is_zero max_exp then (max_exp, cache)
                else
                  let reset_transition_bounds, cache =
                    DCP.EdgeSet.fold
                      (fun dcp_edge (args, cache_acc) ->
                        let bound, cache_acc = transition_bound dcp_edge cache_acc in
                        (EdgeExp.Set.add bound args, cache_acc) )
                      (RG.Chain.transitions chain) (EdgeExp.Set.empty, cache)
                  in
                  let reset_transition_bounds =
                    if EdgeExp.Set.exists EdgeExp.is_zero reset_transition_bounds then
                      EdgeExp.Set.singleton EdgeExp.zero
                    else reset_transition_bounds
                  in
                  let edge_bound =
                    if Int.equal (EdgeExp.Set.cardinal reset_transition_bounds) 1 then
                      EdgeExp.Set.min_elt reset_transition_bounds
                    else EdgeExp.T.Min reset_transition_bounds
                  in
                  if EdgeExp.is_one edge_bound then (max_exp, cache)
                  else (EdgeExp.mult edge_bound max_exp, cache)
              in
              let _, chain_norms = RG.Chain.norms chain reset_graph in
              let increment_sum, cache = calculate_increment_sum chain_norms cache in
              (EdgeExp.add (EdgeExp.add sum reset_exp) increment_sum, cache) )
            chains (EdgeExp.zero, cache)
        in
        debug_log "Final Reset Sum: %a@]@," EdgeExp.pp sum ;
        (sum, cache)
      and variable_bound ~bound_type norm (cache : LooperSummary.cache) =
        let process_formal_or_global_chain_end end_norm =
          debug_log "@[<v2>Formals mapping:@," ;
          EdgeExp.Map.iter
            (fun k (v, _) -> debug_log "%a --> %a@," EdgeExp.pp k EdgeExp.pp v)
            formals_vfg_map ;
          debug_log "@]@," ;
          match EdgeExp.Map.find_opt end_norm terminal_norms_map with
          | Some terminal_norm ->
              terminal_norm
          | None ->
              let msg =
                F.asprintf
                  "Variable norm '%a' has no existing reset. Assuming Infinite variable bound"
                  EdgeExp.pp end_norm
              in
              debug_log "%s@," msg ;
              report_issue IssueType.looper_infinite_cost msg ;
              EdgeExp.T.Inf
          (* let mapped_global_opt = EdgeExp.Map.find_opt end_norm terminal_norms_map in
             let mapped_formal_opt = EdgeExp.Map.find_opt end_norm formals_vfg_map in
             match (mapped_global_opt, mapped_formal_opt) with
             | Some global_norm, _ ->
                 global_norm
             | _, Some (original_norm, _) when EdgeExp.is_formal_variable original_norm formals tenv ->
                 (* TODO: Hack around for now. When we reach the end of reset
                  * chain for formal variable we treat it as a symbolic constant.
                  * What should we do in those instances? Formals cannot be variables
                  * and symbolic constants at the same time. We should maybe introduce
                  * shadow variables at the beginning of each function *)
                 original_norm
             | _ ->
                 let msg =
                   F.asprintf
                     "Variable norm '%a' has no existing reset. Assuming Infinite variable bound"
                     EdgeExp.pp end_norm
                 in
                 debug_log "%s@," msg ;
                 report_issue IssueType.looper_infinite_cost msg ;
                 EdgeExp.T.Inf *)
        in
        let label, sum_function, bound_cache, min_max_constructor =
          match bound_type with
          | BoundType.Upper ->
              let max_constructor args =
                if Int.equal (EdgeExp.Set.cardinal args) 1 then EdgeExp.Set.min_elt args
                else EdgeExp.T.Max args
              in
              ("UVB", calculate_increment_sum, cache.upper_bounds, max_constructor)
          | BoundType.Lower ->
              let min_constructor args =
                if Int.equal (EdgeExp.Set.cardinal args) 1 then EdgeExp.Set.min_elt args
                else EdgeExp.T.Min args
              in
              ("LVB", calculate_decrement_sum, cache.lower_bounds, min_constructor)
        in
        debug_log "@[<v2>[%s] %a@," label EdgeExp.pp norm ;
        let bound, cache =
          match EdgeExp.Map.find_opt norm bound_cache with
          | Some bound ->
              debug_log "Retrieved from cache@," ;
              (bound, cache)
          | None ->
              let var_bound, (cache : LooperSummary.cache) =
                if is_terminal_norm norm then (
                  debug_log "Terminal norm, returning@," ;
                  (norm, cache) )
                else (
                  debug_log "Retrieving cache for: %a@," EdgeExp.pp norm ;
                  let cache = get_update_map norm dcp_edge_set cache in
                  let norm_updates = EdgeExp.Map.find norm cache.updates in
                  let sum_part, cache = sum_function (EdgeExp.Set.singleton norm) cache in
                  if LooperSummary.Resets.is_empty norm_updates.resets then
                    let reset_value = process_formal_or_global_chain_end norm in
                    let bound = EdgeExp.add reset_value sum_part in
                    (bound, cache)
                  else
                    let min_max_reset_args, (cache : LooperSummary.cache) =
                      LooperSummary.Resets.fold
                        (fun (_, norm, const) (args, cache) ->
                          let var_bound, cache = variable_bound ~bound_type norm cache in
                          let min_max_arg =
                            if IntLit.isnegative const then
                              EdgeExp.sub var_bound (EdgeExp.T.Const (Const.Cint (IntLit.neg const)))
                            else EdgeExp.add var_bound (EdgeExp.T.Const (Const.Cint const))
                          in
                          (EdgeExp.Set.add min_max_arg args, cache) )
                        norm_updates.resets (EdgeExp.Set.empty, cache)
                    in
                    EdgeExp.Set.iter
                      (fun arg -> debug_log "Min-max reset arg: %a@," EdgeExp.pp arg)
                      min_max_reset_args ;
                    (* Unpack nested max expressions
                     * TODO: unpacking should be done only if certain conditions are met,
                     * should think about it later *)
                    (* let rec flatten_nested_min_max args acc_set =
                         EdgeExp.Set.fold
                           (fun arg acc ->
                             match arg with
                             | EdgeExp.T.Max nested_args | EdgeExp.T.Min nested_args ->
                                 flatten_nested_min_max nested_args acc
                             | _ ->
                                 EdgeExp.Set.add arg acc )
                           args acc_set
                       in
                       let min_max_reset_args =
                         flatten_nested_min_max min_max_reset_args EdgeExp.Set.empty
                       in *)
                    let min_max_reset_subexp =
                      match EdgeExp.Set.cardinal min_max_reset_args with
                      | 0 ->
                          L.(die InternalError)
                            "[%s] Missing min/max() arguments for [%a]!" label EdgeExp.pp norm
                      | _ ->
                          min_max_constructor min_max_reset_args
                    in
                    debug_log "BEFORE Min-max reset exp: %a@," EdgeExp.pp min_max_reset_subexp ;
                    let min_max_reset_subexp =
                      Option.value_map (EdgeExp.evaluate_const_exp min_max_reset_subexp)
                        ~default:min_max_reset_subexp ~f:(fun const ->
                          EdgeExp.T.Const (Const.Cint const) )
                    in
                    let var_bound = EdgeExp.add min_max_reset_subexp sum_part in
                    (var_bound, cache) )
              in
              let cache =
                match bound_type with
                | BoundType.Upper ->
                    {cache with upper_bounds= EdgeExp.Map.add norm var_bound cache.upper_bounds}
                | BoundType.Lower ->
                    {cache with lower_bounds= EdgeExp.Map.add norm var_bound cache.lower_bounds}
              in
              (var_bound, cache)
        in
        debug_log "Final %s(%a): %a@]@," label EdgeExp.pp norm EdgeExp.pp bound ;
        (bound, cache)
      and transition_bound (src, (edge_data : DCP.EdgeData.t), dst) (cache : LooperSummary.cache) =
        (* For variable norms: TB(t) = IncrementSum + ResetSum 
         * For constant norms: TB(t) = constant *)
        debug_log "@[<v2>[Transition Bound] %a -- %a@," LTS.Node.pp src LTS.Node.pp dst ;
        let process_norm norm (cache_acc : LooperSummary.cache) =
          if is_terminal_norm norm then (
            debug_log "Local bound is a terminal norm, returning@," ;
            (norm, cache) )
          else (
            (* Get reset chains for local bound *)
            debug_log "@[<v2>[Local bound reset chains]@," ;
            let reset_chains, cache_acc =
              match EdgeExp.Map.find_opt norm cache_acc.reset_chains with
              | Some chains ->
                  (chains, cache_acc)
              | None ->
                  let rg_node = (norm, EdgeExp.is_symbolic_const norm formals tenv) in
                  let chains = RG.get_reset_chains rg_node reset_graph dcp in
                  let cache_acc =
                    {cache_acc with reset_chains= EdgeExp.Map.add norm chains cache_acc.reset_chains}
                  in
                  (chains, cache_acc)
            in
            debug_log "@]@," ;
            let norms =
              RG.Chain.Set.fold
                (fun chain acc ->
                  let norms, _ = RG.Chain.norms chain reset_graph in
                  EdgeExp.Set.union acc norms )
                reset_chains EdgeExp.Set.empty
            in
            let increment_sum, cache_acc = calculate_increment_sum norms cache_acc in
            let reset_sum, cache_acc = calculate_reset_sum reset_chains cache_acc in
            (EdgeExp.add increment_sum reset_sum, cache_acc) )
        in
        match edge_data.bound with
        | Some bound ->
            debug_log "Retrieved from cache: %a@]@," EdgeExp.pp bound ;
            (bound, cache)
        | None -> (
            (* Infinite recursion guard, might occur with exponential bounds which are not supported *)
            if edge_data.computing_bound then
              L.die InternalError "TB(t): Infinite recursion guard encountered" ;
            edge_data.computing_bound <- true ;
            match edge_data.bound_norms with
            | [] ->
                debug_log "Missing Local Bound@," ;
                let bound = EdgeExp.T.Inf in
                debug_log "Final TB: %a@]@," EdgeExp.pp bound ;
                edge_data.bound <- Some bound ;
                (bound, cache)
            | bound_norms ->
                let norm = EdgeExp.Set.min_elt (List.hd_exn bound_norms) in
                debug_log "Local bound: %a@," EdgeExp.pp norm ;
                let or_max_args, cache =
                  List.fold bound_norms ~init:(EdgeExp.Set.empty, cache)
                    ~f:(fun (or_bounds_acc, cache_acc) norm_set ->
                      let and_min_args, cache_acc =
                        EdgeExp.Set.fold
                          (fun norm (norm_bounds, cache_acc) ->
                            let bound, cache_acc = process_norm norm cache_acc in
                            (EdgeExp.Set.add bound norm_bounds, cache_acc) )
                          norm_set (EdgeExp.Set.empty, cache_acc)
                      in
                      (* Loop condition X && Y -> Min(Bound(X), Bound(Y)) *)
                      let and_min_bound =
                        if Int.equal (EdgeExp.Set.cardinal and_min_args) 1 then
                          (* Do not wrap in Min if there's only one bound *)
                          EdgeExp.Set.min_elt and_min_args
                        else EdgeExp.T.Min and_min_args
                      in
                      (EdgeExp.Set.add and_min_bound or_bounds_acc, cache_acc) )
                in
                (* Loop condition X || Y -> Max(Bound(X), Bound(Y)) *)
                let bound =
                  if Int.equal (EdgeExp.Set.cardinal or_max_args) 1 then
                    (* Do not wrap in Max if there's only one bound *)
                    EdgeExp.Set.min_elt or_max_args
                  else EdgeExp.T.Max or_max_args
                in
                debug_log "Final TB: %a@]@," EdgeExp.pp bound ;
                edge_data.bound <- Some bound ;
                (bound, cache) )
      in
      (* Sum together the cost of all functions called on this transition *)
      let instantiate_function_calls (edge_data : DCP.EdgeData.t) cache =
        EdgeExp.CallPair.Set.fold
          (fun call_pair (calls, cache_acc) ->
            match call_pair with
            | EdgeExp.CallPair.V (_, proc_name, args, loc) ->
                debug_log "@[<v2>[Summary Instantiation] %a | %a@," Procname.pp proc_name
                  Location.pp loc ;
                let payload_opt = Location.Map.find_opt loc graph_data.call_summaries in
                let call, cache =
                  match payload_opt with
                  | Some payload ->
                      LooperSummary.instantiate payload proc_name args loc tenv active_prover cache
                        ~variable_bound
                  | None ->
                      (LooperSummary.RealCall {name= proc_name; loc; bounds= []}, cache_acc)
                in
                debug_log "@]@," ;
                (call :: calls, cache)
            | call_pair ->
                L.(die InternalError)
                  "[TODO] Missing implementation for CallPair: %a" EdgeExp.CallPair.pp call_pair )
          edge_data.calls ([], cache)
      in
      let bounds, cache =
        if not (DCP.EdgeSet.is_empty remaining_edges) then (
          debug_log "@[<v2>Local Bound could not be determined for following edges:@," ;
          DCP.EdgeSet.iter
            (fun (src, _, dst) -> debug_log "%a   --->    %a@," LTS.Node.pp src LTS.Node.pp dst)
            remaining_edges ;
          debug_log "@]@," ) ;
        debug_log "@.@[<v>====================[Calculating bounds]====================@," ;
        (* Calculate bound for all back-edges and sum them to get the total bound *)
        try
          let edge_set, cache =
            DCP.fold_edges_e
              (fun ((_, edge_data, _) as edge) (edge_set, cache) ->
                if DCP.EdgeData.is_backedge edge_data then
                  let _, cache = transition_bound edge cache in
                  (DCP.EdgeSet.add edge edge_set, cache)
                else if not (EdgeExp.CallPair.Set.is_empty edge_data.calls) then
                  (DCP.EdgeSet.add edge edge_set, cache)
                else (edge_set, cache) )
              dcp
              (DCP.EdgeSet.empty, LooperSummary.empty_cache)
          in
          (* Execution cost must be computed after transitions bounds
           * to avoid computation cycles *)
          let bounds, cache =
            DCP.EdgeSet.fold
              (fun ((src_node, edge_data, dst_node) as edge) (bounds, cache) ->
                let instantiated_calls, cache = instantiate_function_calls edge_data cache in
                let bound, cache = transition_bound edge cache in
                let monotony_map =
                  if EdgeExp.is_const bound then AccessExpressionMap.empty
                  else EdgeExp.determine_monotonicity bound tenv active_prover
                in
                let transition : LooperSummary.transition =
                  { src_node
                  ; dst_node
                  ; bound
                  ; monotony_map
                  ; calls= instantiated_calls
                  ; backedge= edge_data.backedge }
                in
                (transition :: bounds, cache) )
              edge_set ([], cache)
          in
          (bounds, cache)
        with Exit -> ([], LooperSummary.empty_cache)
      in
      debug_log "@[<v2>Calculating bounds for values under formal pointers@," ;
      let formal_bounds, cache =
        EdgeExp.Map.fold
          (fun aux_norm (formal_variable, exit_norm) (bound_map, cache) ->
            if exit_norm then (
              debug_log "%a   --->    %a@," EdgeExp.pp formal_variable EdgeExp.pp aux_norm ;
              let upper_bound, cache = variable_bound ~bound_type:BoundType.Upper aux_norm cache in
              let lower_bound, cache = variable_bound ~bound_type:BoundType.Lower aux_norm cache in
              (EdgeExp.Map.add formal_variable (lower_bound, upper_bound) bound_map, cache) )
            else (bound_map, cache) )
          formals_vfg_map (EdgeExp.Map.empty, cache)
      in
      debug_log "@]@," ;
      let total_bound_exp = LooperSummary.total_bound bounds |> EdgeExp.simplify in
      debug_log "@[<v>[Final bound] %a@," EdgeExp.pp total_bound_exp ;
      let ret_type = Procdesc.get_ret_type proc_desc in
      let return_bound =
        let return_norm_opt =
          match ret_type.desc with
          | Tint ikind ->
              debug_log "[Return type] %a@," Typ.(pp Pp.text) ret_type ;
              let return_access =
                AccessPath.base_of_pvar (Procdesc.get_ret_var proc_desc) ret_type
                |> HilExp.AccessExpression.base
              in
              (* Wrap or do not wrap based on the type *)
              let return_norm =
                if Typ.ikind_is_unsigned ikind then EdgeExp.T.Access return_access
                else EdgeExp.T.Max (EdgeExp.Set.singleton (EdgeExp.T.Access return_access))
              in
              Some return_norm
          | Tptr _ ->
              debug_log "[Return type] %a@," Typ.(pp Pp.text) ret_type ;
              let return_access =
                AccessPath.base_of_pvar (Procdesc.get_ret_var proc_desc) ret_type
                |> HilExp.AccessExpression.base
              in
              (* Pointers are always unsigned integers by nature *)
              Some (EdgeExp.T.Access return_access)
          | _ ->
              None
        in
        match return_norm_opt with
        | Some return_norm ->
            let ub, cache = variable_bound ~bound_type:BoundType.Upper return_norm cache in
            let lb, _ = variable_bound ~bound_type:BoundType.Lower return_norm cache in
            let lb_simplified = EdgeExp.simplify lb in
            let ub_simplified = EdgeExp.simplify ub in
            if EdgeExp.equal lb_simplified ub_simplified then (
              debug_log "[Return Bound] %a@," EdgeExp.pp ub_simplified ;
              Some (EdgeExp.ValuePair.V ub_simplified) )
            else (
              debug_log "@[<v2>[Return Bound]@,LB: %a@,UB: %a@,@]" EdgeExp.pp lb EdgeExp.pp ub ;
              Some (EdgeExp.ValuePair.P (lb_simplified, ub_simplified)) )
        | _ ->
            None
      in
      let payload : LooperSummary.t =
        { formal_map= FormalMap.make (Procdesc.get_attributes proc_desc)
        ; bounds
        ; return_bound
        ; formal_bounds }
      in
      debug_log "========[Returning payload]========@." ;
      let summary_graph = LooperSummary.to_graph payload proc_name begin_loc in
      output_graph
        (proc_graph_dir ^/ summary_graph_fname)
        summary_graph LooperSummary.TreeGraph_Dot.output_graph ;
      Utils.close_outf log_file ;
      debug_fmt := List.tl_exn !debug_fmt ;
      Some payload
    with error ->
      let stack = Printexc.get_backtrace () in
      debug_log "[Analysis Exception]\n%a\n%s" Exn.pp error stack ;
      debug_log "========[Returning dummy Infinity payload]========@." ;
      report_issue IssueType.looper_infinite_cost "cannot be computed due to thrown exception" ;
      Utils.close_outf log_file ;
      debug_fmt := List.tl_exn !debug_fmt ;
      let dummy_transition : LooperSummary.transition =
        { src_node= LTS.Node.Start (proc_name, begin_loc)
        ; dst_node= LTS.Node.Exit
        ; bound= EdgeExp.T.Inf
        ; monotony_map= AccessExpressionMap.empty
        ; calls= []
        ; backedge= true }
      in
      let payload : LooperSummary.t =
        { formal_map= FormalMap.make (Procdesc.get_attributes proc_desc)
        ; bounds= [dummy_transition]
        ; return_bound= None
        ; formal_bounds= EdgeExp.Map.empty }
      in
      Some payload
