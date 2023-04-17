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
  type nonrec t = EdgeExp.T.t * AccessExpressionSet.t LTS.EdgeMap.t [@@deriving compare]
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


let why3_data = ref ProverMap.empty

let analyze_procedure (analysis_data : LooperSummary.t InterproceduralAnalysis.t) =
  let proc_desc = analysis_data.proc_desc in
  let begin_loc = Procdesc.get_loc proc_desc in
  let source_file_str = SourceFile.to_string begin_loc.file in
  let source_file_str =
    (String.rstrip ~drop:(fun x -> not (Char.equal x '.')) source_file_str |> String.drop_suffix) 1
  in
  let proc_name = Procdesc.get_proc_name proc_desc in
  let proc_name_str = String.drop_suffix (Procname.to_simplified_string proc_name) 2 in
  let proc_graph_dir = graphs_dir ^/ proc_name_str in
  Utils.create_dir (F.asprintf "%s/%s/" looper_dir source_file_str) ;
  let debug_log_fname = looper_dir ^/ source_file_str ^/ proc_name_str ^ ".log" in
  let log_file = mk_outfile debug_log_fname in
  debug_fmt := log_file.fmt :: !debug_fmt ;
  let debug_log format = F.fprintf log_file.fmt format in
  let prover_map : prover_data ProverMap.t =
    if ProverMap.is_empty !why3_data then (
      console_log "=========== Initializing Why3 ===========@," ;
      let config : Why3.Whyconf.config = Why3.Whyconf.init_config None in
      let main : Why3.Whyconf.main = Why3.Whyconf.get_main config in
      let env : Why3.Env.env = Why3.Env.create_env (Why3.Whyconf.loadpath main) in
      let real_theory : Why3.Theory.theory = Why3.Env.read_theory env ["real"] "Real" in
      let prover_map =
        List.fold supported_provers ~init:ProverMap.empty ~f:(fun acc prover_cfg ->
            let filter = Why3.Whyconf.parse_filter_prover prover_cfg.name in
            let provers = Why3.Whyconf.filter_provers config filter in
            if Why3.Whyconf.Mprover.is_empty provers then (
              console_log "[Warning] Prover '%s' is not installed or configured.@," prover_cfg.name ;
              acc )
            else
              let why3_prover_cfg = snd (Why3.Whyconf.Mprover.max_binding provers) in
              let driver : Why3.Driver.driver =
                try Why3.Driver.load_driver_file_and_extras main env prover_cfg.driver_path []
                with e ->
                  L.die InternalError "[Looper] Failed to load driver for %s: %a@." prover_cfg.name
                    Why3.Exn_printer.exn_printer e
              in
              ProverMap.add prover_cfg.prover_type
                { name= prover_cfg.name
                ; driver
                ; main
                ; theory= real_theory
                ; idents= StringMap.empty
                ; vars= StringMap.empty
                ; prover_conf=
                    { why3_prover_cfg with
                      command= prover_cfg.command
                    ; command_steps= prover_cfg.command_steps } }
                acc )
      in
      if ProverMap.is_empty prover_map then
        L.(die UserError)
          "[Looper] No suitable Why3 prover was found.\n\
           Please consult the following Why3 page on how\n\
           to install external provers: 'http://why3.lri.fr/doc/install.html'.\n\
           The list of external provers currently supported by Looper contains Z3 and CVC4.\n\
           The Z3 prover is recommended for best results." ;
      why3_data := prover_map ;
      !why3_data )
    else !why3_data
  in
  let active_prover = ProverMap.find Z3 prover_map in
  active_prover.idents <- StringMap.empty ;
  active_prover.vars <- StringMap.empty ;
  debug_log "@[<v>[LOOPER] Source: %s, Procedure '%s' [%a]@,@," source_file_str proc_name_str
    Location.pp (Procdesc.get_loc proc_desc) ;
  debug_log "---------------------------------@," ;
  debug_log "- LTS CONSTRUCTION@," ;
  debug_log "---------------------------------@," ;
  let tenv = Exe_env.get_proc_tenv analysis_data.exe_env proc_name in
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
  let rec compute_norm_set unprocessed processed =
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
                    let new_norm_history = LTS.EdgeMap.add lts_edge used_assignments norm_history in
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
  in
  debug_log "@,==========[Deriving constraints]==================@," ;
  let unprocessed_norms =
    EdgeExp.Set.fold
      (fun norm acc -> UnprocessedNormSet.add (norm, LTS.EdgeMap.empty) acc)
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
  let dcp = DCP.create () in
  LTS.NodeSet.iter (fun node -> DCP.add_vertex dcp node) graph_data.nodes ;
  List.iter edge_pairs ~f:(fun ((src, (lts_edge_data : LTS.EdgeData.t), dst), dcp_edge_data) ->
      debug_log "@[<v2>[Guard Derivation] %a ---> %a@," LTS.Node.pp src LTS.Node.pp dst ;
      DCP.EdgeData.set_edge_output_type dcp_edge_data GuardedDCP ;
      let condition_str =
        List.map lts_edge_data.conditions ~f:(fun and_terms ->
            let and_terms_str =
              List.map (EdgeExp.Set.elements and_terms) ~f:EdgeExp.to_string
              |> String.concat ~sep:" && "
            in
            F.asprintf "(%s)" and_terms_str )
        |> String.concat ~sep:" || "
      in
      debug_log "@[<v2>Conditions:@,%s@]@," condition_str ;
      (* debug_log "(%s) ||@," and_term_str *)
      (* debug_log "@]@," ; *)
      (* debug_log "%a@,"
         EdgeExp.(pp_list "Conditions" EdgeExp.pp)
         (EdgeExp.Set.elements lts_edge_data.conditions) ; *)
      let guards = LTS.EdgeData.derive_guards lts_edge_data final_norm_set tenv active_prover in
      DCP.EdgeData.add_guards dcp_edge_data guards ;
      debug_log "Guard count: %d@," (EdgeExp.Set.cardinal guards) ;
      debug_log "%a@]@," EdgeExp.(pp_list "Guards" EdgeExp.pp) (EdgeExp.Set.elements guards) ;
      DCP.add_edge_e dcp (src, dcp_edge_data, dst) ) ;
  let guarded_nodes =
    DCP.fold_edges_e
      (fun (_, edge_data, dst) acc ->
        if EdgeExp.Set.is_empty edge_data.guards then acc else LTS.NodeSet.add dst acc )
      dcp LTS.NodeSet.empty
  in
  (* Propagate guard to all outgoing edges if all incoming edges
     * are guarded by this guard and the guard itself is not decreased
     * on any of those incoming edges (guard is a norm) *)
  debug_log "@.@,==========[Propagating guards]====================@," ;
  let rec propagate_guards : LTS.NodeSet.t -> unit =
   fun nodes ->
    if not (LTS.NodeSet.is_empty nodes) then
      let get_shared_guards incoming_edges =
        if List.is_empty incoming_edges then EdgeExp.Set.empty
        else
          let _, head_edge_data, _ = List.hd_exn incoming_edges in
          let acc = DCP.EdgeData.active_guards head_edge_data in
          List.fold (List.tl_exn incoming_edges) ~init:acc
            ~f:(fun shared_guards (_, edge_data, _) ->
              (* Get edge guards that are not decreased on this edge *)
              let guards = DCP.EdgeData.active_guards edge_data in
              EdgeExp.Set.inter guards shared_guards )
      in
      (* Pop one node from set of unprocessed nodes *)
      let node = LTS.NodeSet.min_elt nodes in
      let nodes = LTS.NodeSet.remove node nodes in
      let in_backedges, in_edges =
        List.partition_tf (DCP.pred_e dcp node) ~f:(fun (_, edge_data, _) ->
            DCP.EdgeData.is_backedge edge_data )
      in
      let guards = get_shared_guards in_edges in
      let out_edges = DCP.succ_e dcp node in
      let guards, out_edges =
        if LTS.Node.is_loophead node then (
          assert (Int.equal (List.length out_edges) 2) ;
          let branch_true, branch_false =
            List.partition_tf out_edges ~f:(fun (_, edge_data, _) ->
                DCP.EdgeData.branch_type edge_data )
          in
          let (src, branch_true, dst), branch_false =
            (List.hd_exn branch_true, List.hd_exn branch_false)
          in
          branch_true.guards <- EdgeExp.Set.union guards branch_true.guards ;
          if (not (LTS.Node.equal src dst)) && not (DCP.EdgeData.is_backedge branch_true) then
            propagate_guards (LTS.NodeSet.add dst nodes) ;
          let guards =
            if List.is_empty in_backedges then guards
            else
              let _, backedge, _ = List.hd_exn in_backedges in
              let backedge_guards = DCP.EdgeData.active_guards backedge in
              EdgeExp.Set.inter guards backedge_guards
          in
          (guards, [branch_false]) )
        else (guards, out_edges)
      in
      let nodes =
        if EdgeExp.Set.is_empty guards then nodes
        else
          (* Propagate guards to all outgoing edges and add
             * destination nodes of those edges to the processing queue *)
          List.fold out_edges ~init:nodes ~f:(fun acc (_, (edge_data : DCP.EdgeData.t), dst) ->
              edge_data.guards <- EdgeExp.Set.union guards edge_data.guards ;
              if DCP.EdgeData.is_backedge edge_data then acc else LTS.NodeSet.add dst acc )
      in
      propagate_guards nodes
  in
  propagate_guards guarded_nodes ;
  (* Output Guarded DCP over integers *)
  output_graph (proc_graph_dir ^/ g_dcp_fname) dcp DCP_Dot.output_graph ;
  debug_log "@.@[<v2>==========[Converting Integer DCP to Natural Numbers]==========@," ;
  (* Convert DCP with guards to DCP without guards over natural numbers *)
  let to_natural_numbers : DCP.t -> unit =
   fun dcp ->
    DCP.iter_edges_e
      (fun (_, edge_data, _) ->
        let constraints =
          List.fold edge_data.constraints
            ~f:(fun acc (lhs, dc_rhs) ->
              let convert_dc lhs (rhs_norm, op, rhs_const) =
                match EdgeExp.evaluate_const_exp rhs_norm with
                | Some rhs_norm_value ->
                    let const_value =
                      IntLit.max (EdgeExp.eval_consts op rhs_norm_value rhs_const) IntLit.zero
                    in
                    let dc_rhs = (EdgeExp.zero, Binop.PlusA None, const_value) in
                    dc_rhs
                | None -> (
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
                    match rhs_norm with
                    | EdgeExp.T.Strlen _ ->
                        (rhs_norm, op, rhs_const)
                    | EdgeExp.T.Access access -> (
                      match HilExp.AccessExpression.get_typ access tenv with
                      | Some typ when Typ.is_unsigned_int typ ->
                          (rhs_norm, op, rhs_const)
                      | _ ->
                          (EdgeExp.T.Max (EdgeExp.Set.singleton rhs_norm), op, rhs_const) )
                    | _ ->
                        (EdgeExp.T.Max (EdgeExp.Set.singleton rhs_norm), op, rhs_const) )
              in
              let lhs = EdgeExp.T.Max (EdgeExp.Set.singleton lhs) in
              match dc_rhs with
              | DC.Value rhs_value ->
                  let rhs_value = convert_dc lhs rhs_value in
                  acc @ [(lhs, DC.Value rhs_value)]
              | DC.Pair (lb_rhs, ub_rhs) ->
                  let lb_rhs_value = convert_dc lhs lb_rhs in
                  let ub_rhs_value = convert_dc lhs ub_rhs in
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
              debug_log "[Reset] %a' <= %a %a %a@," EdgeExp.pp lhs_norm EdgeExp.pp rhs_norm Binop.pp
                op IntLit.pp rhs_const ;
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
  let norm_set, formal_variables_mapping =
    if not Config.disable_vfg_renaming then (
      (* Create variable flow graph which is necessary for
       * DCP preprocessing which renames variables and consequently
       * ensures that we get an acyclic reset graph *)
      debug_log "@.@[<v2>==========[Creating Variable Flow Graph]==========@," ;
      let variables =
        EdgeExp.Set.filter_map
          (fun norm ->
            if EdgeExp.is_variable norm formals tenv then
              Some (EdgeExp.T.Max (EdgeExp.Set.singleton norm))
            else None )
          final_norm_set
      in
      let vfg = VFG.create () in
      let used_variables =
        DCP.fold_edges_e
          (fun (src, edge_data, dst) acc ->
            List.fold edge_data.constraints ~init:acc
              ~f:(fun used_variables_acc (lhs_norm, dc_rhs) ->
                let dst_node = (lhs_norm, dst) in
                let vfg_add_node node =
                  if not (VFG.mem_vertex vfg node) then VFG.add_vertex vfg node
                in
                let process_value_rhs used_variables_acc (rhs_norm, _, _) =
                  if EdgeExp.Set.mem lhs_norm variables && EdgeExp.Set.mem rhs_norm variables then (
                    let src_node = (rhs_norm, src) in
                    vfg_add_node dst_node ;
                    vfg_add_node src_node ;
                    VFG.add_edge_e vfg (VFG.E.create src_node VFG.Edge.default dst_node) ;
                    EdgeExp.Set.add rhs_norm (EdgeExp.Set.add lhs_norm used_variables_acc) )
                  else used_variables_acc
                in
                match dc_rhs with
                | DC.Value dc_rhs_value ->
                    process_value_rhs used_variables_acc dc_rhs_value
                | DC.Pair (lb_dc_rhs, ub_dc_rhs) ->
                    (process_value_rhs used_variables_acc lb_dc_rhs |> process_value_rhs) ub_dc_rhs )
            )
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
                    match DCP.EdgeData.get_reset edge_data ssa_var with
                    | Some new_reset -> (
                      match reset_opt with
                      | Some existing_reset ->
                          L.die InternalError
                            "Multiple resets of supposed SSA variable: %a = %a | %a" EdgeExp.pp
                            ssa_var EdgeExp.ValuePair.pp existing_reset EdgeExp.ValuePair.pp
                            new_reset
                      | None ->
                          Some new_reset (* EdgeExp.Map.add norm rhs acc *) )
                    | None ->
                        reset_opt )
                  dcp None
              in
              match reset_opt with
              | Some reset ->
                  EdgeExp.Map.add ssa_var reset mapping
              | None ->
                  L.user_warning "Missing initialization of SSA variable '%a'. Adding '%a = %a'@."
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
      let formal_variables_mapping =
        VFG.Map.fold
          (fun (norm, dcp_node) aux_norm acc ->
            debug_log "(%a, %a)   --->   %a@," LTS.Node.pp dcp_node EdgeExp.pp norm EdgeExp.pp
              aux_norm ;
            if EdgeExp.is_formal_variable norm formals tenv then
              let exit_aux_norm = match dcp_node with LTS.Node.Exit -> true | _ -> false in
              EdgeExp.Map.add aux_norm (norm, exit_aux_norm) acc
            else acc )
          vfg_map EdgeExp.Map.empty
      in
      debug_log "@]@," ;
      (* Apply VFG mapping and rename DCP variables to ensure acyclic reset DAG *)
      DCP.iter_edges_e
        (fun (dcp_src, edge_data, dcp_dst) ->
          let constraints =
            List.fold edge_data.constraints ~init:[] ~f:(fun acc (lhs_norm, dc_rhs) ->
                let lhs_node = (lhs_norm, dcp_dst) in
                let map_value_rhs (rhs_norm, op, rhs_const) =
                  let rhs_node = (rhs_norm, dcp_src) in
                  match (VFG.Map.find_opt lhs_node vfg_map, VFG.Map.find_opt rhs_node vfg_map) with
                  | Some lhs_mapped, Some rhs_mapped ->
                      Some (lhs_mapped, (rhs_mapped, op, rhs_const))
                  | None, Some rhs_mapped ->
                      if EdgeExp.is_variable lhs_norm formals tenv then None
                      else Some (lhs_norm, (rhs_mapped, op, rhs_const))
                  | Some lhs_mapped, None ->
                      if EdgeExp.is_variable rhs_norm formals tenv then None
                      else Some (lhs_mapped, (rhs_norm, op, rhs_const))
                  | None, None ->
                      if EdgeExp.is_return lhs_norm then
                        if EdgeExp.is_variable rhs_norm formals tenv then None
                        else Some (lhs_norm, (rhs_norm, op, rhs_const))
                      else if
                        EdgeExp.is_variable rhs_norm formals tenv
                        || EdgeExp.is_variable lhs_norm formals tenv
                      then None
                      else Some (lhs_norm, (rhs_norm, op, rhs_const))
                in
                (* TODO: This whole part is kinda weird, need to figure out if it would
                 * be better to change the VFG definition to work with DC.value_pair nodes instead? *)
                match dc_rhs with
                | DC.Value value_rhs -> (
                  match map_value_rhs value_rhs with
                  | Some (lhs_norm, mapped_rhs) ->
                      acc @ [(lhs_norm, DC.Value mapped_rhs)]
                  | None ->
                      acc )
                | DC.Pair (lb_rhs, ub_rhs) -> (
                  match (map_value_rhs lb_rhs, map_value_rhs ub_rhs) with
                  | Some (lb_lhs, lb_rhs), Some (ub_lhs, ub_rhs) ->
                      assert (EdgeExp.equal lb_lhs ub_lhs) ;
                      acc @ [(lhs_norm, DC.Pair (lb_rhs, ub_rhs))]
                  | Some (lhs, rhs), None | None, Some (lhs, rhs) ->
                      (* TODO: not sure about this, figure out later *)
                      acc @ [(lhs, DC.Value rhs)]
                  | None, None ->
                      acc ) )
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
                  | EdgeExp.CallPair.P (renamed_lb_call, _), EdgeExp.CallPair.V renamed_ub_call ->
                      EdgeExp.CallPair.P (renamed_lb_call, renamed_ub_call)
                  | EdgeExp.CallPair.V renamed_lb_call, EdgeExp.CallPair.P (_, renamed_ub_call) ->
                      EdgeExp.CallPair.P (renamed_lb_call, renamed_ub_call)
                  | EdgeExp.CallPair.P (renamed_lb_call, _), EdgeExp.CallPair.P (_, renamed_ub_call)
                    ->
                      EdgeExp.CallPair.P (renamed_lb_call, renamed_ub_call) ) )
              edge_data.calls
          in
          edge_data.calls <- calls_renamed_args ;
          edge_data.constraints <- constraints ;
          DCP.EdgeData.set_edge_output_type edge_data DCP )
        dcp ;
      debug_log "@]@," ;
      output_graph (proc_graph_dir ^/ ssa_dcp_fname) dcp DCP_Dot.output_graph ;
      (vfg_norm_set, formal_variables_mapping) )
    else
      ( final_norm_set
      , EdgeExp.Set.fold
          (fun norm map ->
            if EdgeExp.is_formal_variable norm formals tenv then
              EdgeExp.Map.add norm (norm, true) map
            else map )
          final_norm_set EdgeExp.Map.empty )
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
  (* Edges that are not part of any SCC can be executed only once,
   * thus their local bound mapping is 1 and consequently their
   * transition bound TB(t) is 1 *)
  let dcp_edge_set =
    DCP.fold_edges_e (fun edge acc -> DCP.EdgeSet.add edge acc) dcp DCP.EdgeSet.empty
  in
  let dcp_scc_graph = DCP.create () in
  let scc_edges = get_scc_edges dcp dcp_scc_graph in
  let non_scc_edges = DCP.EdgeSet.diff dcp_edge_set scc_edges in
  DCP.EdgeSet.iter (fun (_, edge_data, _) -> edge_data.bound_norm <- Some EdgeExp.one) non_scc_edges ;
  (* Create SCC graph *)
  DCP.EdgeSet.iter
    (fun (src, edge_data, dst) -> DCP.add_edge_e dcp_scc_graph (src, edge_data, dst))
    scc_edges ;
  output_graph (proc_graph_dir ^/ dcp_sccs_fname) dcp_scc_graph DCP_Dot.output_graph ;
  (* For each variable norm construct a E(v) set of edges where it is decreased
     * and assign each edge from this set local bound of v *)
  let norm_edge_sets, processed_edges =
    EdgeExp.Set.fold
      (fun norm (sets, processed_edges) ->
        let get_edge_set norm =
          DCP.EdgeSet.filter
            (fun (_, edge_data, _) ->
              match DC.get_dc norm edge_data.constraints with
              | Some dc when DC.same_norms dc && DC.is_decreasing dc ->
                  edge_data.bound_norm <- Some norm ;
                  true
              | _ ->
                  false )
            scc_edges
        in
        let rec aux norm =
          match norm with
          | EdgeExp.T.Max set when Int.equal (EdgeExp.Set.cardinal set) 1 ->
              aux (EdgeExp.Set.min_elt set)
          | EdgeExp.T.Access access ->
              let access_base = HilExp.AccessExpression.get_base access in
              if AccessPath.BaseSet.mem access_base formals then (sets, processed_edges)
              else
                let bounded_edges = get_edge_set norm in
                let sets = EdgeExp.Map.add norm bounded_edges sets in
                (sets, DCP.EdgeSet.union processed_edges bounded_edges)
          | EdgeExp.T.BinOp _ ->
              (* [TODO] Validate that norm is not purely built over symbolic constants *)
              let bounded_edges = get_edge_set norm in
              let sets = EdgeExp.Map.add norm bounded_edges sets in
              (sets, DCP.EdgeSet.union processed_edges bounded_edges)
          | EdgeExp.T.Const _ ->
              (sets, processed_edges)
          | _ ->
              L.(die InternalError) "[Norm edge sets] Invalid norm expression!"
        in
        aux norm )
      norm_set
      (EdgeExp.Map.empty, DCP.EdgeSet.empty)
  in
  EdgeExp.Map.iter
    (fun norm edge_set ->
      if not (DCP.EdgeSet.is_empty edge_set) then (
        debug_log "@[<v2>E(%a):@," EdgeExp.pp norm ;
        DCP.EdgeSet.iter
          (fun (src, edge_data, dst) ->
            let local_bound = Option.value_exn edge_data.bound_norm in
            debug_log "%a -- %a -- %a@," LTS.Node.pp src EdgeExp.pp local_bound LTS.Node.pp dst )
          edge_set ;
        debug_log "@]@," ) )
    norm_edge_sets ;
  (* Find local bounds for remaining edges that were not processed by
     * the first or second step. Use previously constructed E(v) sets
     * and for each set try to remove edges from the DCP graph. If some
     * unprocessed edges cease to be part of any SCC after the removal,
     * assign variable v as local bound of those edges *)
  let remaining_edges =
    EdgeExp.Map.fold
      (fun norm edges remaining_edges ->
        if DCP.EdgeSet.is_empty remaining_edges then remaining_edges
        else if not (DCP.EdgeSet.is_empty edges) then (
          (* Remove edges of E(v) set from DCP *)
          DCP.EdgeSet.iter (fun edge -> DCP.remove_edge_e dcp edge) edges ;
          (* Calculate SCCs for modified graph *)
          let scc_edges = get_scc_edges dcp dcp in
          let non_scc_edges = DCP.EdgeSet.diff remaining_edges scc_edges in
          DCP.EdgeSet.iter
            (fun (_, edge_data, _) -> edge_data.bound_norm <- Some norm)
            non_scc_edges ;
          (* Restore DCP *)
          DCP.EdgeSet.iter (fun edge -> DCP.add_edge_e dcp edge) edges ;
          DCP.EdgeSet.diff remaining_edges non_scc_edges )
        else remaining_edges )
      norm_edge_sets
      (DCP.EdgeSet.diff scc_edges processed_edges)
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
        (EdgeExp.add total_sum decrement_sum, cache) )
      norms (EdgeExp.zero, cache)
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
          let fold_aux (dcp_edge : DCP.E.t) (args, cache) =
            let bound, cache = transition_bound dcp_edge cache in
            (EdgeExp.Set.add bound args, cache)
          in
          let reset_exp, cache =
            if EdgeExp.is_zero max_exp then (max_exp, cache)
            else
              let args, cache =
                DCP.EdgeSet.fold fold_aux (RG.Chain.transitions chain) (EdgeExp.Set.empty, cache)
              in
              let args =
                if EdgeExp.Set.exists EdgeExp.is_zero args then EdgeExp.Set.singleton EdgeExp.zero
                else args
              in
              let edge_bound =
                if Int.equal (EdgeExp.Set.cardinal args) 1 then EdgeExp.Set.min_elt args
                else EdgeExp.T.Min args
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
            if EdgeExp.is_variable norm formals tenv then
              let cache = get_update_map norm dcp_edge_set cache in
              let norm_updates = EdgeExp.Map.find norm cache.updates in
              let sum_part, cache = sum_function (EdgeExp.Set.singleton norm) cache in
              if LooperSummary.Resets.is_empty norm_updates.resets then (
                match EdgeExp.Map.find_opt norm formal_variables_mapping with
                | Some (original_norm, _) when EdgeExp.is_formal_variable original_norm formals tenv
                  ->
                    (* TODO: Hack around for now. When we reach the end of reset
                       * chain for formal variable we treat it as a symbolic constant.
                       * What should we do in those instances? Formals cannot be variables
                       * and symbolic constants at the same time. We should maybe introduce
                       * shadow variables at the beginning of each function *)
                    let var_bound = EdgeExp.add original_norm sum_part in
                    (var_bound, cache)
                | _ ->
                    L.user_warning
                      "[%a] Variable norm '%a' has no existing reset. Returning Infinity variable \
                       bound.@,"
                      Procname.pp proc_name EdgeExp.pp norm ;
                    (EdgeExp.T.Inf, cache) )
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
                (* Unpack nested max expressions
                 * TODO: unpacking should be done only if certain conditions are met,
                 * should think about it later *)
                let rec flatten_nested_min_max args acc_set =
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
                in
                let min_max_reset_subexp =
                  match EdgeExp.Set.cardinal min_max_reset_args with
                  | 0 ->
                      L.(die InternalError)
                        "[%s] Missing min/max() arguments for [%a]!" label EdgeExp.pp norm
                  | _ ->
                      min_max_constructor min_max_reset_args
                in
                let min_max_reset_subexp =
                  Option.value_map (EdgeExp.evaluate_const_exp min_max_reset_subexp)
                    ~default:min_max_reset_subexp ~f:(fun const ->
                      EdgeExp.T.Const (Const.Cint const) )
                in
                let var_bound = EdgeExp.add min_max_reset_subexp sum_part in
                (var_bound, cache)
            else (norm, cache)
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
    match edge_data.bound with
    | Some bound ->
        debug_log "Retrieved from cache: %a@]@," EdgeExp.pp bound ;
        (bound, cache)
    | None -> (
        (* Infinite recursion guard, might occur with exponential bounds which are not supported *)
        if edge_data.computing_bound then raise Exit ;
        edge_data.computing_bound <- true ;
        match edge_data.bound_norm with
        | Some norm ->
            debug_log "Local bound: %a@," EdgeExp.pp norm ;
            let bound, cache =
              if EdgeExp.is_variable norm formals tenv then (
                (* Get reset chains for local bound *)
                debug_log "@[<v2>[Local bound reset chains]@," ;
                let reset_chains, cache =
                  match EdgeExp.Map.find_opt norm cache.reset_chains with
                  | Some chains ->
                      (chains, cache)
                  | None ->
                      let rg_node = (norm, EdgeExp.is_symbolic_const norm formals tenv) in
                      let chains = RG.get_reset_chains rg_node reset_graph dcp in
                      let cache =
                        {cache with reset_chains= EdgeExp.Map.add norm chains cache.reset_chains}
                      in
                      (chains, cache)
                in
                RG.Chain.Set.iter (fun chain -> debug_log "%a@," RG.Chain.pp chain) reset_chains ;
                debug_log "@]@," ;
                let norms =
                  RG.Chain.Set.fold
                    (fun chain acc ->
                      let norms, _ = RG.Chain.norms chain reset_graph in
                      EdgeExp.Set.union acc norms )
                    reset_chains EdgeExp.Set.empty
                in
                let increment_sum, cache = calculate_increment_sum norms cache in
                let reset_sum, cache = calculate_reset_sum reset_chains cache in
                (EdgeExp.add increment_sum reset_sum, cache) )
              else (
                debug_log "Local bound is a symbolic constant, returning@," ;
                (norm, cache) )
            in
            debug_log "Final TB: %a@]@," EdgeExp.pp bound ;
            edge_data.bound <- Some bound ;
            (bound, cache)
        | None ->
            debug_log "Missing Local Bound@," ;
            (* L.(die InternalError)
               "[Transition Bound] Transition '%a ---> %a' has no local bound!" LTS.Node.pp src
               LTS.Node.pp dst ; *)
            let bound = EdgeExp.T.Inf in
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
            debug_log "@[<v2>[Summary Instantiation] %a | %a@," Procname.pp proc_name Location.pp
              loc ;
            let payload_opt = Location.Map.find_opt loc graph_data.call_summaries in
            let call, cache =
              match payload_opt with
              | Some (LooperSummary.Real payload) ->
                  let call_transitions, new_cache =
                    LooperSummary.instantiate payload args tenv active_prover cache ~variable_bound
                  in
                  let instantiated_call : LooperSummary.call =
                    RealCall {name= proc_name; loc; bounds= call_transitions}
                  in
                  (instantiated_call, new_cache)
              | Some (LooperSummary.Model model_payload) ->
                  let instantiated_call : LooperSummary.call =
                    ModelCall
                      { name= proc_name
                      ; loc
                      ; bound=
                          (* TODO: Shouldn't the bound be value pair here too? Use upper bound for now.
                             Probably will have to change the call summary definitions and usage too. *)
                          EdgeExp.ValuePair.get_ub model_payload.complexity
                      ; monotony_map= AccessExpressionMap.empty }
                  in
                  (instantiated_call, cache)
              | None ->
                  (LooperSummary.RealCall {name= proc_name; loc; bounds= []}, cache_acc)
            in
            debug_log "@]@," ;
            (call :: calls, cache)
        | EdgeExp.CallPair.P (lb_call, ub_call) ->
            L.(die InternalError) "[TODO] Missing implementation" )
      edge_data.calls ([], cache)
  in
  let bounds, cache =
    if not (DCP.EdgeSet.is_empty remaining_edges) then (
      debug_log "@[<v2>Local Bound could not be determined for following edges:@," ;
      DCP.EdgeSet.iter
        (fun (src, _, dst) -> debug_log "%a   --->    %a@," LTS.Node.pp src LTS.Node.pp dst)
        remaining_edges ;
      debug_log "@]@," ) ;
    debug_log "@,====================[Calculating bounds]====================@," ;
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
              {src_node; dst_node; bound; monotony_map; calls= instantiated_calls}
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
      formal_variables_mapping (EdgeExp.Map.empty, cache)
  in
  debug_log "@]@," ;
  let total_bound_exp = LooperSummary.total_bound bounds |> EdgeExp.simplify in
  debug_log "[Final bound] %a@," EdgeExp.pp total_bound_exp ;
  let ret_type = Procdesc.get_ret_type proc_desc in
  let return_bound =
    match ret_type.desc with
    | Tint _ ->
        debug_log "[Return type] %a@," Typ.(pp Pp.text) ret_type ;
        let return_access =
          AccessPath.base_of_pvar (Procdesc.get_ret_var proc_desc) ret_type
          |> HilExp.AccessExpression.base
        in
        let return_norm = EdgeExp.T.Max (EdgeExp.Set.singleton (EdgeExp.T.Access return_access)) in
        let ub_return_bound, cache = variable_bound ~bound_type:BoundType.Upper return_norm cache in
        let lb_return_bound, _ = variable_bound ~bound_type:BoundType.Lower return_norm cache in
        debug_log "[Return bound] [%a, %a]@," EdgeExp.pp lb_return_bound EdgeExp.pp ub_return_bound ;
        Some (lb_return_bound, ub_return_bound)
    | _ ->
        None
  in
  let payload : LooperSummary.t =
    { formal_map= FormalMap.make (Procdesc.get_attributes proc_desc)
    ; bounds
    ; return_bound
    ; return_monotonicity_map= (AccessExpressionMap.empty, AccessExpressionMap.empty)
    ; formal_bounds
    ; formal_monotonicity_map= (AccessExpressionMap.empty, AccessExpressionMap.empty) }
  in
  debug_log "========[Returning payload]========@," ;
  Utils.close_outf log_file ;
  debug_fmt := List.tl_exn !debug_fmt ;
  let summary_graph = LooperSummary.to_graph payload proc_name begin_loc in
  output_graph
    (proc_graph_dir ^/ summary_graph_fname)
    summary_graph LooperSummary.TreeGraph_Dot.output_graph ;
  Some payload
