(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)


open! IStd

module F = Format
module L = Logging
module Domain = LooperDomain

let console_log : ('a, F.formatter, unit) format -> 'a = fun fmt -> F.printf fmt


module DCP_SCC = Graph.Components.Make(Domain.DCP)
module VFG_SCC = Graph.Components.Make(Domain.VFG)


module UnprocessedNormSet = Caml.Set.Make(struct
  type nonrec t = Domain.EdgeExp.t * Domain.AccessSet.t Domain.DCP.EdgeMap.t
  [@@deriving compare]
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

let mk_outfile fname = match Utils.create_outfile fname with
  | None -> L.die InternalError "Could not create '%s'." fname
  | Some outf -> outf


let why3_data = ref Domain.ProverMap.empty


let analyze_procedure (analysis_data : Domain.Summary.t InterproceduralAnalysis.t) =
  let open Domain in

  let proc_desc = analysis_data.proc_desc in
  let begin_loc = Procdesc.get_loc proc_desc in
  let source_file_str = SourceFile.to_string begin_loc.file in
  let source_file_str = (String.rstrip ~drop:(fun x -> not (Char.equal x '.')) source_file_str |> String.drop_suffix) 1 in

  let proc_name = Procdesc.get_proc_name proc_desc in
  let proc_name_str = String.drop_suffix (Procname.to_simplified_string proc_name) 2 in
  let proc_graph_dir = graphs_dir ^/ proc_name_str in

  Utils.create_dir (F.asprintf "%s/%s/" looper_dir source_file_str);

  let debug_log_fname = looper_dir ^/ source_file_str ^/ proc_name_str ^ ".log" in
  let log_file = mk_outfile debug_log_fname in
  debug_fmt := log_file.fmt :: !debug_fmt;
  let debug_log format = F.fprintf log_file.fmt format in


  let prover_map : prover_data ProverMap.t = if ProverMap.is_empty !why3_data then (
    console_log "=========== Initializing Why3 ===========\n";
    let config : Why3.Whyconf.config = Why3.Whyconf.(load_default_config_if_needed (read_config None)) in
    let main : Why3.Whyconf.main = Why3.Whyconf.get_main config in
    let provers : Why3.Whyconf.config_prover Why3.Whyconf.Mprover.t = Why3.Whyconf.get_provers config in
    Why3.Whyconf.Mprover.iter (fun prover _ ->
      console_log "Prover: %s %s\n" prover.prover_name prover.prover_version;
    ) provers;

    let prover_names = [(Z3, "Z3"); (CVC4, "CVC4"); (Vampire, "Vampire")] in

    let env : Why3.Env.env = Why3.Env.create_env (Why3.Whyconf.loadpath main) in
    let real_theory : Why3.Theory.theory = Why3.Env.read_theory env ["real"] "Real" in

    let prover_map = List.fold prover_names ~init:ProverMap.empty ~f:(fun acc (prover_type, name) -> 
      let prover : Why3.Whyconf.config_prover =
        let filter = Why3.Whyconf.parse_filter_prover name in
        let provers = Why3.Whyconf.filter_provers config filter in
        if Why3.Whyconf.Mprover.is_empty provers then (
          L.die InternalError "Prover '%s' is not installed or configured." name
        ) else snd (Why3.Whyconf.Mprover.max_binding provers)
      in

      let driver : Why3.Driver.driver = try Why3.Whyconf.load_driver main env prover.driver []
      with e -> L.die InternalError "Failed to load driver for %s: %a@." name Why3.Exn_printer.exn_printer e
      in

      ProverMap.add prover_type { name; 
        prover_conf = prover; 
        driver = driver; 
        theory = real_theory;
        idents = StringMap.empty;
        vars = StringMap.empty;
      } acc
    )
    in
    why3_data := prover_map;
    !why3_data
  )
  else (
    !why3_data
  )
  in

  let active_prover = ProverMap.find Z3 prover_map in
  active_prover.idents <- StringMap.empty;
  active_prover.vars <- StringMap.empty;


  debug_log "[LOOPER] Source: %s, Procedure '%s' [%a]\n\n" source_file_str proc_name_str Location.pp (Procdesc.get_loc proc_desc);
  debug_log "---------------------------------\n\
            - LTS CONSTRUCTION\n\
            ---------------------------------\n";
  let tenv = Exe_env.get_tenv analysis_data.exe_env proc_name in
  let graph_data = LooperLTS.GraphConstructor.create_lts tenv proc_desc analysis_data in
  
  let lts = DCP.create () in
  DCP.NodeSet.iter (fun node ->
    DCP.add_vertex lts node;
  ) graph_data.nodes;
  DCP.EdgeSet.iter (fun (src, edge_data, dst) ->
    edge_data.edge_type <- LTS;
    DCP.add_edge_e lts (src, edge_data, dst);
  ) graph_data.edges;

  output_graph (proc_graph_dir ^/ lts_fname) lts DCP_Dot.output_graph;

  debug_log "\n---------------------------------\n\
              - PERFORMING ANALYSIS \n\
              ---------------------------------\n";

  (* Draw dot graph, use nodes and edges stored in graph_data *)
  debug_log "[POTENTIAL NORMS]\n";
  EdgeExp.Set.iter (fun norm -> debug_log "  %a\n" EdgeExp.pp norm) graph_data.potential_norms;

  debug_log "[INITIAL NORMS]\n";
  EdgeExp.Set.iter (fun norm -> debug_log "  %a\n" EdgeExp.pp norm) graph_data.norms;

  let dcp = DCP.create () in
  DCP.NodeSet.iter (fun node ->
    DCP.add_vertex dcp node;
  ) graph_data.nodes;


  let rec compute_norm_set unprocessed processed = if UnprocessedNormSet.is_empty unprocessed
  then processed
  else (
    let (norm, norm_history) as unprocessed_norm = UnprocessedNormSet.min_elt unprocessed in
    let unprocessed = UnprocessedNormSet.remove unprocessed_norm unprocessed in
    let processed = EdgeExp.Set.add norm processed in
    debug_log "[DC derivation] Processing norm: %a\n" EdgeExp.pp norm;

    let unprocessed = if EdgeExp.is_variable norm graph_data.formals then (
      DCP.EdgeSet.fold (fun ((_, edge_data, _) as edge) unprocessed ->
        let used_assignments = match DCP.EdgeMap.find_opt edge norm_history with
        | Some set -> set
        | None -> AccessSet.empty
        in

        match DCP.EdgeData.derive_constraint edge_data norm used_assignments graph_data.formals with
        | Some (new_norm, substituted_accesses) -> (
          (* Remember used assignments on this specific edge to avoid infinite recursive
           * loop when generating new norms from assignments such as [i = i * n] *)
          let new_norm_history = DCP.EdgeMap.add edge substituted_accesses norm_history in

          if EdgeExp.Set.mem new_norm processed then unprocessed
          else (
            debug_log "[DC derivation] Adding new norm: %a\n" EdgeExp.pp new_norm;
            UnprocessedNormSet.add (new_norm, new_norm_history) unprocessed
          )
        )
        | None -> unprocessed
        
      ) graph_data.edges unprocessed
    )
    else unprocessed
    in

    compute_norm_set unprocessed processed
  )
  in

  debug_log "\n==========[Deriving constraints]==================\n";
  let unprocessed_norms = EdgeExp.Set.fold (fun norm acc ->
    UnprocessedNormSet.add (norm, DCP.EdgeMap.empty) acc
  ) graph_data.norms UnprocessedNormSet.empty
  in

  let final_norm_set = compute_norm_set unprocessed_norms EdgeExp.Set.empty in

  debug_log "[FINAL NORMS]\n";
  EdgeExp.Set.iter (fun norm -> debug_log "  %a\n" EdgeExp.pp norm) final_norm_set;

  (* All DCs and norms are derived, now derive guards.
   * Use SMT solver to check which norms on which
   * transitions are guaranted to be greater than 0
   * based on conditions that hold on specified transition.
   * For example if transition is guarded by conditions
   * [x >= 0] and [y > x] then we can prove that
   * norm [x + y] > 0 thus it is a guard on this transition *)
  debug_log "\n==========[Deriving guards]=======================\n";



  DCP.EdgeSet.iter (fun (src, edge_data, dst) ->
    debug_log "[Guard Derivation] %a ---> %a\n" DCP.Node.pp src DCP.Node.pp dst;
    edge_data.edge_type <- GuardedDCP;
    DCP.EdgeData.derive_guards_why3 edge_data final_norm_set tenv active_prover;
    
    EdgeExp.Set.iter (fun guard -> debug_log "\t%s > 0\n" (EdgeExp.to_string guard)) edge_data.guards;

    DCP.add_edge_e dcp (src, edge_data, dst);
  ) graph_data.edges;

  let guarded_nodes = DCP.fold_edges_e (fun (_, edge_data, dst) acc ->
    if EdgeExp.Set.is_empty edge_data.guards then acc else DCP.NodeSet.add dst acc
  ) dcp DCP.NodeSet.empty
  in

  (* Propagate guard to all outgoing edges if all incoming edges
    * are guarded by this guard and the guard itself is not decreased
    * on any of those incoming edges (guard is a norm) *)
  debug_log "\n==========[Propagating guards]====================\n";
  let rec propagate_guards : DCP.NodeSet.t -> unit = fun nodes -> (
    if not (DCP.NodeSet.is_empty nodes) then (
      let get_shared_guards incoming_edges = if List.is_empty incoming_edges then EdgeExp.Set.empty
        else (
          let (_, head_edge_data, _) = List.hd_exn incoming_edges in
          let acc = DCP.EdgeData.active_guards head_edge_data in
          List.fold (List.tl_exn incoming_edges) ~init:acc ~f:(fun shared_guards (_, edge_data, _) -> 
            (* Get edge guards that are not decreased on this edge *)
            let guards = DCP.EdgeData.active_guards edge_data in
            EdgeExp.Set.inter guards shared_guards
          )
      )
      in

      (* Pop one node from set of unprocessed nodes *)
      let node = DCP.NodeSet.min_elt nodes in
      let nodes = DCP.NodeSet.remove node nodes in
      
      let in_backedges, in_edges = List.partition_tf (DCP.pred_e dcp node) 
      ~f:(fun (_, edge_data, _) -> DCP.EdgeData.is_backedge edge_data) 
      in
      let guards = get_shared_guards in_edges in
      let out_edges = DCP.succ_e dcp node in

      let guards, out_edges = match node with
      | DCP.Node.Prune (kind, _, _) when is_loop_prune kind -> (
        assert(Int.equal (List.length out_edges) 2);
        let branch_true, branch_false = List.partition_tf out_edges ~f:(fun (_, edge_data, _) -> 
          DCP.EdgeData.branch_type edge_data
        )
        in
        let (src, branch_true, dst), branch_false = List.hd_exn branch_true, List.hd_exn branch_false in

        branch_true.guards <- EdgeExp.Set.union guards branch_true.guards;

        if not (DCP.Node.equal src dst) && not (DCP.EdgeData.is_backedge branch_true) 
        then propagate_guards (DCP.NodeSet.add dst nodes);

        let guards = if List.is_empty in_backedges then guards
        else (
          let _, backedge, _ = List.hd_exn in_backedges in
          let backedge_guards = DCP.EdgeData.active_guards backedge in
          EdgeExp.Set.inter guards backedge_guards
        )
        in
        guards, [branch_false]
      )
      | _ -> guards, out_edges
      in
      let nodes = if EdgeExp.Set.is_empty guards then nodes else (
        (* Propagate guards to all outgoing edges and add
          * destination nodes of those edges to the processing queue *)
        List.fold out_edges ~init:nodes ~f:(fun acc (_, (edge_data : DCP.EdgeData.t), dst) ->
          edge_data.guards <- EdgeExp.Set.union guards edge_data.guards;
          if DCP.EdgeData.is_backedge edge_data then acc else DCP.NodeSet.add dst acc
        )
      )
      in
      propagate_guards nodes
    )
  )
  in
  propagate_guards guarded_nodes;

  (* Output Guarded DCP over integers *)
  output_graph (proc_graph_dir ^/ g_dcp_fname) dcp DCP_Dot.output_graph;

  debug_log "\n==========[Converting Integer DCP to Natural Numbers]==========\n";

  (* Convert DCP with guards to DCP without guards over natural numbers *)
  let to_natural_numbers : DCP.EdgeSet.t -> unit = fun edges -> (
    DCP.EdgeSet.iter (fun (_, edge_data, _) ->
      let constraints = DC.Map.fold (fun lhs (rhs_norm, op, rhs_const) acc ->
        let rhs_const = if IntLit.isnegative rhs_const then (
          (* lhs != rhs hack for now, abstraction algorithm presented in the thesis
            * doesn't add up in the example 'SingleLinkSimple' where they have [i]' <= [n]-1
            * which is indeed right if we want to get valid bound but their abstraction algorithm
            * leads to [i]' <= [n] because there's no guard for n on the transition *)
          if EdgeExp.Set.mem rhs_norm edge_data.guards || not (EdgeExp.equal lhs rhs_norm)
          then IntLit.minus_one 
          else IntLit.zero
        ) else (
          rhs_const
        )
        in
        match EdgeExp.evaluate_const_exp rhs_norm with
        | Some rhs_norm_value -> (
          let const_value = EdgeExp.eval_consts op rhs_norm_value rhs_const in
          let dc_rhs = EdgeExp.zero, Binop.PlusA None, const_value in
          DC.Map.add (EdgeExp.Max [lhs]) dc_rhs acc
        )
        | None -> (
          let dc_rhs = EdgeExp.Max [rhs_norm], op, rhs_const in
          DC.Map.add (EdgeExp.Max [lhs]) dc_rhs acc
        )
      ) edge_data.constraints DC.Map.empty
      in
      edge_data.constraints <- constraints;
      edge_data.edge_type <- DCP;
    ) edges
  )
  in
  to_natural_numbers graph_data.edges;


  output_graph (proc_graph_dir ^/ dcp_fname) dcp DCP_Dot.output_graph;


  let norm_set = if not Config.disable_vfg_renaming then (
    (* Create variable flow graph which is necessary for
     * DCP preprocessing which renames variables and consequently
     * ensures that we get an acyclic reset graph *)
    debug_log "\n==========[Creating Variable Flow Graph]==========\n";
    let variables = EdgeExp.Set.filter_map (fun norm -> 
      if EdgeExp.is_variable norm graph_data.formals
      then Some (EdgeExp.Max [norm])
      else None
    ) final_norm_set
    in

    let vfg = VFG.create () in
    let used_variables = DCP.EdgeSet.fold (fun (src, edge_data, dst) acc -> 
      DC.Map.fold (fun lhs_norm (rhs_norm, _, _) inner_acc ->
        if (EdgeExp.Set.mem lhs_norm variables) && (EdgeExp.Set.mem rhs_norm variables) then (
          let vfg_add_node node = if not (VFG.mem_vertex vfg node) then (
            VFG.add_vertex vfg node
          )
          in
          let dst_node = (lhs_norm, dst) in
          let src_node = (rhs_norm, src) in
          vfg_add_node dst_node; vfg_add_node src_node;
          VFG.add_edge_e vfg (VFG.E.create src_node (VFG.Edge.default) dst_node);
          EdgeExp.Set.add rhs_norm (EdgeExp.Set.add lhs_norm inner_acc)
        )
        else inner_acc
      ) edge_data.constraints acc
    ) graph_data.edges EdgeExp.Set.empty
    in

    let ssa_variables = EdgeExp.Set.diff variables used_variables in
    debug_log "[SSA VARIABLES]\n";
    EdgeExp.Set.iter (fun norm -> debug_log "  %a\n" EdgeExp.pp norm) ssa_variables;

    let ssa_variables_map = EdgeExp.Set.fold (fun norm mapping ->
      if EdgeExp.is_return norm then mapping else (
        DCP.EdgeSet.fold (fun (_, edge_data, _) acc ->
          match DCP.EdgeData.get_reset edge_data norm with
          | Some rhs -> EdgeExp.Map.add norm rhs acc
          | None -> acc
        ) graph_data.edges mapping
      )
    ) ssa_variables EdgeExp.Map.empty
    in
    debug_log "[SSA VARIABLES INITIALIZATION]\n";
    EdgeExp.Map.iter (fun lhs rhs -> debug_log "  %a = %a\n" EdgeExp.pp lhs EdgeExp.pp rhs) ssa_variables_map;

    output_graph (proc_graph_dir ^/ vfg_fname) vfg VFG_Dot.output_graph;


    (* Construct VFG name map, create fresh variable 'v' for each SCC
     * and map each VFG node to this fresh variable. *)
    debug_log "\n==========[Creating VFG mapping]==================\n";
    let vfg_components = VFG_SCC.scc_list vfg in

    let get_vfg_scc_edges vfg vfg_components scc_graph =
      List.fold vfg_components ~init:VFG.EdgeSet.empty ~f:(fun acc component ->
        (* Iterate over all combinations of SCC nodes and check if there
         * are edges between them in both directions *)
        List.fold component ~init:acc ~f:(fun acc node ->
          VFG.add_vertex scc_graph node;

          List.fold component ~init:acc ~f:(fun acc node2 ->
            let edges = VFG.EdgeSet.of_list (VFG.find_all_edges vfg node node2) in
            VFG.EdgeSet.union acc edges
          )
        )
      )
    in

    let vfg_scc_graph = VFG.create () in
    let scc_edges = get_vfg_scc_edges vfg vfg_components vfg_scc_graph in
    VFG.EdgeSet.iter (fun (src, edge_data, dst) ->
      VFG.add_edge_e vfg_scc_graph (src, edge_data, dst);
    ) scc_edges;

    output_graph (proc_graph_dir ^/ vfg_sccs_fname) vfg_scc_graph VFG_Dot.output_graph;


    debug_log "[VFG] SCC count: %d\n" (List.length vfg_components);
    let vfg_map, vfg_norm_set = List.foldi vfg_components ~f:(fun idx (map, norm_set) component ->
      let pvar = Pvar.mk (Mangled.from_string ("var_" ^ string_of_int idx)) proc_name in
      let aux_norm = EdgeExp.Access (AccessPath.of_pvar pvar (Typ.mk (Tint IUInt))) in

      List.fold component ~init:(map, EdgeExp.Set.add aux_norm norm_set) ~f:(fun (map, norm_set) ((exp, _ as node) : VFG.Node.t) ->
        if EdgeExp.is_return exp then VFG.Map.add node exp map, EdgeExp.Set.add exp norm_set
        else VFG.Map.add node aux_norm map, norm_set
      )
    ) ~init:(VFG.Map.empty, EdgeExp.Set.empty)
    in
    debug_log "[VFG Mapping]\n";
    VFG.Map.iter (fun (norm, dcp_node) aux_norm -> 
      debug_log "  (%a, %a) --> %a\n" DCP.Node.pp dcp_node EdgeExp.pp norm EdgeExp.pp aux_norm;
    ) vfg_map;


    (* Apply VFG mapping and rename DCP variables to ensure acyclic reset DAG *)
    DCP.EdgeSet.iter (fun (dcp_src, edge_data, dcp_dst) -> 
      let constraints = DC.Map.fold (fun lhs_norm (rhs_norm, op, rhs_const) map ->
        let lhs_node, rhs_node = (lhs_norm, dcp_dst), (rhs_norm, dcp_src) in
        match VFG.Map.find_opt lhs_node vfg_map, VFG.Map.find_opt rhs_node vfg_map with
        | Some lhs_mapped, Some rhs_mapped -> DC.Map.add lhs_mapped (rhs_mapped, op, rhs_const) map
        | None, Some rhs_mapped -> (
          if EdgeExp.is_variable lhs_norm graph_data.formals then map
          else DC.Map.add lhs_norm (rhs_mapped, op, rhs_const) map
        )
        | Some lhs_mapped, None -> (
          if EdgeExp.is_variable rhs_norm graph_data.formals then map
          else DC.Map.add lhs_mapped (rhs_norm, op, rhs_const) map
        )
        | None, None -> (
          let formals = graph_data.formals in
          if EdgeExp.is_return lhs_norm then (
            if EdgeExp.is_variable rhs_norm formals then map
            else DC.Map.add lhs_norm (rhs_norm, op, rhs_const) map
          ) else (
            if EdgeExp.is_variable rhs_norm formals || EdgeExp.is_variable lhs_norm formals then map
            else DC.Map.add lhs_norm (rhs_norm, op, rhs_const) map
          )
        )
      ) edge_data.constraints DC.Map.empty
      in


      let calls_renamed_args = EdgeExp.Set.map (fun call -> match call with
      | EdgeExp.Call (ret_typ, proc_name, args, loc) -> (
        let renamed_args = List.map args ~f:(fun (arg, typ) ->
          if Typ.is_int typ then (
            let renamed_arg, _ = EdgeExp.map_accesses arg ~f:(fun access _ ->
              let access = EdgeExp.Access access in
              if EdgeExp.is_symbolic_const access graph_data.formals then access, None
              else (
                console_log "%a  ---> %a  | ACCESS: %a\n" DCP.Node.pp dcp_src DCP.Node.pp dcp_dst EdgeExp.pp access;

                (* A little hack-around, need to figure out how to deal with this later *)
                let possible_keys = [
                  (EdgeExp.Max [access], dcp_dst);
                  (EdgeExp.Max [access], dcp_src);
                  (access, dcp_dst);
                  (access, dcp_src)] 
                in
                let rec find_vfg_variable keys = match keys with
                | [] -> (
                  (* This case should occur only for SSA variables which are constant after initialization *)
                  match EdgeExp.Map.find_opt access ssa_variables_map with
                  | Some ssa_init_rhs -> ssa_init_rhs
                  | None -> assert(false)
                )
                | vfg_node :: xs -> (match VFG.Map.find_opt vfg_node vfg_map with
                  | Some vfg_var -> vfg_var
                  | None -> (
                    find_vfg_variable xs
                  )
                )
                in
                find_vfg_variable possible_keys, None
              )
            ) None
            in
            renamed_arg, typ
          )
          else arg, typ
        )
        in
        EdgeExp.Call (ret_typ, proc_name, renamed_args, loc)
      )
      | _ -> assert(false)
      ) edge_data.calls
      in

      edge_data.calls <- calls_renamed_args;
      edge_data.constraints <- constraints;
      edge_data.edge_type <- DCP;
    ) graph_data.edges;

    output_graph (proc_graph_dir ^/ ssa_dcp_fname) dcp DCP_Dot.output_graph;
    vfg_norm_set
  ) 
  else final_norm_set
  in


  (* Reset graph construction, must be performed after VFG renaming phase *)
  debug_log "\n==========[Creating Reset Graph]==================\n";
  let reset_graph = RG.create () in
  DCP.EdgeSet.iter (fun (src, edge_data, dst) -> 
    (* Search for resets *)
    DC.Map.iter (fun lhs_norm (rhs_norm, op, rhs_const) ->
      debug_log "Checking %a == %a ?\n" EdgeExp.pp lhs_norm EdgeExp.pp rhs_norm;
      if not (EdgeExp.equal lhs_norm rhs_norm) then (
        debug_log "[Reset] %a != %a, const: %s %a\n" EdgeExp.pp lhs_norm EdgeExp.pp rhs_norm (Binop.str Pp.text op) IntLit.pp rhs_const;
        RG.add_vertex reset_graph lhs_norm;
        RG.add_vertex reset_graph rhs_norm;
        let edge = RG.E.create rhs_norm (RG.Edge.make (src, edge_data, dst) rhs_const) lhs_norm in
        RG.add_edge_e reset_graph edge;
      )
    ) edge_data.constraints;
  ) graph_data.edges;


  output_graph (proc_graph_dir ^/ rg_fname) reset_graph RG_Dot.output_graph;

  (* Suboptimal way to find all SCC edges, the ocamlgraph library for some
   * reason does not have a function that returns edges of SCCs.  *)
  let get_scc_edges dcp scc_graph =
    let components = DCP_SCC.scc_list dcp in
    
    List.fold components ~init:DCP.EdgeSet.empty ~f:(fun acc component ->
      (* Iterate over all combinations of SCC nodes and check if there
      * are edges between them in both directions *)
      List.fold component ~init:acc ~f:(fun acc node ->
        DCP.add_vertex scc_graph node;

        List.fold component ~init:acc ~f:(fun acc node2 ->
          let edges = DCP.EdgeSet.of_list (DCP.find_all_edges dcp node node2) in
          DCP.EdgeSet.union acc edges
        )
      )
    )
  in

  debug_log "\n==========[Determining Local Bounds]==============\n";
  (* Edges that are not part of any SCC can be executed only once,
   * thus their local bound mapping is 1 and consequently their
   * transition bound TB(t) is 1 *)
  let dcp_scc_graph = DCP.create () in
  let scc_edges = get_scc_edges dcp dcp_scc_graph in
  let non_scc_edges = DCP.EdgeSet.diff graph_data.edges scc_edges in
  DCP.EdgeSet.iter (fun (_, edge_data, _) ->
    edge_data.bound_norm <- Some EdgeExp.one;
  ) non_scc_edges;

  (* Create SCC graph *)
  DCP.EdgeSet.iter (fun (src, edge_data, dst) ->
    edge_data.edge_type <- LTS;
    DCP.add_edge_e dcp_scc_graph (src, edge_data, dst);
  ) scc_edges;


  output_graph (proc_graph_dir ^/ dcp_sccs_fname) dcp_scc_graph DCP_Dot.output_graph;


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
    | EdgeExp.Max [EdgeExp.Access ((var, _), _)]
    | EdgeExp.Access ((var, _), _) -> (
      let base_pvar = Option.value_exn (Var.get_pvar var) in
      if Pvar.Set.mem base_pvar graph_data.formals then sets, processed_edges
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
  ) norm_set (EdgeExp.Map.empty, DCP.EdgeSet.empty)
  in


  EdgeExp.Map.iter (fun norm edge_set ->
    debug_log "E(%a):\n" EdgeExp.pp norm;
    DCP.EdgeSet.iter (fun (src, edge_data, dst) ->
      let local_bound = Option.value_exn edge_data.bound_norm in
      debug_log "  %a -- %a -- %a\n" DCP.Node.pp src EdgeExp.pp local_bound DCP.Node.pp dst;
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
        let scc_edges = get_scc_edges dcp dcp in
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
    if EdgeExp.Map.mem norm cache.updates then cache
    else (
      (* Create missing increments and resets sets for this variable norm *)
      let updates = DCP.EdgeSet.fold (fun ((_, edge_data, _) as edge) updates ->
        match DC.Map.get_dc norm edge_data.constraints with
        | Some ((_, (rhs_norm, _, rhs_const)) as dc) -> (
          (* Variable norm is used on this edge *)
          if DC.is_reset dc then (
            {updates with resets = Resets.add (edge, rhs_norm, rhs_const) updates.resets}
          ) else if DC.is_decreasing dc then (
            {updates with decrements = Decrements.add (edge, rhs_const) updates.decrements}
          ) else if not (IntLit.iszero rhs_const) then (
            {updates with increments = Increments.add (edge, rhs_const) updates.increments}
          )
          else updates
        )
        | None -> updates
      ) edges empty_updates
      in
      { cache with updates = EdgeExp.Map.add norm updates cache.updates }
    )
  in

  let rec calculate_increment_sum norms cache = EdgeExp.Set.fold (fun norm (total_sum, cache) -> 
    (* Calculates increment sum based on increments of variable norm:
      * SUM(TB(t) * const) for all edges where norm is incremented, 0 if nowhere *)
    let cache = get_update_map norm graph_data.edges cache in
    let norm_updates = EdgeExp.Map.find norm cache.updates in
    let increment_sum, cache = Increments.fold (fun (edge, const) (increment_sum, cache) ->
      let bound, cache = transition_bound edge cache in
      let const = EdgeExp.mult bound (EdgeExp.Const (Const.Cint const)) in
      (EdgeExp.add increment_sum const), cache
    ) norm_updates.increments (EdgeExp.zero, cache)
    in
    (EdgeExp.add total_sum increment_sum), cache
  ) norms (EdgeExp.zero, cache)


  and calculate_decrement_sum norms cache = EdgeExp.Set.fold (fun norm (total_sum, cache) -> 
    (* Calculates decrement sum based on decrements of variable norm:
      * SUM(TB(t) * const) for all edges where norm is decremented, 0 if nowhere *)
    let cache = get_update_map norm graph_data.edges cache in
    let norm_updates = EdgeExp.Map.find norm cache.updates in
    let decrement_sum, cache = Decrements.fold (fun (edge, const) (decrement_sum, cache) ->
      let bound, cache = transition_bound edge cache in
      let const = EdgeExp.mult bound (EdgeExp.Const (Const.Cint const)) in
      (EdgeExp.add decrement_sum const), cache
    ) norm_updates.decrements (EdgeExp.zero, cache)
    in
    (EdgeExp.add total_sum decrement_sum), cache
  ) norms (EdgeExp.zero, cache)


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
      (* max(max(x, 0) - 1, 0) --> max(x - 1, 0) *)
      | EdgeExp.Max args -> EdgeExp.sub (List.hd_exn args) const_bound
      | _ -> EdgeExp.sub var_bound const_bound
      in
      EdgeExp.Max [binop_bound], cache
    ) else if IntLit.iszero chain_value then (
      var_bound, cache
    ) else (
      (* const > 0 => result must be positive, max function is useless *)
      let const_bound = EdgeExp.Const (Const.Cint chain_value) in
      let binop_bound = EdgeExp.add var_bound const_bound in
      binop_bound, cache
    )
    in
    (* Creates a list of arguments for min(args) function. Arguments are
      * transition bounds of each transition of a reset chain. Zero TB stops
      * the fold as we cannot get smaller value. *)
    let fold_aux (args, cache) (dcp_edge : DCP.E.t) =
      let open Base.Continue_or_stop in
      let bound, cache = transition_bound dcp_edge cache in
      if EdgeExp.is_zero bound then Stop ([EdgeExp.zero], cache) 
      else (
        match List.hd args with
        | Some arg when EdgeExp.is_one arg -> Continue (args, cache)
        | _ -> (
          if EdgeExp.is_one bound then Continue ([bound], cache) 
          else Continue (bound :: args, cache)
        )
      )
    in
    let reset_exp, cache = if EdgeExp.is_zero max_exp then (
        max_exp, cache
      ) else (
        let chain_transitions = DCP.EdgeSet.elements (RG.Chain.transitions chain) in
        let args, cache = List.fold_until chain_transitions ~init:([], cache) ~f:fold_aux ~finish:(fun acc -> acc) in
        let args = List.dedup_and_sort ~compare:EdgeExp.compare args in
        let edge_bound = if Int.equal (List.length args) 1 then List.hd_exn args else EdgeExp.Min (args) in
        if EdgeExp.is_one edge_bound then max_exp, cache
        else EdgeExp.mult edge_bound max_exp, cache
      )
    in
    let _, chain_norms = RG.Chain.norms chain reset_graph in
    let increment_sum, cache = calculate_increment_sum chain_norms cache in
    (EdgeExp.add (EdgeExp.add sum reset_exp) increment_sum), cache
  ) chains (EdgeExp.zero, cache)


  and variable_bound norm cache =
    let bound, cache = match EdgeExp.Map.find_opt norm cache.variable_bounds with
    | Some bound -> bound, cache
    | None -> (
      if EdgeExp.is_variable norm graph_data.formals then (
        let var_bound, cache = match norm with
        | EdgeExp.Max args when List.length args > 1 -> (
          (* Variable bound for a max(...) expression. Calculate VB for each variable argument *)
          let cache, args = List.fold args ~init:(cache, [])  ~f:(fun (cache, args_acc) arg ->
            match arg with
            | EdgeExp.Access _ -> (
              let arg, cache = variable_bound arg cache in
              cache, arg :: args_acc
            )
            | EdgeExp.Max nested_args -> (
              (* Nested max expression, unpack arguments *)
              debug_log "Nested max arg: %a\n" EdgeExp.pp arg;
              let args = List.filter nested_args ~f:(fun x -> not (List.mem args_acc x ~equal:EdgeExp.equal)) in
              cache, args @ args_acc
            )
            | _ -> (cache, arg :: args_acc)
          ) in
          EdgeExp.Max args, cache
        )
        | _ -> (
          debug_log "   [VB(%a)]\n" EdgeExp.pp norm;
          let cache = get_update_map norm graph_data.edges cache in
          let norm_updates = EdgeExp.Map.find norm cache.updates in
          let increment_sum, cache = calculate_increment_sum (EdgeExp.Set.singleton norm) cache in

          assert(not (Resets.is_empty norm_updates.resets));
          let max_args, cache = Resets.fold (fun (_, norm, const) (args, cache) ->
            let var_bound, cache = variable_bound norm cache in
            let max_arg = if IntLit.isnegative const then (
              let const = EdgeExp.Const (Const.Cint (IntLit.neg const)) in
              [EdgeExp.sub var_bound const]
            ) else if IntLit.iszero const then (
              [var_bound]
            ) else (
              let const = EdgeExp.Const (Const.Cint const) in
              [EdgeExp.add var_bound const]
            )
            in
            args @ max_arg, cache
          ) norm_updates.resets ([], cache)
          in
          debug_log "   [VB(%a)] Max args: " EdgeExp.pp norm;
          List.iter max_args ~f:(fun x -> debug_log "%a " EdgeExp.pp x);
          debug_log "\n";

          (* Deduplicate and unpack nested max expressions
           * TODO: unpacking should be done only if certain conditions are met, should think about it later *)
          let rec flatten_nested_max args acc_set = List.fold args ~init:acc_set ~f:(fun acc arg ->
            match arg with
            | EdgeExp.Max nested_args -> flatten_nested_max nested_args acc
            | _ -> EdgeExp.Set.add arg acc
          )
          in

          let flattened_args = flatten_nested_max max_args EdgeExp.Set.empty |> EdgeExp.Set.elements in
          let max_subexp, cache = match List.length flattened_args with
          | 0 -> L.(die InternalError)"[VB] Missing max() arguments for [%a]!" EdgeExp.pp norm
          | 1 -> (
            let arg = List.hd_exn flattened_args in
            let is_always_positive, cache = match EdgeExp.Map.find_opt arg cache.positivity with
            | Some value -> value, cache
            | None -> (
              let value = EdgeExp.always_positive_why3 arg tenv active_prover in
              value, { cache with positivity = EdgeExp.Map.add arg value cache.positivity }
            )
            in
            (if is_always_positive then arg else EdgeExp.Max [arg]), cache
          )
          | _ -> EdgeExp.Max flattened_args, cache
          in
          EdgeExp.add max_subexp increment_sum, cache
        )
        in

        var_bound, {cache with variable_bounds = EdgeExp.Map.add norm var_bound cache.variable_bounds}
      ) 
      else norm, {cache with variable_bounds = EdgeExp.Map.add norm norm cache.variable_bounds}
    )
    in
    debug_log "   [VB(%a)] %a\n" EdgeExp.pp norm EdgeExp.pp bound;
    bound, cache


  and variable_lower_bound norm cache =
    let bound, cache = match EdgeExp.Map.find_opt norm cache.lower_bounds with
    | Some bound -> bound, cache
    | None -> (
      if EdgeExp.is_variable norm graph_data.formals then (
        let var_bound, cache = match norm with
        | EdgeExp.Max args -> (
          (* Variable bound for a max(...) expression. Calculate VB for each variable argument *)
          let cache, args = List.fold args ~init:(cache, [])  ~f:(fun (cache, args_acc) arg ->
            match arg with
            | EdgeExp.Access _ -> (
              let arg, cache = variable_lower_bound arg cache in
              cache, arg :: args_acc
            )
            | EdgeExp.Max nested_args -> (
              (* Nested max expression, unpack arguments *)
              debug_log "Nested max arg: %a\n" EdgeExp.pp arg;
              let args = List.filter nested_args ~f:(fun x -> not (List.mem args_acc x ~equal:EdgeExp.equal)) in
              cache, args @ args_acc
            )
            | _ -> (cache, arg :: args_acc)
          ) in
          EdgeExp.Max args, cache
        )
        | _ -> (
          debug_log "   [LB(%a)]\n" EdgeExp.pp norm;
          let cache = get_update_map norm graph_data.edges cache in
          let norm_updates = EdgeExp.Map.find norm cache.updates in
          let decrement_sum, cache = calculate_decrement_sum (EdgeExp.Set.singleton norm) cache in

          assert(not (Resets.is_empty norm_updates.resets));
          let min_args, cache = Resets.fold (fun (_, norm, const) (args, cache) ->
            let var_bound, cache = variable_lower_bound norm cache in
            let min_arg = if IntLit.isnegative const 
            then EdgeExp.sub var_bound (EdgeExp.Const (Const.Cint (IntLit.neg const)))
            else EdgeExp.add var_bound (EdgeExp.Const (Const.Cint const))
            in
            min_arg :: args, cache
          ) norm_updates.resets ([], cache)
          in

          let rec flatten_nested_min args acc_set = List.fold args ~init:acc_set ~f:(fun acc arg ->
            match arg with
            | EdgeExp.Min nested_args -> flatten_nested_min nested_args acc
            | _ -> EdgeExp.Set.add arg acc
          )
          in

          let flattened_args = flatten_nested_min min_args EdgeExp.Set.empty |> EdgeExp.Set.elements in
          let min_subexp, cache = match List.length flattened_args with
          | 0 -> L.(die InternalError)"[LB] Missing min() arguments for [%a]!" EdgeExp.pp norm
          | 1 -> List.hd_exn flattened_args, cache
          | _ -> EdgeExp.Min flattened_args, cache
          in
          EdgeExp.add min_subexp decrement_sum, cache
        )
        in

        var_bound, {cache with lower_bounds = EdgeExp.Map.add norm var_bound cache.lower_bounds}
      ) 
      else norm, {cache with lower_bounds = EdgeExp.Map.add norm norm cache.lower_bounds}
    )
    in
    debug_log "   [LB(%a)] %a\n" EdgeExp.pp norm EdgeExp.pp bound;
    bound, cache


  and transition_bound (src, (edge_data : DCP.EdgeData.t), dst) cache =
    (* For variable norms: TB(t) = IncrementSum + ResetSum 
     * For constant norms: TB(t) = constant *)
    debug_log "[TB] %a -- %a\n" DCP.Node.pp src DCP.Node.pp dst;
    match edge_data.bound with
    | Some bound -> bound, cache
    | None -> (
      (* Infinite recursion guard, might occur with exponential bounds which are not supported *)
      if edge_data.computing_bound then raise Exit;
      edge_data.computing_bound <- true;

      match edge_data.bound_norm with
      | Some norm -> (
        debug_log "   [Local bound] %a\n" EdgeExp.pp norm;
        let bound, cache = match norm with
        | EdgeExp.Const (Const.Cint _) -> (
          (* Non-loop edge, can be executed only once, const is always 1 *)
          norm, cache
        )
        | _ -> if EdgeExp.is_variable norm graph_data.formals then (
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
              debug_log "   [Reset Chain] %a\n" RG.Chain.pp chain;
            ) reset_chains;

            let norms = RG.Chain.Set.fold (fun chain acc ->
              let norms, _ = RG.Chain.norms chain reset_graph in
              EdgeExp.Set.union acc norms
            ) reset_chains EdgeExp.Set.empty
            in
            let increment_sum, cache = calculate_increment_sum norms cache in
            let reset_sum, cache = calculate_reset_sum reset_chains cache in
            (EdgeExp.add increment_sum reset_sum), cache
          )
          else norm, cache
        in
        
        debug_log "[Edge bound (%a)] %a\n" EdgeExp.pp norm EdgeExp.pp bound;
        edge_data.bound <- Some bound;
        bound, cache
      )
      | None -> L.(die InternalError)"[Bound] edge has no bound norm!"
    )
  in


  (* Sum together the cost of all functions called on this transition *)
  let instantiate_function_calls (edge_data : DCP.EdgeData.t) cache =
    EdgeExp.Set.fold (fun call_exp (calls, cache_acc) -> match call_exp with
      | EdgeExp.Call (_, proc_name, args, loc) -> (
        let payload_opt = Location.Map.find_opt loc graph_data.call_summaries in
        match payload_opt with
        | Some payload -> (
          debug_log "[Summary Instantiation] %a | %a\n" Procname.pp proc_name Location.pp loc;

          let call_transitions, new_cache = Summary.instantiate payload args tenv active_prover cache
            ~upper_bound:variable_bound ~lower_bound:variable_lower_bound
          in

          let instantiated_call : Summary.call = {
            name = proc_name;
            loc;
            bounds = call_transitions
          }
          in
          instantiated_call :: calls, new_cache
        )
        | None -> (
          let missing_payload_call : Summary.call = {
            name = proc_name;
            loc;
            bounds = []
          }
          in
          missing_payload_call :: calls, cache_acc
        )
      )
      | _ -> assert(false)
    ) edge_data.calls ([], cache)
  in


  let bounds, cache = if not (DCP.EdgeSet.is_empty remaining_edges) then (
    let culprits = List.map (DCP.EdgeSet.elements remaining_edges) ~f:(fun (src, _, dst) ->
      F.asprintf "%a ---> %a" DCP.Node.pp src DCP.Node.pp dst
    ) |> String.concat ~sep:"\n"
    in
    L.internal_error "[%a] Local bound could not be \
    determined for following edges:\n%s\n\
    Returning [Infinity]\n" Procname.pp proc_name culprits;
    [], empty_cache
  ) else (
    debug_log "\n==========[Calculating bounds]====================\n";

    (* Calculate bound for all back-edges and sum them to get the total bound *)
    try
      debug_log "[Local bounds]\n";
      let edge_set, cache = DCP.EdgeSet.fold (fun edge (edge_set, cache) ->
        let src, edge_data, dst = edge in
        let local_bound = Option.value_exn edge_data.bound_norm in
        debug_log "  %a ---> %a: %a\n" DCP.Node.pp src DCP.Node.pp dst EdgeExp.pp local_bound;

        if DCP.EdgeData.is_backedge edge_data then (
          let _, cache = transition_bound edge cache in
          DCP.EdgeSet.add edge edge_set, cache
        )
        else if not (EdgeExp.Set.is_empty edge_data.calls) then (
          DCP.EdgeSet.add edge edge_set, cache
        )
        else edge_set, cache
      ) graph_data.edges (DCP.EdgeSet.empty, empty_cache)
      in

      (* Execution cost must be computed after transitions bounds
       * to avoid computation cycles *)
      let bounds, cache = DCP.EdgeSet.fold (fun ((src_node, edge_data, dst_node) as edge) (bounds, cache) ->
        let instantiated_calls, cache = instantiate_function_calls edge_data cache in
        let bound, cache = transition_bound edge cache in

        let monotony_map = if EdgeExp.is_const bound 
        then AccessPathMap.empty
        else EdgeExp.determine_monotony_why3 bound tenv active_prover
        in

        let transition : Summary.transition = {
          src_node; dst_node;
          bound;
          monotony_map;
          calls = instantiated_calls
        }
        in
        transition :: bounds, cache
      ) edge_set ([], cache)
      in

      bounds, cache
    with Exit -> (
      [], empty_cache
    )
  )
  in

  let total_bound_exp = Summary.total_bound bounds in
  debug_log "\n[Final bound] %a\n" EdgeExp.pp total_bound_exp;

  let ret_type = Procdesc.get_ret_type proc_desc in
  let return_bound = match ret_type.desc with
  | Tint _ -> (
    debug_log "[Return type] %a\n" Typ.(pp Pp.text) ret_type;
    let return_access = AccessPath.of_pvar (Procdesc.get_ret_var proc_desc) ret_type in
    let return_norm = EdgeExp.Max [EdgeExp.Access return_access] in
    let return_bound, _ = variable_bound return_norm cache in
    debug_log "[Return bound] %a\n" EdgeExp.pp return_bound;
    Some return_bound
  )
  | _ -> None
  in

  let payload : Domain.Summary.t = {
    formal_map = FormalMap.make proc_desc;
    bounds = bounds;
    return_bound = return_bound;
  }
  in

  debug_log "========[Returning payload]========\n";
  Utils.close_outf log_file;
  debug_fmt := List.tl_exn !debug_fmt;

  let summary_graph = Summary.to_graph payload proc_name begin_loc in
  output_graph (proc_graph_dir ^/ summary_graph_fname) summary_graph Summary.TreeGraph_Dot.output_graph;
  Some payload
