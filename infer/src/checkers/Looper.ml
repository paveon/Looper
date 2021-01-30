open! IStd

module F = Format
module L = Logging
module Domain = LooperDomain
module Analyzer = LooperLTS

let console_log : ('a, F.formatter, unit) format -> 'a = fun fmt -> F.printf fmt


module CFG = ProcCfg.NormalOneInstrPerNode
(* module CFG = ProcCfg.Normal *)

(* module Analyzer = AbstractInterpreter.Make (CFG) (TransferFunctions) *)
(* module Analyzer = AbstractInterpreter.MakeWTO (TransferFunctions (CFG)) *)
module DCP_SCC = Graph.Components.Make(Domain.DCP)
module VFG_SCC = Graph.Components.Make(Domain.VFG)


let lts_fname = "LTS.dot"
let dcp_fname = "DCP.dot"
let g_dcp_fname = "DCP_guarded.dot"
let vfg_fname = "VFG.dot"
let rg_fname = "RG.dot"
let dcp_sccs_fname = "DCP_SCCs.dot"
let ssa_dcp_fname = "SSA_DCP.dot"

let looper_dir = Config.(results_dir ^/ "../Looper/")
let graphs_dir = looper_dir ^/ "Graphs/"

let mk_outfile fname = match Utils.create_outfile fname with
  | None -> L.die InternalError "Could not create '%s'." fname
  | Some outf -> outf

let checker {Callbacks.exe_env; summary; } : Summary.t =
  let open Domain in
  let proc_desc = Summary.get_proc_desc summary in
  let begin_loc = Procdesc.get_loc proc_desc in
  let source_file_str = SourceFile.to_string begin_loc.file in
  let source_file_str = (String.rstrip ~drop:(fun x -> not (Char.equal x '.')) source_file_str |> String.drop_suffix) 1 in

  let proc_name = Procdesc.get_proc_name proc_desc in
  let proc_name_str = String.drop_suffix (Procname.to_simplified_string proc_name) 2 in
  let proc_graph_dir = graphs_dir ^/ proc_name_str in
  (* (proc_graph_dir ^/ name) *)

  Utils.create_dir (F.asprintf "%s/%s/" looper_dir source_file_str);

  let debug_log_fname = looper_dir ^/ source_file_str ^/ proc_name_str ^ ".log" in
  let log_file = mk_outfile debug_log_fname in
  let debug_log format = F.fprintf log_file.fmt format in

  debug_log "[LOOPER] Source: %s, Procedure '%s' [%a]\n\n" source_file_str proc_name_str Location.pp (Procdesc.get_loc proc_desc);

  debug_log "---------------------------------\n\
            - LTS CONSTRUCTION\n\
            ---------------------------------\n";
  
  let tenv = Exe_env.get_tenv exe_env proc_name in
  let graph_data = Analyzer.GraphConstructor.create_lts tenv proc_desc summary log_file in
  
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
  (* log "%a" pp post; *)

  (* Draw dot graph, use nodes and edges stored in graph_data *)
  debug_log "[POTENTIAL NORMS]\n";
  EdgeExp.Set.iter (fun norm -> debug_log "  %a\n" EdgeExp.pp norm) graph_data.potential_norms;

  debug_log "[INITIAL NORMS]\n";
  EdgeExp.Set.iter (fun norm -> debug_log "  %a\n" EdgeExp.pp norm) graph_data.norms;

  let dcp = DCP.create () in
  DCP.NodeSet.iter (fun node ->
    DCP.add_vertex dcp node;
  ) graph_data.nodes;

  
  (* Derive difference constraints for each edge for each norm until we
   * process all norms. Additional norms are generated during this process *)
  let rec compute_norm_set unprocessed processed = if EdgeExp.Set.is_empty unprocessed
  then processed
  else (
    let norm = EdgeExp.Set.min_elt unprocessed in
    let unprocessed = EdgeExp.Set.remove norm unprocessed in
    let processed = EdgeExp.Set.add norm processed in
    debug_log "[DC derivation] Processing norm: %a\n" EdgeExp.pp norm;

    let unprocessed = if EdgeExp.is_const norm then unprocessed
    else DCP.EdgeSet.fold (fun ((src, _, dst) as edge) unprocessed ->
      let all_norms = EdgeExp.Set.union processed unprocessed in
      (* let derived_norms = DCP.EdgeData.derive_constraint edge norm all_norms graph_data.formals in *)
      let derived_norms = if EdgeExp.is_variable norm graph_data.formals then (
        console_log "%a ---> %a, deriving for: %a\n" DCP.Node.pp src DCP.Node.pp dst EdgeExp.pp norm;
        DCP.EdgeData.derive_constraint edge norm all_norms graph_data.formals
      )
      else EdgeExp.Set.empty
      in
      
      (* Remove already processed norms and add new norms to unprocessed set *)
      let new_norms = EdgeExp.Set.diff derived_norms processed in
      EdgeExp.Set.union new_norms unprocessed
    ) graph_data.edges unprocessed
    in
    compute_norm_set unprocessed processed
  )
  in

  debug_log "\n==========[Deriving constraints]==================\n";
  let final_norm_set = compute_norm_set graph_data.norms EdgeExp.Set.empty in

  debug_log "[FINAL NORMS]\n";
  EdgeExp.Set.iter (fun norm -> debug_log "  %a\n" EdgeExp.pp norm) final_norm_set;

  (* All DCs and norms are derived, now derive guards.
    * Use Z3 SMT solver to check which norms on which
    * transitions are guaranted to be greater than 0
    * based on conditions that hold on specified transition.
    * For example if transition is guarded by conditions
    * [x >= 0] and [y > x] then we can prove that
    * norm [x + y] > 0 thus it is a guard on this transition *)
  debug_log "\n==========[Deriving guards]=======================\n";
  let cfg = [("model", "true"); ("proof", "false"); ("auto_config", "true"); ("timeout", "5000")] in
  let z3_ctx = (Z3.mk_context cfg) in
  let solver = (Z3.Solver.mk_solver z3_ctx None) in
  DCP.EdgeSet.iter (fun (src, edge_data, dst) ->
    debug_log "[Guard Derivation] %a ---> %a\n" DCP.Node.pp src DCP.Node.pp dst;
    edge_data.edge_type <- GuardedDCP;
    DCP.EdgeData.derive_guards edge_data final_norm_set tenv z3_ctx solver;
    List.iter (EdgeExp.Set.elements edge_data.guards) ~f:(fun guard -> 
      debug_log "\t%s > 0\n" (EdgeExp.to_string guard);
    );
    DCP.add_edge_e dcp (src, edge_data, dst);
  ) graph_data.edges;

  let guarded_nodes = DCP.fold_edges_e (fun (_, edge_data, dst) acc ->
    if EdgeExp.Set.is_empty edge_data.guards then acc else DCP.NodeSet.add dst acc
  ) dcp DCP.NodeSet.empty
  in

  (* let test_expr = EdgeExp.BinOp (Binop.MinusA None, EdgeExp.of_int 5, EdgeExp.of_int 6) in
  let test = EdgeExp.always_positive test_expr z3_ctx solver in
  console_log "'%a' always positive: %B\n" EdgeExp.pp test_expr test; *)

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

      (* let rec get_shared_guards : EdgeExp.Set.t -> DCP.edge list -> EdgeExp.Set.t =
      fun guards edges -> match edges with
      | (_, edge_data, _) :: edges -> (
        if DCP.EdgeData.is_backedge edge_data then (
          get_shared_guards guards edges
        ) else (
          (* Get edge guards that are not decreased on this edge *)
          let guards = DCP.EdgeData.active_guards edge_data in
          EdgeExp.Set.inter guards (get_shared_guards guards edges)
        )
      )
      | [] -> guards
      in *)

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

  (* Convert DCP with guards to DCP without guards over natural numbers *)
  let to_natural_numbers : DCP.EdgeSet.t -> unit = fun edges -> (
    DCP.EdgeSet.iter (fun (_, edge_data, _) ->
      let constraints = DC.Map.fold (fun lhs (rhs_norm, op, rhs_const) acc ->
        let dc_rhs = if IntLit.isnegative rhs_const then (
          (* lhs != rhs hack for now, abstraction algorithm presented in the thesis
            * doesn't add up in the example 'SingleLinkSimple' where they have [i]' <= [n]-1
            * which is indeed right if we want to get valid bound but their abstraction algorithm
            * leads to [i]' <= [n] because there's no guard for n on the transition *)
          let rhs_const = if EdgeExp.Set.mem rhs_norm edge_data.guards || not (EdgeExp.equal lhs rhs_norm) then IntLit.minus_one 
          else IntLit.zero in
          rhs_norm, op, rhs_const
        ) else (
          rhs_norm, op, rhs_const
        )
        in
        DC.Map.add lhs dc_rhs acc
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
    let variables = EdgeExp.Set.filter (fun norm -> 
      EdgeExp.is_variable norm graph_data.formals
    ) final_norm_set
    in

    let vfg = VFG.create () in
    let used_variables = DCP.EdgeSet.fold (fun (src, edge_data, dst) acc -> 
      DC.Map.fold (fun lhs_norm (rhs_norm, _, _) inner_acc ->
        (* not (EdgeExp.equal lhs_norm rhs_norm && IntLit.iszero c) && *)
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
    debug_log "[VFG] SCC count: %d\n" (List.length vfg_components);
    let vfg_map, vfg_norm_set = List.foldi vfg_components ~init:(VFG.Map.empty, EdgeExp.Set.empty) ~f:(fun idx (map, norm_set) component ->
      let pvar = Pvar.mk (Mangled.from_string ("var_" ^ string_of_int idx)) proc_name in
      let aux_norm = EdgeExp.Access (AccessPath.of_pvar pvar Typ.uint) in
      (* let map = List.fold component ~init:map ~f:(fun map (norm, dcp_node as node) -> 
        debug_log "(%a, %a) --> %a\n" DCP.Node.pp dcp_node EdgeExp.pp norm EdgeExp.pp aux_norm;
        VFG.Map.add node aux_norm map
      )
      in
      map, EdgeExp.Set.add aux_norm norm_set *)

      List.fold component ~init:(map, EdgeExp.Set.add aux_norm norm_set) ~f:(fun (map, norm_set) ((exp, _ as node) : VFG.Node.t) ->
        if EdgeExp.is_return exp then VFG.Map.add node exp map, EdgeExp.Set.add exp norm_set
        else VFG.Map.add node aux_norm map, norm_set
      )
    )
    in
    debug_log "[VFG Mapping]\n";
    VFG.Map.iter (fun (norm, dcp_node) aux_norm -> 
      debug_log "  (%a, %a) --> %a\n" DCP.Node.pp dcp_node EdgeExp.pp norm EdgeExp.pp aux_norm;
    ) vfg_map;


    (* Apply VFG mapping and rename DCP variables to ensure acyclic reset DAG *)
    DCP.EdgeSet.iter (fun (dcp_src, edge_data, dcp_dst) -> 
      (* let constraints = DC.Map.fold (fun lhs_norm (rhs_norm, const) map -> 
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
      in *)
      let constraints = DC.Map.fold (fun lhs_norm (rhs_norm, op, rhs_const) map ->
        let lhs_node, rhs_node = (lhs_norm, dcp_dst), (rhs_norm, dcp_src) in
        match VFG.Map.find_opt lhs_node vfg_map, VFG.Map.find_opt rhs_node vfg_map with
        | Some lhs_mapped, Some rhs_mapped -> DC.Map.add lhs_mapped (rhs_mapped, op, rhs_const) map
        | None, Some rhs_mapped -> (
          if EdgeExp.is_variable lhs_norm graph_data.formals then (
            map
            (* if DC.Map.mem rhs_mapped map then map
            else DC.Map.add rhs_mapped (rhs_mapped, const) map *)
          )
          else DC.Map.add lhs_norm (rhs_mapped, op, rhs_const) map
        )
        | Some lhs_mapped, None -> (
          if EdgeExp.is_variable rhs_norm graph_data.formals then (
            map
            (* if DC.Map.mem lhs_mapped map then map
            else DC.Map.add lhs_mapped (lhs_mapped, const) map *)
          )
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
              if EdgeExp.is_formal access graph_data.formals then access, None
              else (
                match VFG.Map.find_opt (access, dcp_dst) vfg_map, VFG.Map.find_opt (access, dcp_src) vfg_map with
                | Some dst_map, Some _ -> dst_map, None
                | Some dst_map, None -> dst_map, None
                | None, Some src_map -> src_map, None
                | _ -> (
                  (* This case should occur only for SSA variables which are constant after initialization *)
                  console_log "VFG ACCESS: %a\n" EdgeExp.pp access;
                  let ssa_init_rhs = EdgeExp.Map.find access ssa_variables_map in
                  ssa_init_rhs, None
                  (* debug_log "  [VFG] Missing mapping for: %a\n" EdgeExp.pp access;
                  access, None *)
                )
              )
            ) None
            in
            renamed_arg, typ

          ) else arg, typ
        )
        in
        EdgeExp.Call (ret_typ, proc_name, renamed_args, loc)

        (* match Location.Map.find_opt loc graph_data.call_summaries with
        | Some call_summary -> (
          debug_log "[Call] %a\n  [Complexity bound] %a\n" EdgeExp.pp call EdgeExp.pp call_summary.bound;
          (match call_summary.return_bound with
          | Some bound -> debug_log "  [Return bound] %a\n" EdgeExp.pp bound
          | _ -> ());
          debug_log "  [Complexity bound renamed]: %a\n" EdgeExp.pp renamed_bound;
          call
        )
        | None -> call *)
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


  (* Determine all local bounds *)
  let dcp_scc_graph = DCP.create () in

  (* Suboptimal way to find all SCC edges, the ocamlgraph library for some
    * reason does not have a function that returns edges of SCCs.  *)
  let get_scc_edges dcp =
    let components = DCP_SCC.scc_list dcp in

    List.fold components ~init:DCP.EdgeSet.empty ~f:(fun acc component ->
      (* Iterate over all combinations of SCC nodes and check if there
      * are edges between them in both directions *)
      List.fold component ~init:acc ~f:(fun acc node ->
        DCP.add_vertex dcp_scc_graph node;

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
  let scc_edges = get_scc_edges dcp in
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
          let _, (rhs_norm, op, rhs_const) = dc in
          if not (DC.same_norms dc) then (
            (* Must be a reset *)
            let resets = Resets.add (edge, rhs_norm, rhs_const) resets in
            increments, resets
          ) else if DC.is_increasing dc then (
            (* Must be a increment *)
            let increments = Increments.add (edge, rhs_const) increments in
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
    let cache = get_update_map norm graph_data.edges cache in
    let increments, _ = EdgeExp.Map.find norm cache.updates in
    let norm_increment_sum, cache = Increments.fold (fun (dcp_edge, const) (norm_increment_sum, cache) ->
      let _, edge_data, _ = dcp_edge in
      let cache = transition_bound dcp_edge cache in
      let increment_exp = EdgeExp.mult edge_data.bound (EdgeExp.Const (Const.Cint const)) in
      (EdgeExp.add norm_increment_sum increment_exp), cache
    ) increments (EdgeExp.zero, cache)
    in
    (EdgeExp.add total_sum norm_increment_sum), cache
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
      let _, edge_data, _ = dcp_edge in
      let cache = transition_bound dcp_edge cache in
      if EdgeExp.is_zero edge_data.bound then Stop ([EdgeExp.zero], cache) 
      else (
        match List.hd args with
        | Some arg when EdgeExp.is_one arg -> Continue (args, cache)
        | _ -> (
          if EdgeExp.is_one edge_data.bound then Continue ([edge_data.bound], cache) 
          else Continue (edge_data.bound :: args, cache)
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
        | EdgeExp.Max args -> (
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
          let _, resets = EdgeExp.Map.find norm cache.updates in
          let increment_sum, cache = calculate_increment_sum (EdgeExp.Set.singleton norm) cache in

          assert(not (Resets.is_empty resets));
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
          ) resets ([], cache)
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
              let value = EdgeExp.always_positive arg tenv z3_ctx solver in
              value, { cache with positivity = EdgeExp.Map.add arg value cache.positivity }
            )
            in
            (if is_always_positive then arg else EdgeExp.Max [arg]), cache
          )
          | _ -> EdgeExp.Max flattened_args, cache
          in


          (* let max_args_unpacked = List.fold max_args ~init:[] ~f:(fun acc arg ->
            match arg with
            | EdgeExp.Max nested_args -> (
              List.fold nested_args ~init:acc ~f:(fun acc nested_arg -> 
                if List.mem acc nested_arg ~equal:EdgeExp.equal then acc else nested_arg :: acc
              )
            )
            | _ -> if List.mem acc arg ~equal:EdgeExp.equal then acc else arg :: acc
          )
          in
          let max_subexp = match List.length max_args_unpacked with
          | 0 -> L.(die InternalError)"[VB] Missing max() arguments for [%a]!" EdgeExp.pp norm
          | 1 -> List.hd_exn max_args_unpacked
          | _ -> EdgeExp.Max max_args_unpacked 
          in *)
          (EdgeExp.add max_subexp increment_sum), cache
        )
        in

        var_bound, { cache with variable_bounds = EdgeExp.Map.add norm var_bound cache.variable_bounds }
      ) 
      else (
        let always_positive = EdgeExp.always_positive norm tenv z3_ctx solver in
        debug_log "   [Always positive] %a: %B\n" EdgeExp.pp norm always_positive;
        let bound = if always_positive then norm else EdgeExp.Max [norm] in
        bound, { 
          cache with 
          variable_bounds = EdgeExp.Map.add norm bound cache.variable_bounds;
          positivity = EdgeExp.Map.add norm always_positive cache.positivity; }
      )
    )
    in
    debug_log "   [VB(%a)] %a\n" EdgeExp.pp norm EdgeExp.pp bound;
    bound, cache


  and transition_bound (src, (edge_data : DCP.EdgeData.t), dst) cache =
    (* For variable norms: TB(t) = IncrementSum + ResetSum 
      * For constant norms: TB(t) = constant *)
    debug_log "[TB] %a -- %a\n" DCP.Node.pp src DCP.Node.pp dst;

    match edge_data.bound with
    | EdgeExp.Inf when edge_data.computing_bound -> raise Exit
    | EdgeExp.Inf -> (
      (* Infinite recursion guard *)
      edge_data.computing_bound <- true;

      (* let cache = calculate_exec_cost edge_data cache in
      log "   [Execution cost] %a\n" EdgeExp.pp edge_data.execution_cost; *)

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
        (* | _ -> L.(die InternalError)"[Bound] Unsupported norm expression [%a]!" EdgeExp.pp norm *)
        in
        
        debug_log "[Edge bound (%a)] %a\n" EdgeExp.pp norm EdgeExp.pp bound;
        edge_data.bound <- bound;
        cache
      )
      | None -> L.(die InternalError)"[Bound] edge has no bound norm!"
    )
    | _ -> cache

  and calculate_exec_cost (edge_data : DCP.EdgeData.t) cache =
    (* Sum together the cost of all functions called on this transition *)
    let cost_list, updated_cache = EdgeExp.Set.fold (fun call_exp (cost_list, cache_acc) -> match call_exp with
      | EdgeExp.Call (_, proc_name, args, loc) -> (
        let payload_opt = Location.Map.find_opt loc graph_data.call_summaries in
        match payload_opt with
        | Some payload -> (
          let subst_bound = EdgeExp.subst payload.bound args payload.formal_map in
          debug_log "  [CALL] %a : %a | %a\n" Procname.pp proc_name Domain.pp_summary payload Location.pp loc;
          (* debug_log "  [CALL] FormalMap: %a\n" FormalMap.pp payload.formal_map; *)
          debug_log "  [CALL] Formal Bound: %a\n" EdgeExp.pp payload.bound;
          debug_log "  [CALL] Instantiated Bound: %a\n" EdgeExp.pp subst_bound;

          (* Replace each argument with its variable bound (coarse overapproximation?) *)
          let call_cost, new_cache = EdgeExp.map_accesses subst_bound ~f:(fun argument_access cache_acc -> 
            let argument_bound, cache_acc = variable_bound (EdgeExp.Access argument_access) cache_acc in
            argument_bound, cache_acc
          ) cache_acc
          in
          (EdgeExp.simplify call_cost) :: cost_list, new_cache
        )
        | None -> cost_list, cache_acc

        (* match Location.Map.find_opt loc call_summaries with
        | Some call_summary -> (
          debug_log "  [Call] %a : %a | %a\n" Procname.pp proc_name Domain.pp_summary call_summary Location.pp loc;
          (* Replace each argument with its variable bound (coarse overapproximation?) *)
          let call_cost, new_cache = EdgeExp.map_accesses call_summary.bound ~f:(fun argument_access cache_acc -> 
            let argument_bound, cache_acc = variable_bound (EdgeExp.Access argument_access) cache_acc in
            argument_bound, cache_acc
          ) cache_acc
          in
          (EdgeExp.simplify call_cost) :: cost_list, new_cache
        )
        | None -> cost_list, cache_acc *)
      )
      | _ -> assert(false)
    ) edge_data.calls ([], cache)
    in
    if not (List.is_empty cost_list) then (
      let cost_expr = List.fold (List.tl_exn cost_list) ~init:(List.hd_exn cost_list)  ~f:EdgeExp.add in
      edge_data.execution_cost <- cost_expr;
    );
    updated_cache
  in

  let bound, cache = if not (DCP.EdgeSet.is_empty remaining_edges) then (
    let culprits = List.map (DCP.EdgeSet.elements remaining_edges) ~f:(fun (src, _, dst) ->
      F.asprintf "%a ---> %a" DCP.Node.pp src DCP.Node.pp dst
    ) |> String.concat ~sep:"\n"
    in
    L.internal_error "[%a] Local bound could not be \
    determined for following edges:\n%s\n\
    Returning [Infinity]\n" Procname.pp proc_name culprits;
    EdgeExp.Inf, empty_cache
  ) else (
    debug_log "[Local bounds]\n";

    (* Filter out-of-loop edges with function calls *)
    let call_edges = DCP.EdgeSet.filter (fun (src, edge_data, dst) ->
      let local_bound = Option.value_exn edge_data.bound_norm in
      debug_log "  %a ---> %a: %a\n" DCP.Node.pp src DCP.Node.pp dst EdgeExp.pp local_bound;
      EdgeExp.is_one local_bound && not (EdgeExp.Set.is_empty edge_data.calls)
    ) graph_data.edges
    in

    debug_log "\n==========[Calculating bounds]====================\n";

    (* Calculate bound for all back-edges and sum them to get the total bound *)
    try
      let cache = DCP.EdgeSet.fold (fun edge cache ->
        let _, edge_data, _ = edge in
        if DCP.EdgeData.is_backedge edge_data then transition_bound edge cache
        else cache
      ) graph_data.edges empty_cache
      in

      (* Execution cost must be computed after transitions bounds
       * to avoid computation cycles *)
      let bound, cache = DCP.EdgeSet.fold (fun edge (bound, cache) ->
        let src, edge_data, dst = edge in
        if DCP.EdgeData.is_backedge edge_data then (
          let cache = calculate_exec_cost edge_data cache in

          let total_edge_cost = if EdgeExp.is_one edge_data.execution_cost then (
            let value = EdgeExp.mult edge_data.bound edge_data.execution_cost in
            debug_log "[Edge cost] %a ---> %a: %a * %a = %a\n" DCP.Node.pp src DCP.Node.pp dst 
            EdgeExp.pp edge_data.bound EdgeExp.pp edge_data.execution_cost EdgeExp.pp value;
            value
          ) else (
            let value = EdgeExp.mult edge_data.bound (EdgeExp.add EdgeExp.one edge_data.execution_cost) in
            debug_log "[Edge cost] %a ---> %a: %a + %a * %a = %a\n" DCP.Node.pp src DCP.Node.pp dst 
            EdgeExp.pp edge_data.bound EdgeExp.pp edge_data.bound EdgeExp.pp edge_data.execution_cost EdgeExp.pp value;
            value
          )
          in

          (EdgeExp.add bound total_edge_cost), cache
        ) else bound, cache
      ) graph_data.edges (EdgeExp.zero, cache)
      in
      debug_log "Total back-edge cost: %a\n" EdgeExp.pp bound;

      let exec_cost, cache = DCP.EdgeSet.fold (fun (src, edge_data, dst) (total_exec_cost, cache) ->
        let cache = calculate_exec_cost edge_data cache in
        debug_log "[Call edge] %a ---> %a, exec cost: %a\n" DCP.Node.pp src DCP.Node.pp dst EdgeExp.pp edge_data.execution_cost;

        (* TODO: Ignore function calls with unit cost for now. We'll figure out what to do with those later on *)
        let new_cost = if EdgeExp.is_one edge_data.execution_cost then total_exec_cost
        else EdgeExp.add total_exec_cost edge_data.execution_cost
        in
        new_cost, cache
      ) call_edges (EdgeExp.zero, cache)
      in
      debug_log "Total exec cost: %a\n" EdgeExp.pp exec_cost;

      EdgeExp.add bound exec_cost, cache
    with Exit -> (
      EdgeExp.Inf, empty_cache
    )
  )
  in
  debug_log "\n[Final bound] %a\n" EdgeExp.pp bound;

  (* let param_sorts, param_symbols, bound_vars, bound_accesses, bound_vars_map = List.foldi bound_formals 
  ~init:([], [], [], [], AccessPathMap.empty) 
  ~f:(fun idx (sorts, symbols, bound_vars, accesses, bindings) exp ->
    match exp with
    | EdgeExp.Access access -> (
      let access_str = F.asprintf "%a" AccessPath.pp access in
      let access_symbol = Z3.Symbol.mk_string z3_ctx access_str in
      (* let access_exp = Z3.Expr.mk_const z3_ctx access_symbol z3_int_sort in *)
      let de_bruijn_index = (List.length bound_formals) - idx - 1 in
      (* let de_bruijn_index = idx in *)
      let bound_var = Z3.Quantifier.mk_bound z3_ctx de_bruijn_index z3_int_sort in
      match AccessPath.get_typ access tenv with
      | Some typ when Typ.is_int typ -> (
        sorts @ [z3_int_sort], 
        symbols @ [access_symbol],
        bound_vars @ [bound_var],
        accesses @ [access],
        AccessPathMap.add access bound_var bindings
      )
      | _ -> assert(false)
    )
    | _ -> assert(false)
  )
  in *)



  (* let monotony_map = try
    let bound_formals = EdgeExp.Set.elements (EdgeExp.get_accesses bound) in
    let real_sort = Z3.Arithmetic.Real.mk_sort z3_ctx in
    let param_sorts, param_symbols, bound_accesses = List.fold bound_formals ~init:([], [], [])
    ~f:(fun (sorts, symbols, accesses) exp ->
      match exp with
      | EdgeExp.Access access -> (
        let access_str = F.asprintf "%a" AccessPath.pp access in
        let access_symbol = Z3.Symbol.mk_string z3_ctx access_str in
        match AccessPath.get_typ access tenv with
        | Some typ when Typ.is_int typ -> (
          sorts @ [real_sort], 
          symbols @ [access_symbol],
          accesses @ [access]
        )
        | _ -> assert(false)
      )
      | _ -> assert(false)
    )
    in

    if EdgeExp.is_const bound then EdgeExp.Map.empty
    else (
      debug_log "[Determining monotony of variables]\n";
      let bound_func_decl = Z3.FuncDecl.mk_func_decl_s z3_ctx "bound_function" param_sorts real_sort in
      let params = List.map param_symbols ~f:(fun symbol -> Z3.Expr.mk_const z3_ctx symbol real_sort) in
      let func_app = Z3.Expr.mk_app z3_ctx bound_func_decl params in
      let q_bound_var = Z3.Quantifier.mk_bound z3_ctx 0 real_sort in

      let tmp_var_symbol = Z3.Symbol.mk_string z3_ctx "tmp_var" in
      let tmp_var_exp = Z3.Expr.mk_const z3_ctx tmp_var_symbol real_sort in

      List.foldi param_symbols ~init:EdgeExp.Map.empty ~f:(fun replace_idx acc current_symbol ->
        let formal_exp = List.nth_exn bound_formals replace_idx in
        let param_access = List.nth_exn bound_accesses replace_idx in
        let param_sort = List.nth_exn param_sorts replace_idx in
        let param_name = Z3.Symbol.to_string current_symbol in
        let param_expr = Z3.Expr.mk_const z3_ctx current_symbol real_sort in

        let new_params = List.mapi params ~f:(fun param_idx param ->
          if Int.equal param_idx replace_idx then tmp_var_exp else param
        )
        in
        let z3_func_app_2 = Z3.Expr.mk_app z3_ctx bound_func_decl new_params in

        (* Construct Z3 bound with bound variable for the current parameter *)
        let bound_access_map access = if AccessPath.equal access param_access 
        then Some q_bound_var 
        else None
        in
        let z3_bound = EdgeExp.to_z3_expr bound tenv z3_ctx (Some bound_access_map) |> fst in
        let type_constraints = EdgeExp.to_z3_expr bound tenv z3_ctx None |> snd |> Z3ExprSet.elements in

        (* Use constructed bound in quantified expression to define function over all arguments *)
        let args = List.mapi params ~f:(fun param_idx param ->
          if Int.equal param_idx replace_idx then q_bound_var else param
        )
        in

        (* ForAll[x]: bound_func(.., x, ..) = bound_expr *)
        let q_func_app = Z3.Expr.mk_app z3_ctx bound_func_decl args in
        let q_body = Z3.Boolean.mk_eq z3_ctx q_func_app z3_bound in
        let quantifier = Z3.Quantifier.mk_forall z3_ctx [param_sort] [current_symbol] q_body None [] [] None None in
        let quantifier_expr = Z3.Expr.simplify (Z3.Quantifier.expr_of_quantifier quantifier) None in
        let solver_base_assertions = quantifier_expr :: type_constraints in

        (* debug_log "\n  [Z3 Quantifier body] %s\n" (Z3.Expr.to_string quantifier_body);
        debug_log "\n  [Z3 Bound function] %s\n" (Z3.Expr.to_string func_constraint); *)
        
        let antecedent = Z3.Arithmetic.mk_gt z3_ctx tmp_var_exp param_expr in
        let non_decreasing_consequent = Z3.Arithmetic.mk_ge z3_ctx z3_func_app_2 func_app in
        let non_decreasing_implication = Z3.Boolean.mk_implies z3_ctx antecedent non_decreasing_consequent in
        let non_decreasing_goal = Z3.Expr.simplify (Z3.Boolean.mk_not z3_ctx non_decreasing_implication) None in

        let non_increasing_consequent = Z3.Arithmetic.mk_le z3_ctx z3_func_app_2 func_app in
        let non_increasing_implication = Z3.Boolean.mk_implies z3_ctx antecedent non_increasing_consequent in
        let non_increasing_goal = Z3.Expr.simplify (Z3.Boolean.mk_not z3_ctx non_increasing_implication) None in

        (* debug_log "  [Z3 Goal] %s\n" (Z3.Expr.to_string goal); *)
        (* List.iter type_constraints ~f:(fun expr -> 
          debug_log "  [Z3 Type constraint] %s\n" (Z3.Expr.to_string expr);
        ); *)

        try
          (* Check for non-decreasing property first *)
          Z3.Solver.reset solver;
          Z3.Solver.add solver (non_decreasing_goal :: solver_base_assertions);

          match Z3.Solver.check solver [] with
          | Z3.Solver.UNSATISFIABLE -> (
            debug_log "  [Variable: %s] Non-decreasing\n" param_name;
            EdgeExp.Map.add formal_exp VariableMonotony.NonDecreasing acc
          )
          | Z3.Solver.SATISFIABLE -> (
            let decreasing_model = match Z3.Solver.get_model solver with
            | Some model -> Z3.Model.to_string model
            | None -> assert(false)
            in

            (* Check for non-increasing property next *)
            Z3.Solver.reset solver;
            Z3.Solver.add solver (non_increasing_goal :: solver_base_assertions);

            match Z3.Solver.check solver [] with
            | Z3.Solver.UNSATISFIABLE -> (
              debug_log "  [Variable: %s] Non-increasing\n" param_name;
              EdgeExp.Map.add formal_exp VariableMonotony.NonDecreasing acc
            )
            | Z3.Solver.SATISFIABLE -> (
              debug_log "  [Variable: %s] Not Monotonic\n" param_name;
              EdgeExp.Map.add formal_exp VariableMonotony.NotMonotonic acc
            ) 
            | Z3.Solver.UNKNOWN -> (
              (* EdgeExp.Map.add formal_exp FormalBoundMonotony.NotMonotonic acc *)
              L.die InternalError "[Monotony Check] Unknown Z3 result: %s\n" (Z3.Solver.get_reason_unknown solver)
            )
          )
          | Z3.Solver.UNKNOWN -> (
            (* EdgeExp.Map.add formal_exp FormalBoundMonotony.NotMonotonic acc *)
            L.die InternalError "[Monotony Check] Unknown Z3 result: %s\n" (Z3.Solver.get_reason_unknown solver)
          )
        with Z3.Error str -> (
          (* This should hopefully be only caused by potential Z3 timeout *)
          (* EdgeExp.Map.add formal_exp FormalBoundMonotony.NonDecreasing acc *)
          L.die InternalError "[Z3 Error] %s\n" str
        )
      )
    );
  with Z3.Error str -> (
    L.die InternalError "[Z3 Error] %s\n" str
  )
  in *)

  debug_log "========[Determining monotony of bound variables]========\n";
  let monotony_map = EdgeExp.determine_monotony bound tenv z3_ctx solver in
  EdgeExp.Map.iter (fun variable monotony -> match monotony with
    | VariableMonotony.NonDecreasing -> debug_log "[Variable: %a] Non-decreasing\n" EdgeExp.pp variable;
    | VariableMonotony.NonIncreasing -> debug_log "[Variable: %a] Non-increasing\n" EdgeExp.pp variable;
    | VariableMonotony.NotMonotonic -> debug_log "[Variable: %a] Not Monotonic\n" EdgeExp.pp variable;
  ) monotony_map;

  (* (* This is kind of stupid but it seems there's no good way to avoid
   * converting to Z3 expression twice: once with bound variables for quantified
   * expression and once with free variables for type constraint expressions *)
  let bound_access_map access = AccessPathMap.find access bound_vars_map, Z3ExprSet.empty in
  let z3_bound = EdgeExp.to_z3_expr bound tenv z3_ctx (Some bound_access_map) |> fst in
  let type_constraints = EdgeExp.to_z3_expr bound tenv z3_ctx None |> snd |> Z3ExprSet.elements in

  debug_log "[Determining monotony of variables]\n";

  (* Create quantified expression for function declaration, which defines the value of the
   * function for all possible arguments, i.e., ForAll[params]: func_decl(params) = bound *)
  try
    let z3_zero_const = Z3.Arithmetic.Integer.mk_numeral_i z3_ctx 0 in
    let z3_bound_func_decl = Z3.FuncDecl.mk_func_decl_s z3_ctx "bound_function" param_sorts z3_int_sort in
    let params = List.map param_symbols ~f:(fun symbol -> Z3.Expr.mk_const z3_ctx symbol z3_int_sort) in
    (* let type_constraints = List.map params ~f:(fun param ->
      Z3.Arithmetic.mk_ge z3_ctx param z3_zero_const
    ) in *)

    let z3_func_app = Z3.Expr.mk_app z3_ctx z3_bound_func_decl params in
    let z3_quant_func_app = Z3.Expr.mk_app z3_ctx z3_bound_func_decl bound_vars in
    let quantifier_body = Z3.Boolean.mk_eq z3_ctx z3_quant_func_app z3_bound in
    let quantified_func = Z3.Quantifier.mk_forall z3_ctx param_sorts param_symbols quantifier_body None [] [] None None in
    let func_constraint = Z3.Expr.simplify (Z3.Quantifier.expr_of_quantifier quantified_func) None in
    let solver_base_assertions = func_constraint :: type_constraints in
    (* let solver_base_assertions = func_constraint :: [] in *)

    debug_log "\n  [Z3 Quantifier body] %s\n" (Z3.Expr.to_string quantifier_body);
    debug_log "\n  [Z3 Bound function] %s\n" (Z3.Expr.to_string func_constraint);

    List.iteri param_symbols ~f:(fun replace_idx current_symbol ->
      let param_name = Z3.Symbol.to_string current_symbol in
      debug_log "  [Variable: %s]" param_name;
      
      (* Check for non-decreasing property *)
      let symbol_name = param_name ^ "_2" in
      let symbol = Z3.Symbol.mk_string z3_ctx symbol_name in
      let symbol_exp = Z3.Expr.mk_const z3_ctx symbol z3_int_sort in
      let old_symbol_exp = Z3.Expr.mk_const z3_ctx current_symbol z3_int_sort in

      let new_param_symbols = List.mapi param_symbols ~f:(fun param_idx param_symbol ->
        if Int.equal param_idx replace_idx then symbol else param_symbol
      )
      in


      let new_quantified_func = Z3.Quantifier.mk_forall z3_ctx param_sorts new_param_symbols quantifier_body None [] [] None None in
      let new_func_constraint = Z3.Expr.simplify (Z3.Quantifier.expr_of_quantifier new_quantified_func) None in

      let new_params = List.mapi params ~f:(fun param_idx param ->
        if Int.equal param_idx replace_idx then symbol_exp else param
      )
      in
      let z3_func_app_2 = Z3.Expr.mk_app z3_ctx z3_bound_func_decl new_params in

      let antecedent = Z3.Arithmetic.mk_gt z3_ctx symbol_exp old_symbol_exp in
      let non_decreasing_consequent = Z3.Arithmetic.mk_ge z3_ctx z3_func_app_2 z3_func_app in
      let non_decreasing_implication = Z3.Boolean.mk_implies z3_ctx antecedent non_decreasing_consequent in
      let non_decreasing_goal = Z3.Expr.simplify (Z3.Boolean.mk_not z3_ctx non_decreasing_implication) None in

      (* debug_log "  [Z3 Goal] %s\n" (Z3.Expr.to_string goal); *)
      (* List.iter type_constraints ~f:(fun expr -> 
        debug_log "  [Z3 Type constraint] %s\n" (Z3.Expr.to_string expr);
      ); *)

      Z3.Solver.reset solver;
      Z3.Solver.add solver (solver_base_assertions @ [non_decreasing_goal]);

      match Z3.Solver.check solver [] with
      | Z3.Solver.UNSATISFIABLE -> (
        debug_log " Non-decreasing\n";
        let assertions = Z3.Solver.get_assertions solver in
        List.iter assertions ~f:(fun expr -> 
          debug_log "  [Z3 Solver Assertion] %s\n" (Z3.Expr.to_string expr);
        );
      )
      | Z3.Solver.SATISFIABLE -> (
        debug_log " DECREASING\n";
        debug_log "  [Variable: %s]" param_name;
        let decreasing_model = match Z3.Solver.get_model solver with
        | Some model -> Z3.Model.to_string model
        | None -> assert(false)
        in

        (* Check for non-increasing property *)
        let non_increasing_consequent = Z3.Arithmetic.mk_le z3_ctx z3_func_app_2 z3_func_app in
        let non_increasing_implication = Z3.Boolean.mk_implies z3_ctx antecedent non_increasing_consequent in
        let non_increasing_goal = Z3.Expr.simplify (Z3.Boolean.mk_not z3_ctx non_increasing_implication) None in

        Z3.Solver.reset solver;
        Z3.Solver.add solver (non_increasing_goal :: solver_base_assertions);
        match Z3.Solver.check solver [] with
        | Z3.Solver.UNSATISFIABLE -> (
          debug_log " Non-increasing\n";
        )
        | Z3.Solver.SATISFIABLE -> (
          debug_log " Not Monotonic\n";
        ) 
        | Z3.Solver.UNKNOWN -> (
          let assertions = Z3.Solver.get_assertions solver in
          List.iter assertions ~f:(fun expr -> 
            debug_log "  [Z3 Solver Assertion] %s\n" (Z3.Expr.to_string expr);
          );
          L.die InternalError "[Monotony Check] Unknown Z3 result: %s\n" (Z3.Solver.get_reason_unknown solver)
        )
      )
      | Z3.Solver.UNKNOWN -> (
        let assertions = Z3.Solver.get_assertions solver in
        List.iter assertions ~f:(fun expr -> 
          debug_log "  [Z3 Solver Assertion] %s\n" (Z3.Expr.to_string expr);
        );
        L.die InternalError "[Monotony Check] Unknown Z3 result: %s\n" (Z3.Solver.get_reason_unknown solver)
      )
    ); *)

  let ret_type = Procdesc.get_ret_type proc_desc in
  let return_bound = match ret_type.desc with
  | Tint _ -> (
    debug_log "[Return type] %a\n" Typ.(pp Pp.text) ret_type;
    (* let edge_list = DCP.EdgeSet.elements graph_data.edges in *)
    (* let _, return_edge, _ = List.find_exn edge_list ~f:(fun (_, edge, _) -> DCP.EdgeData.is_exit_edge edge) in *)
    let return_access = AccessPath.of_pvar (Procdesc.get_ret_var proc_desc) ret_type in
    (* log "[Return access] %a\n" AccessPath.pp return_access; *)
    (* let norm, _ = DC.Map.find (EdgeExp.Access return_access) return_edge.constraints in *)
    (* log "[Return norm] %a\n" EdgeExp.pp norm; *)
    let return_bound, _ = variable_bound (EdgeExp.Access return_access) cache in
    debug_log "[Return bound] %a\n" EdgeExp.pp return_bound;
    Some return_bound
  )
  | _ -> None
  in

  debug_log "Description:\n  signed x: max(x, 0) == [x]\n---------------------------------\n";
  let payload : Domain.summary = {
    formal_map = FormalMap.make proc_desc;
    monotony_map = monotony_map;
    bound = bound;
    return_bound = return_bound;
  }
  in
  Utils.close_outf log_file;

  let looper_json = looper_dir ^/ source_file_str ^/ proc_name_str ^ ".json" in
  (* let json_file = mk_outfile json_report_fname in *)
  
  let new_summary = Analyzer.Payload.update_summary payload summary in
  JsonReports.write_looper_report ~looper_json new_summary;
  new_summary
