open! IStd

module F = Format
module L = Logging
module Domain = LooperDomain
module Analyzer = LooperLTS

let log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.printf fmt


module CFG = ProcCfg.NormalOneInstrPerNode
(* module CFG = ProcCfg.Normal *)

(* module Analyzer = AbstractInterpreter.Make (CFG) (TransferFunctions) *)
(* module Analyzer = AbstractInterpreter.MakeWTO (TransferFunctions (CFG)) *)
module DCP_SCC = Graph.Components.Make(Domain.DCP)
module VFG_SCC = Graph.Components.Make(Domain.VFG)


let checker {Callbacks.exe_env; summary; } : Summary.t =
  let open Domain in
  let proc_desc = Summary.get_proc_desc summary in
  let proc_name = Procdesc.get_proc_name proc_desc in
  let proc_name_str = Procname.to_simplified_string proc_name in
  log "\n\n---------------------------------";
  log "\n- ANALYZING: %s" proc_name_str;
  log "\n---------------------------------\n";
  log " Begin location: %a\n" Location.pp (Procdesc.get_loc proc_desc);

  let graph_data = Analyzer.GraphConstructor.create_lts (Exe_env.get_tenv exe_env proc_name) proc_desc summary in
  
  let lts = DCP.create () in
  DCP.NodeSet.iter (fun node ->
    DCP.add_vertex lts node;
  ) graph_data.nodes;
  DCP.EdgeSet.iter (fun edge ->
    DCP.add_edge_e lts edge;
  ) graph_data.edges;

  let out_folder = "./Graphs/" ^ proc_name_str ^ "/" in
  (try Unix.mkdir_p out_folder with _ -> ());
  let file = Out_channel.create (out_folder ^ "LTS.dot") in
  active_graph_type := LTS;
  DCPDot.output_graph file lts;
  Out_channel.close file;

  log "\n---------------------------------";
  log "\n- ANALYSIS REPORT %s" proc_name_str;
  log "\n---------------------------------\n";
  (* log "%a" pp post; *)

  (* Draw dot graph, use nodes and edges stored in graph_data *)
  log "[POTENTIAL NORMS] ";
  EdgeExp.Set.iter (fun norm -> log "%a; " EdgeExp.pp norm) graph_data.potential_norms; log "\n";

  log "[INITIAL NORMS] ";
  EdgeExp.Set.iter (fun norm -> log "%a; " EdgeExp.pp norm) graph_data.norms; log "\n";

  let dcp = DCP.create () in
  DCP.NodeSet.iter (fun node ->
    DCP.add_vertex dcp node;
  ) graph_data.nodes;

  
  (* Much easier to implement and more readable in imperative style.
    * Derive difference constraints for each edge for each norm and
    * add newly created norms to unprocessed_norms set during the process *)
  let unprocessed_norms = ref graph_data.norms in
  let processed_norms = ref EdgeExp.Set.empty in
  while not (EdgeExp.Set.is_empty !unprocessed_norms) do (
    let norm = EdgeExp.Set.min_elt !unprocessed_norms in
    unprocessed_norms := EdgeExp.Set.remove norm !unprocessed_norms;
    processed_norms := EdgeExp.Set.add norm !processed_norms;
    DCP.EdgeSet.iter (fun (_, edge_data, _) ->
      let new_norms = DCP.EdgeData.derive_constraint edge_data norm graph_data.formals in
      
      (* Remove already processed norms and add new norms to unprocessed set *)
      let new_norms = EdgeExp.Set.diff new_norms !processed_norms in
      unprocessed_norms := EdgeExp.Set.union new_norms !unprocessed_norms;
    ) graph_data.edges;
  ) done;

  log "[FINAL NORMS] ";
  EdgeExp.Set.iter (fun norm -> log "%a; " EdgeExp.pp norm) !processed_norms; log "\n";

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
  DCP.EdgeSet.iter (fun (src, edge_data, dst) ->
    DCP.EdgeData.derive_guards edge_data !processed_norms solver ctx;
    DCP.add_edge_e dcp (src, edge_data, dst);
  ) graph_data.edges;

  let guarded_nodes = DCP.fold_edges_e (fun (_, edge_data, dst) acc ->
    if EdgeExp.Set.is_empty edge_data.guards then acc 
    else (
      (* log "GUARDED NODE: %a\n" DCP.Node.pp dst;  *)
      DCP.NodeSet.add dst acc
    )
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
        if DCP.EdgeData.is_backedge edge_data then (
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
          match edge_data.branch_info with
          | Some (_, branch, _) when branch -> true
          | _ -> false
        )
        in
        let (src, true_branch, dst) = List.hd_exn true_branch in
        true_branch.guards <- EdgeExp.Set.union guards true_branch.guards;
        if not (DCP.Node.equal src dst) then propagate_guards (DCP.NodeSet.add dst nodes);

        let (_, backedge, _) = List.find_exn incoming_edges ~f:(fun (_, edge_data, _) -> 
          DCP.EdgeData.is_backedge edge_data
        ) in

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
  to_natural_numbers graph_data.edges;

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
      (norm_is_variable lhs_norm graph_data.formals) && 
      (norm_is_variable rhs_norm graph_data.formals) then (
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
  ) graph_data.edges;

  let file = Out_channel.create (out_folder ^ "VFG.dot") in
  VFG_Dot.output_graph file vf_graph;
  Out_channel.close file;

  (* Create VFG mapping, create fresh variable 'v' for each SCC
    * and map each VFG node to this fresh variable. *)
  let vfg_components = VFG_SCC.scc_list vf_graph in
  let vfg_map = List.foldi vfg_components ~init:VFG.Map.empty ~f:(fun idx map component ->
    let pvar = Pvar.mk (Mangled.from_string ("var_" ^ string_of_int idx)) proc_name in
    let aux_norm = EdgeExp.Access (AccessPath.of_pvar pvar Typ.uint) in

    List.fold component ~init:map ~f:(fun map ((exp, _ as node) : VFG.Node.t) ->
      let aux_norm = match exp with
      | EdgeExp.Access ((var, _), _) -> (match Var.get_pvar var with
        | Some pvar when Pvar.is_return pvar -> exp
        | _ -> aux_norm
      )
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
    let calls = CallSiteSet.map (fun (call, loc) -> match call with
    | EdgeExp.Call (typ, procname, args, call_summary) -> (
      log "VFG call: %a\n" EdgeExp.pp call;
      let renamed_bound, _ = EdgeExp.map_accesses call_summary.bound ~f:(fun access _ ->
        let access = EdgeExp.Access access in
        let renamed_var = match VFG.Map.find_opt (access, dcp_dst) vfg_map with
        | Some mapped_var -> mapped_var
        | None -> access
        in
        renamed_var, None
      ) None
      in
      log "VFG renamed bound: %a\n" EdgeExp.pp renamed_bound;
      EdgeExp.Call (typ, procname, args, { call_summary with bound = renamed_bound; }), loc
    )
    | _ -> assert(false)
    ) edge_data.calls 
    in
    edge_data.calls <- calls;
    edge_data.constraints <- constraints;
  ) graph_data.edges;

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
  ) graph_data.edges;

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
  let non_scc_edges = DCP.EdgeSet.diff graph_data.edges scc_edges in
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
  ) !processed_norms (EdgeExp.Map.empty, DCP.EdgeSet.empty)
  in
  EdgeExp.Map.iter (fun norm edge_set ->
    log "E(%a):\n" EdgeExp.pp norm;
    DCP.EdgeSet.iter (fun (src, edge_data, dst) ->
      let local_bound = Option.value_exn edge_data.bound_norm in
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
      let var_bound, cache = match norm with
      | EdgeExp.Access ((var, _), _) -> (
        let base_pvar = Option.value_exn (Var.get_pvar var) in

        if Pvar.Set.mem base_pvar graph_data.formals then (
          match PvarMap.find_opt base_pvar graph_data.type_map with
          | Some typ -> (match typ.desc with
            | Typ.Tint ikind -> if Typ.ikind_is_unsigned ikind then (
                (* for unsigned x: max(x, 0) => x *)
                norm, cache
              ) else (
                (* for signed x: max(x, 0) *)
                EdgeExp.Max [norm], cache
              )
            | _ -> L.(die InternalError)"[VB] Unexpected Lvar type!"
          )
          | None -> L.(die InternalError)"[VB] Lvar [%a] is not a local variable!" Pvar.pp_value base_pvar
        ) else (
          let cache = get_update_map norm graph_data.edges cache in
          let _, resets = EdgeExp.Map.find norm cache.updates in
          let increment_sum, cache = calculate_increment_sum (EdgeExp.Set.singleton norm) cache in
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

          (* Deduplicate and unpack nested max expressions
           * TODO: unpacking should be done only if certain conditions are met, should think about it later *)
          let max_args_unpacked = List.fold max_args ~init:[] ~f:(fun acc arg ->
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
          | 0 -> (
            L.(die InternalError)"[VB] Missing max() arguments for [%a]!" EdgeExp.pp norm
          )
          | 1 -> List.hd_exn max_args_unpacked
          | _ -> EdgeExp.Max max_args_unpacked 
          in
          (EdgeExp.add max_subexp increment_sum), cache
        )
      )
      | EdgeExp.Const Const.Cint const_norm -> (
        if IntLit.isnegative const_norm then EdgeExp.Max [norm], cache
        else norm, cache
      )
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
            log "Nested max arg: %a\n" EdgeExp.pp arg;
            let args = List.filter nested_args ~f:(fun x -> not (List.mem args_acc x ~equal:EdgeExp.equal)) in
            cache, args @ args_acc
          )
          | _ -> (cache, arg :: args_acc)
        ) in
        EdgeExp.Max args, cache
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

    match edge_data.bound with
    | EdgeExp.Inf when edge_data.computing_bound -> raise Exit
    | EdgeExp.Inf -> (
      (* Infinite recursion guard *)
      edge_data.computing_bound <- true;

      (* let cache = calculate_exec_cost edge_data cache in
      log "   [Execution cost] %a\n" EdgeExp.pp edge_data.execution_cost; *)

      match edge_data.bound_norm with
      | Some norm -> (
        log "   [Local bound] %a\n" EdgeExp.pp norm;
        let bound, cache = match norm with
        | EdgeExp.Access ((var, _), _) -> (
          let base_pvar = Option.value_exn (Var.get_pvar var) in
          if Pvar.Set.mem base_pvar graph_data.formals then norm, cache
          else (
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
            (EdgeExp.add increment_sum reset_sum), cache
          )
        )
        | EdgeExp.Const (Const.Cint _) -> (
          (* Non-loop edge, can be executed only once, const is always 1 *)
          norm, cache
        )
        | _ -> L.(die InternalError)"[Bound] Unsupported norm expression [%a]!" EdgeExp.pp norm
        in
        log "[Edge bound (%a)] %a\n" EdgeExp.pp norm EdgeExp.pp bound;
        edge_data.bound <- bound;
        cache
      )
      | None -> L.(die InternalError)"[Bound] edge has no bound norm!"
    )
    | _ -> cache

  and calculate_exec_cost (edge_data : DCP.EdgeData.t) cache =
    (* Sum together the cost of all functions called on this transition *)
    let cost_list, updated_cache = CallSiteSet.fold (fun (call_exp, loc) (cost_list, cache_acc) -> match call_exp with
      | EdgeExp.Call (_, proc_name, _, call_summary) -> (
        log "   [Call] %a : %a | %a\n" Procname.pp proc_name Domain.pp_summary call_summary Location.pp loc;

        (* Replace each argument with its variable bound (coarse overapproximation?) *)
        let call_cost, new_cache = EdgeExp.map_accesses call_summary.bound ~f:(fun argument_access cache_acc -> 
          let argument_bound, cache_acc = variable_bound (EdgeExp.Access argument_access) cache_acc in
          argument_bound, cache_acc
        ) cache_acc
        in
        call_cost :: cost_list, new_cache
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
    L.internal_error "[%a] Local bound could not be\
    determined for following edges:\n%s\n\
    Returning [Infinity]\n" Procname.pp proc_name culprits;
    EdgeExp.Inf, empty_cache
  ) else (
    log "[Local bounds]\n";
    let call_edges = DCP.EdgeSet.filter (fun (src, edge_data, dst) ->
      let local_bound = Option.value_exn edge_data.bound_norm in
      log "  %a -- %a -- %a\n" DCP.Node.pp src EdgeExp.pp local_bound DCP.Node.pp dst;
      EdgeExp.is_one local_bound && not (CallSiteSet.is_empty edge_data.calls)
    ) graph_data.edges
    in

    (* Calculate bound for all backedeges and sum them to get the total bound *)
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
        let _, edge_data, _ = edge in
        if DCP.EdgeData.is_backedge edge_data then (
          let cache = calculate_exec_cost edge_data cache in
          log "Edge cost: %a\n" EdgeExp.pp edge_data.execution_cost;
          let total_edge_cost = EdgeExp.mult edge_data.bound edge_data.execution_cost in
          (EdgeExp.add bound total_edge_cost), cache
        ) else bound, cache
      ) graph_data.edges (EdgeExp.zero, cache)
      in


      let exec_cost, cache = DCP.EdgeSet.fold (fun (_, edge_data, _) (total_exec_cost, cache) ->
        let cache = calculate_exec_cost edge_data cache in
        let cost = EdgeExp.add total_exec_cost edge_data.execution_cost in
        cost, cache
      ) call_edges (EdgeExp.zero, cache)
      in

      EdgeExp.add bound exec_cost, cache
    with Exit -> (
      EdgeExp.Inf, empty_cache
    )
  )
  in
  log "\n[Final bound] %a\n" EdgeExp.pp bound;
  
  let ret_type = Procdesc.get_ret_type proc_desc in
  let return_bound = match ret_type.desc with
  | Tint _ -> (
    log "[Return type] %a\n" Typ.(pp Pp.text) ret_type;
    (* let edge_list = DCP.EdgeSet.elements graph_data.edges in *)
    (* let _, return_edge, _ = List.find_exn edge_list ~f:(fun (_, edge, _) -> DCP.EdgeData.is_exit_edge edge) in *)
    let return_access = AccessPath.of_pvar (Procdesc.get_ret_var proc_desc) ret_type in
    (* log "[Return access] %a\n" AccessPath.pp return_access; *)
    (* let norm, _ = DC.Map.find (EdgeExp.Access return_access) return_edge.constraints in *)
    (* log "[Return norm] %a\n" EdgeExp.pp norm; *)
    let return_bound, _ = variable_bound (EdgeExp.Access return_access) cache in
    log "[Return bound] %a\n" EdgeExp.pp return_bound;
    Some return_bound
  )
  | _ -> None
  in

  log "Description:\n  signed x: max(x, 0) == [x]\n---------------------------------\n";
  let payload : EdgeExp.summary = {
    formal_map = FormalMap.make proc_desc;
    globals = PvarMap.empty;
    bound = bound;
    return_bound = return_bound;
  }
  in
  Analyzer.Payload.update_summary payload summary