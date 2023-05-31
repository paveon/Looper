(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
open LooperUtils
module L = Logging
module F = Format
module LTS = LabeledTransitionSystem
module DCP = DifferenceConstraintProgram

module Increments = Caml.Set.Make (struct
  type nonrec t = DCP.E.t * IntLit.t [@@deriving compare]
end)

module Decrements = Caml.Set.Make (struct
  type nonrec t = DCP.E.t * IntLit.t [@@deriving compare]
end)

module Resets = Caml.Set.Make (struct
  type nonrec t = DCP.E.t * EdgeExp.T.t * IntLit.t [@@deriving compare]
end)

type norm_updates = {increments: Increments.t; decrements: Decrements.t; resets: Resets.t}

let empty_updates =
  {increments= Increments.empty; decrements= Decrements.empty; resets= Resets.empty}


type cache =
  { updates: norm_updates EdgeExp.Map.t
  ; upper_bounds: EdgeExp.T.t EdgeExp.Map.t
  ; lower_bounds: EdgeExp.T.t EdgeExp.Map.t
  ; reset_chains: ResetGraph.Chain.Set.t EdgeExp.Map.t
  ; positivity: bool EdgeExp.Map.t }

let empty_cache =
  { updates= EdgeExp.Map.empty
  ; upper_bounds= EdgeExp.Map.empty
  ; lower_bounds= EdgeExp.Map.empty
  ; reset_chains= EdgeExp.Map.empty
  ; positivity= EdgeExp.Map.empty }


type model_call =
  { name: Procname.t
  ; loc: Location.t
  ; bound: EdgeExp.T.t
  ; monotonicity_map: Monotonicity.t AccessExpressionMap.t }

type real_call = {name: Procname.t; loc: Location.t; bounds: transition list}

and call = ModelCall of model_call | RealCall of real_call

and transition =
  { src_node: LTS.Node.t
  ; dst_node: LTS.Node.t
  ; bound: EdgeExp.T.t
  ; monotony_map: Monotonicity.t AccessExpressionMap.t
  ; calls: call list
  ; backedge: bool }

type t =
  { formal_map: FormalMap.t
  ; bounds: transition list
  ; return_bound: EdgeExp.ValuePair.t option
  ; formal_bounds: EdgeExp.ValuePair.pair EdgeExp.Map.t }

module Model = struct
  type t =
    { name: string
    ; return_bound: EdgeExp.ValuePair.t option
    ; monotonicity_map: Monotonicity.t IntMap.t
    ; side_effects: EdgeExp.ValuePair.pair EdgeExp.Map.t
    ; compute_complexity:
           (EdgeExp.T.t * Typ.t) list
        -> cache
        -> variable_bound:(bound_type:BoundType.t -> EdgeExp.T.t -> cache -> EdgeExp.T.t * cache)
        -> EdgeExp.T.t * cache }

  (* let pp fmt model = F.fprintf fmt "complexity: %a" EdgeExp.ValuePair.pp model.complexity *)
end

type model_summary = Real of t | Model of Model.t

let total_bound transitions =
  let rec calculate_transition_cost transition =
    let cost_of_calls =
      List.fold transition.calls ~init:EdgeExp.zero ~f:(fun bound_sum call ->
          match call with
          | RealCall real_call ->
              List.fold real_call.bounds
                ~f:(fun sum (call_transition : transition) ->
                  EdgeExp.add sum (calculate_transition_cost call_transition) )
                ~init:bound_sum
          | ModelCall model_call ->
              EdgeExp.add bound_sum model_call.bound )
    in
    let calls_mult = EdgeExp.mult transition.bound cost_of_calls in
    let total_edge_cost =
      if transition.backedge then EdgeExp.add transition.bound calls_mult else calls_mult
    in
    (* let total_edge_cost =
         if EdgeExp.is_zero cost_of_calls then
           (* debug_log "[Edge cost] %a ---> %a: %a\n" LTS.Node.pp transition.src_node LTS.Node.pp
              transition.dst_node EdgeExp.pp transition.bound ; *)
           transition.bound
         else if EdgeExp.is_one cost_of_calls then
           let value = transition.bound in
           (* debug_log "[Edge cost] %a ---> %a: %a * %a = %a\n" LTS.Node.pp transition.src_node
              LTS.Node.pp transition.dst_node EdgeExp.pp transition.bound EdgeExp.pp cost_of_calls
              EdgeExp.pp value ; *)
           value
         else
           (* TODO: How should we properly calculate this to get accurate bound reflecting
              back-edge execution count? *)
           (* let value = EdgeExp.add transition.bound (EdgeExp.mult transition.bound cost_of_calls) in *)
           let value = EdgeExp.mult transition.bound cost_of_calls in
           (* debug_log "[Edge cost] %a ---> %a: %a + %a * %a = %a\n" LTS.Node.pp transition.src_node
              LTS.Node.pp transition.dst_node EdgeExp.pp transition.bound EdgeExp.pp transition.bound
              EdgeExp.pp cost_of_calls EdgeExp.pp value ; *)
           value
       in *)
    total_edge_cost
  in
  let costs = List.map transitions ~f:calculate_transition_cost in
  if List.is_empty costs then EdgeExp.zero
  else List.reduce_exn costs ~f:EdgeExp.add |> EdgeExp.simplify


let instantiate (summary : model_summary) proc_name args loc ~variable_bound tenv active_prover
    cache =
  let arg_monotonicity_maps : Monotonicity.t AccessExpressionMap.t IntMap.t ref =
    ref IntMap.empty
  in
  let get_formal_idx formal_access =
    match summary with
    | Real real_summary ->
        let formal_access_base = HilExp.AccessExpression.get_base formal_access in
        Option.value_exn (FormalMap.get_formal_index formal_access_base real_summary.formal_map)
    | Model _ ->
        assert false
  in
  (* List.iteri args ~f:(fun arg_idx (arg_exp, arg_typ) ->
     if EdgeExp.is_integer_type arg_typ && EdgeExp.is_const arg_exp |> not then
       let monotonicity = EdgeExp.determine_monotonicity arg_exp tenv active_prover in
       let updated_map = IntMap.add arg_idx monotonicity !arg_monotonicity_maps in
       arg_monotonicity_maps := updated_map;
     ); *)

  (* let arg_monotonicity_maps =
       List.map args ~f:(fun (arg_exp, arg_typ) ->
           if EdgeExp.is_integer_type arg_typ && EdgeExp.is_const arg_exp |> not then
             Some (EdgeExp.determine_monotonicity arg_exp tenv active_prover)
           else None )
     in *)
  let maximize_argument_exp arg_exp arg_monotonicity_map cache =
    (* Bound increases with the increasing value of this parameter.
       * Maximize value of the argument expression *)
    let evaluated_arg, (cache_acc : cache) =
      EdgeExp.map_accesses arg_exp ~init:cache ~f:(fun arg_access cache_acc ->
          let var_monotony = AccessExpressionMap.find arg_access arg_monotonicity_map in
          match var_monotony with
          | Monotonicity.NonDecreasing ->
              variable_bound ~bound_type:BoundType.Upper (EdgeExp.T.Access arg_access) cache_acc
          | Monotonicity.NonIncreasing ->
              variable_bound ~bound_type:BoundType.Lower (EdgeExp.T.Access arg_access) cache_acc
          | Monotonicity.NotMonotonic ->
              assert false )
    in
    (EdgeExp.flatten_min_max evaluated_arg, cache_acc)
  in
  let minimize_arg_exp arg_exp arg_monotonicity_map cache =
    (* Bound decreases with the increasing value of this parameter.
       * Minimize value of the argument expression *)
    let evaluated_arg, cache_acc =
      EdgeExp.map_accesses arg_exp ~init:cache ~f:(fun arg_access cache_acc ->
          let var_monotony = AccessExpressionMap.find arg_access arg_monotonicity_map in
          match var_monotony with
          | Monotonicity.NonDecreasing ->
              variable_bound ~bound_type:BoundType.Lower (EdgeExp.T.Access arg_access) cache_acc
          | Monotonicity.NonIncreasing ->
              variable_bound ~bound_type:BoundType.Upper (EdgeExp.T.Access arg_access) cache_acc
          | Monotonicity.NotMonotonic ->
              assert false )
    in
    (EdgeExp.flatten_min_max evaluated_arg, cache_acc)
  in
  let evaluate_bound_argument formal_monotonicity arg_exp arg_monotonicity_map cache =
    match formal_monotonicity with
    | Monotonicity.NonDecreasing ->
        (* Bound increases with the increasing value of this parameter.
           * Maximize value of the argument expression *)
        debug_log "Formal monotonicity: non-decreasing@,Goal: maximize argument value@," ;
        debug_log "Argument: %a@," EdgeExp.pp arg_exp ;
        let evaluated_arg, cache_acc = maximize_argument_exp arg_exp arg_monotonicity_map cache in
        debug_log "Evaluated argument: %a@," EdgeExp.pp evaluated_arg ;
        (evaluated_arg, cache_acc)
    | Monotonicity.NonIncreasing ->
        (* Bound decreases with the increasing value of this parameter.
           * Minimize value of the argument expression *)
        debug_log "Formal monotonicity: non-increasing@,Goal: minimize argument value@," ;
        debug_log "Argument: %a@," EdgeExp.pp arg_exp ;
        let evaluated_arg, cache_acc = minimize_arg_exp arg_exp arg_monotonicity_map cache in
        debug_log "Evaluated argument: %a@," EdgeExp.pp evaluated_arg ;
        (evaluated_arg, cache_acc)
    | Monotonicity.NotMonotonic ->
        debug_log "Formal monotonicity: not monotonic@," ;
        debug_log "Argument: %a@," EdgeExp.pp arg_exp ;
        assert false
  in
  let instantiate_bound bound formals_monotonicity_map cache =
    debug_log "@[<v2>[Instantiating bound] %a@," EdgeExp.pp bound ;
    debug_log "@[<v2>[Formals monotonicity map]@," ;
    AccessExpressionMap.iter
      (fun access monotonicity ->
        match monotonicity with
        | Monotonicity.NonDecreasing ->
            debug_log "%a: Non-decreasing@," HilExp.AccessExpression.pp access
        | Monotonicity.NonIncreasing ->
            debug_log "%a: Non-increasing@," HilExp.AccessExpression.pp access
        | Monotonicity.NotMonotonic ->
            debug_log "%a: Not monotonic@," HilExp.AccessExpression.pp access )
      formals_monotonicity_map ;
    debug_log "@]@," ;
    debug_log "@[<v2>[Min-maxing formal bound variables]@," ;
    let substitute_access formal_access cache =
      let var, _ = HilExp.AccessExpression.get_base formal_access in
      if Var.is_global var then (
        debug_log "Global access: %a, skipping@," HilExp.AccessExpression.pp formal_access ;
        (EdgeExp.T.Access formal_access, cache) )
      else (
        (* Substitute the LB/UB of the argument into the bound formal access
           based on the formal and argument monotonicities *)
        debug_log "Mapping formal access: %a@," HilExp.AccessExpression.pp formal_access ;
        let formal_idx = get_formal_idx formal_access in
        let arg_exp, arg_typ = List.nth_exn args formal_idx in
        if EdgeExp.is_const arg_exp then
          (* The substituted argument itself is constant,
             no need to evaluate anything based on monotonicity *)
          (arg_exp, cache)
        else if not (EdgeExp.is_integer_type arg_typ) then
          (* TODO: Need to fix this. Not sure how, maybe catch the exception
             and return INF as instantiated bound? *)
          L.die InternalError
            "Non-integer '%a' argument '%a' substitution in bound expression, ignoring"
            Typ.(pp Pp.text)
            arg_typ EdgeExp.pp arg_exp
        else
          (* Determine monotonicities on-demand if needed *)
          let arg_monotonicity_map =
            match IntMap.find_opt formal_idx !arg_monotonicity_maps with
            | Some map ->
                map
            | None ->
                let monotonicity = EdgeExp.determine_monotonicity arg_exp tenv active_prover in
                let updated_map = IntMap.add formal_idx monotonicity !arg_monotonicity_maps in
                arg_monotonicity_maps := updated_map ;
                monotonicity
          in
          match AccessExpressionMap.find_opt formal_access formals_monotonicity_map with
          | Some formal_monotonicity ->
              evaluate_bound_argument formal_monotonicity arg_exp arg_monotonicity_map cache
          | None ->
              (* TODO: Here also? Catch exception and deal with it by INF bound? *)
              L.die InternalError
                "[Summary Instantiation] Missing monotonicity information for formal parameter: %a"
                HilExp.AccessExpression.pp formal_access )
    in
    try
      let instantiated_bound, cache =
        if EdgeExp.is_const bound then (bound, cache)
        else EdgeExp.map_accesses bound ~init:cache ~f:substitute_access
      in
      let instantiated_bound = EdgeExp.flatten_min_max instantiated_bound in
      debug_log "Instantiated TB: %a@," EdgeExp.pp instantiated_bound ;
      debug_log "@]@]@," ;
      (instantiated_bound, cache)
    with error ->
      debug_log "@]@]@," ;
      raise error
  in
  let rec instantiate_transition_summary (transition : transition) cache =
    debug_log "@[<v2>[Instantiating transition summary] %a ---> %a@," LTS.Node.pp
      transition.src_node LTS.Node.pp transition.dst_node ;
    debug_log "Summary TB: %a@," EdgeExp.pp transition.bound ;
    try
      let bound, cache =
        if EdgeExp.is_const transition.bound then (
          debug_log "Constant TB, skipping instantiation...@," ;
          (transition.bound, cache) )
        else instantiate_bound transition.bound transition.monotony_map cache
      in
      let bound_monotony_map =
        if EdgeExp.is_const bound then AccessExpressionMap.empty
        else EdgeExp.determine_monotonicity bound tenv active_prover
      in
      let instantiate_real_call (real_call : real_call) cache =
        let call_transitions, cache =
          List.fold real_call.bounds ~init:([], cache)
            ~f:(fun (call_transitions, cache) (call_transition : transition) ->
              let instantiated_call_transition, cache =
                instantiate_transition_summary call_transition cache
              in
              (instantiated_call_transition :: call_transitions, cache) )
        in
        (RealCall {real_call with bounds= call_transitions}, cache)
      in
      let instantiate_model_call (model_call : model_call) cache =
        let bound, cache =
          if EdgeExp.is_const model_call.bound then (model_call.bound, cache)
          else instantiate_bound model_call.bound model_call.monotonicity_map cache
          (* if EdgeExp.is_const model_call.bound then (model_call.bound, cache)
             else instantiate_model_bound model_call.bound model_call.monotonicity_map cache *)
        in
        (ModelCall {model_call with bound}, cache)
      in
      let instantiate_transition_call (calls_acc, cache) call =
        let instantiated_call, cache =
          match call with
          | RealCall real_call ->
              instantiate_real_call real_call cache
          | ModelCall model_call ->
              instantiate_model_call model_call cache
        in
        (instantiated_call :: calls_acc, cache)
      in
      let calls, cache =
        List.fold transition.calls ~f:instantiate_transition_call ~init:([], cache)
      in
      let transition = {transition with bound; calls; monotony_map= bound_monotony_map} in
      debug_log "@]@," ;
      (transition, cache)
    with error ->
      (* let stack = Printexc.get_backtrace () in *)
      (* debug_log "[Analysis Exception]\n%a\n%s" Exn.pp error stack ; *)
      debug_log "[Analysis Exception] %a@," Exn.pp error ;
      debug_log "Failed to instantiate summary, assuming INF bound" ;
      let transition =
        {transition with bound= EdgeExp.T.Inf; calls= []; monotony_map= AccessExpressionMap.empty}
      in
      debug_log "@]@," ;
      (transition, cache)
  in
  match summary with
  | Real real_summary ->
      debug_log "Summary transition count: %d@," (List.length real_summary.bounds) ;
      let transitions, new_cache =
        if List.is_empty real_summary.bounds then ([], cache)
        else (
          debug_log "Summary transition count: %d@," (List.length real_summary.bounds) ;
          List.fold real_summary.bounds
            ~f:(fun (transitions, cache) (transition : transition) ->
              let instantiated_transition, cache =
                instantiate_transition_summary transition cache
              in
              (instantiated_transition :: transitions, cache) )
            ~init:([], cache) )
      in
      debug_log "Summary instantiated" ;
      let instantiated_call = RealCall {name= proc_name; loc; bounds= transitions} in
      (instantiated_call, new_cache)
  | Model model_summary ->
      let complexity, cache = model_summary.compute_complexity args cache ~variable_bound in
      let monotonicity_map = EdgeExp.determine_monotonicity complexity tenv active_prover in
      let instantiated_call =
        ModelCall {name= proc_name; loc; bound= complexity; monotonicity_map}
      in
      (instantiated_call, cache)


(* let pp fmt (summary : t) = EdgeExp.pp fmt (total_bound summary.bounds) *)
let pp fmt (summary : t) = ()

module TreeGraph = struct
  module Node = struct
    type t =
      | CallNode of Procname.t * Location.t
      | TransitionNode of LTS.Node.t * EdgeExp.T.t * LTS.Node.t
    [@@deriving compare]

    let hash x = Hashtbl.hash_param 100 100 x

    let equal = [%compare.equal: t]
  end

  module Edge = struct
    type t = unit [@@deriving compare]

    let hash = Hashtbl.hash

    let equal = [%compare.equal: t]

    let default = ()
  end

  include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Node) (Edge)
  include DefaultDot

  let edge_attributes : E.t -> 'a list = fun _ -> [`Label ""; `Color 4711]

  let vertex_attributes : V.t -> 'a list =
   fun node ->
    match node with
    | CallNode (procname, loc) ->
        let label = F.asprintf "%a: %a" Procname.pp procname Location.pp loc in
        let color : int = 0xFF0000 in
        [`Shape `Box; `Label label; `Style `Rounded; `Color color]
    | TransitionNode (src, bound, dst) ->
        let label = F.asprintf "{%a --> %a}\n%a" LTS.Node.pp src LTS.Node.pp dst EdgeExp.pp bound in
        let color : int = 0x0000FF in
        [`Shape `Box; `Label label; `Color color; `Height 1.0]


  let vertex_name : V.t -> string = fun vertex -> string_of_int (Node.hash vertex)

  module Map = Caml.Map.Make (Node)
end

module TreeGraph_Dot = Graph.Graphviz.Dot (TreeGraph)

let to_graph (summary : t) procname loc =
  let graph = TreeGraph.create () in
  let rec construct_subtree root transitions =
    List.iter transitions ~f:(fun trans ->
        let transition_node =
          TreeGraph.Node.TransitionNode (trans.src_node, trans.bound, trans.dst_node)
        in
        TreeGraph.add_vertex graph transition_node ;
        TreeGraph.add_edge graph root transition_node ;
        List.iter trans.calls ~f:(fun call ->
            match call with
            | RealCall real_call ->
                let call_node = TreeGraph.Node.CallNode (real_call.name, real_call.loc) in
                TreeGraph.add_vertex graph call_node ;
                TreeGraph.add_edge graph transition_node call_node ;
                construct_subtree call_node real_call.bounds
            | ModelCall model_call ->
                let call_node = TreeGraph.Node.CallNode (model_call.name, model_call.loc) in
                TreeGraph.add_vertex graph call_node ;
                TreeGraph.add_edge graph transition_node call_node ;
                construct_subtree call_node [] ) )
  in
  let root_node = TreeGraph.Node.CallNode (procname, loc) in
  TreeGraph.add_vertex graph root_node ;
  construct_subtree root_node summary.bounds ;
  graph
