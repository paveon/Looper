(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
open LooperUtils

module L = Logging
module F = Format
module LTS = LabeledTransitionSystem
module DCP = DifferenceConstraintProgram


let debug_log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.fprintf (List.hd_exn !debug_fmt) fmt


module Increments = Caml.Set.Make(struct
  type nonrec t = DCP.E.t * IntLit.t
  [@@deriving compare]
end)

module Decrements = Caml.Set.Make(struct
  type nonrec t = DCP.E.t * IntLit.t
  [@@deriving compare]
end)

module Resets = Caml.Set.Make(struct
  type nonrec t = DCP.E.t * EdgeExp.t * IntLit.t
  [@@deriving compare]
end)

type norm_updates = {
   increments: Increments.t;
   decrements: Decrements.t;
   resets: Resets.t
}

let empty_updates = { 
  increments = Increments.empty;
  decrements = Decrements.empty;
  resets = Resets.empty;
}

type cache = {
  updates: norm_updates EdgeExp.Map.t;
  variable_bounds: EdgeExp.t EdgeExp.Map.t;
  lower_bounds: EdgeExp.t EdgeExp.Map.t;
  reset_chains: ResetGraph.Chain.Set.t EdgeExp.Map.t;
  positivity: bool EdgeExp.Map.t;
}

let empty_cache = { 
  updates = EdgeExp.Map.empty; 
  variable_bounds = EdgeExp.Map.empty;
  lower_bounds = EdgeExp.Map.empty;
  reset_chains = EdgeExp.Map.empty;
  positivity = EdgeExp.Map.empty;
}


type call = {
  name: Procname.t;
  loc: Location.t;
  bounds: transition list;
}

and transition = {
  src_node: LTS.Node.t;
  dst_node: LTS.Node.t;
  bound: EdgeExp.t;
  monotony_map: Monotonicity.t AccessExpressionMap.t;
  calls: call list
}

and t = {
  formal_map: FormalMap.t;
  bounds: transition list;
  return_bound: EdgeExp.t option;
  formal_bounds: (EdgeExp.t * EdgeExp.t) LooperUtils.AccessExpressionMap.t
}


let total_bound transitions =
  let rec calculate_transition_cost transition =
    let cost_of_calls = List.fold transition.calls ~init:EdgeExp.zero ~f:(fun bound_sum (call : call) ->
      List.fold call.bounds ~f:(fun sum (call_transition : transition) ->
        EdgeExp.add sum (calculate_transition_cost call_transition)
      ) ~init:bound_sum
    )
    in
    let total_edge_cost = if EdgeExp.is_zero cost_of_calls then (
      debug_log "[Edge cost] %a ---> %a: %a\n" 
      LTS.Node.pp transition.src_node LTS.Node.pp transition.dst_node 
      EdgeExp.pp transition.bound;
      transition.bound
    ) 
    else if EdgeExp.is_one cost_of_calls then (
      let value = transition.bound in
      debug_log "[Edge cost] %a ---> %a: %a * %a = %a\n" 
      LTS.Node.pp transition.src_node LTS.Node.pp transition.dst_node 
      EdgeExp.pp transition.bound EdgeExp.pp cost_of_calls EdgeExp.pp value;
      value
    )
    else (
      let value = EdgeExp.add transition.bound (EdgeExp.mult transition.bound cost_of_calls) in
      debug_log "[Edge cost] %a ---> %a: %a + %a * %a = %a\n" 
      LTS.Node.pp transition.src_node LTS.Node.pp transition.dst_node
      EdgeExp.pp transition.bound EdgeExp.pp transition.bound EdgeExp.pp cost_of_calls EdgeExp.pp value;
      value
    )
    in

    total_edge_cost
  in

  let costs = List.map transitions ~f:calculate_transition_cost in
  if List.is_empty costs then EdgeExp.zero else List.reduce_exn costs ~f:EdgeExp.add


let instantiate (summary : t) args ~upper_bound ~lower_bound tenv active_prover cache =
  let maximize_argument_exp arg_exp arg_monotonicity_map cache =
    (* Bound increases with the increasing value of this parameter.
      * Maximize value of the argument expression *)
    let evaluated_arg, (cache_acc : cache) = EdgeExp.map_accesses arg_exp ~f:(fun arg_access cache_acc ->
      let var_monotony = AccessExpressionMap.find arg_access arg_monotonicity_map in
      match var_monotony with
      | Monotonicity.NonDecreasing -> (
        upper_bound (EdgeExp.Access arg_access) cache_acc
      )
      | Monotonicity.NonIncreasing -> (
        lower_bound (EdgeExp.Access arg_access) cache_acc
      )
      | Monotonicity.NotMonotonic -> assert(false);
    ) cache
    in
    evaluated_arg, cache_acc
  in


  let minimize_arg_exp arg_exp arg_monotonicity_map cache = 
    (* Bound decreases with the increasing value of this parameter.
      * Minimize value of the argument expression *)
    let evaluated_arg, cache_acc = EdgeExp.map_accesses arg_exp ~f:(fun arg_access cache_acc ->
      let var_monotony = AccessExpressionMap.find arg_access arg_monotonicity_map in
      match var_monotony with
      | Monotonicity.NonDecreasing -> (
        lower_bound (EdgeExp.Access arg_access) cache_acc
      )
      | Monotonicity.NonIncreasing -> (
        upper_bound (EdgeExp.Access arg_access) cache_acc
      )
      | Monotonicity.NotMonotonic -> assert(false);
    ) cache
    in
    evaluated_arg, cache_acc
  in


  let evaluate_bound_argument formal_access_base formal_monotonicity arg_exp arg_monotonicity_map cache =           
    match formal_monotonicity with
    | Monotonicity.NonDecreasing -> (
      (* Bound increases with the increasing value of this parameter.
        * Maximize value of the argument expression *)
      debug_log "Formal monotonicity: non-decreasing@,Goal: maximize argument value@,";
      debug_log "Argument: %a@," EdgeExp.pp arg_exp;
      let evaluated_arg, cache_acc = maximize_argument_exp arg_exp arg_monotonicity_map cache in
      debug_log "Evaluated argument: %a@," EdgeExp.pp evaluated_arg;
      evaluated_arg, cache_acc
    )
    | Monotonicity.NonIncreasing -> (
      (* Bound decreases with the increasing value of this parameter.
        * Minimize value of the argument expression *)
      debug_log "Formal monotonicity: non-increasing@,Goal: minimize argument value@,";
      debug_log "Argument: %a@," EdgeExp.pp arg_exp;
      let evaluated_arg, cache_acc = minimize_arg_exp arg_exp arg_monotonicity_map cache in
      debug_log "Evaluated argument: %a@," EdgeExp.pp evaluated_arg;
      evaluated_arg, cache_acc
    )
    | Monotonicity.NotMonotonic -> (
      debug_log "Formal monotonicity: not monotonic@,";
      debug_log "Argument: %a@," EdgeExp.pp arg_exp;
      assert(false);
    )
  in


  let instantiate_bound bound formals_monotonicity_map arg_monotonicity_maps cache =
    debug_log "@[<v2>[Instantiating bound] %a@," EdgeExp.pp bound;
    debug_log "@[<v2>[Formals monotonicity map]@,";
    AccessExpressionMap.iter (fun access monotonicity ->
      match monotonicity with
      | Monotonicity.NonDecreasing -> debug_log "%a: Non-decreasing@," HilExp.AccessExpression.pp access
      | Monotonicity.NonIncreasing -> debug_log "%a: Non-increasing@," HilExp.AccessExpression.pp access
      | Monotonicity.NotMonotonic -> debug_log "%a: Not monotonic@," HilExp.AccessExpression.pp access
    ) formals_monotonicity_map;
    debug_log "@]@,";

    debug_log "@[<v2>[Min-maxing formal bound variables]@,";
    let instantiated_bound = EdgeExp.map_accesses bound ~f:(fun formal_access cache_acc ->
      debug_log "Mapping formal access: %a@," HilExp.AccessExpression.pp formal_access;
      let formal_access_base = HilExp.AccessExpression.get_base formal_access in
      let formal_idx = Option.value_exn (FormalMap.get_formal_index formal_access_base summary.formal_map) in
      let arg_exp, arg_typ = List.nth_exn args formal_idx in
      let arg_monotonicity_map_opt = List.nth_exn arg_monotonicity_maps formal_idx in
      match arg_monotonicity_map_opt with
      | Some arg_monotonicity_map -> (
        match AccessExpressionMap.find_opt formal_access formals_monotonicity_map with
        | Some formal_monotony -> (
          evaluate_bound_argument formal_access_base formal_monotony arg_exp arg_monotonicity_map cache_acc
        )
        | None -> L.die InternalError 
          "[Summary Instantiation] Missing monotonicity \
          information for formal parameter: %a" HilExp.AccessExpression.pp formal_access;
      )
      | None when EdgeExp.is_const arg_exp -> arg_exp, cache
      | None -> (
        (* Not an integer argument, should not appear in a bound expression *)
        L.die InternalError 
          "Non-integer argument '%a' substitution in bound expression. Typ: %a"
          EdgeExp.pp arg_exp Typ.(pp Pp.text) arg_typ;
      )
    ) cache
    in
    debug_log "@]@,";
    instantiated_bound
  in


  let rec instantiate_transition_summary (transition : transition) arg_monotonicity_maps cache =
    debug_log "@[<v2>[Instantiating transition summary] %a ---> %a@," 
      LTS.Node.pp transition.src_node
      LTS.Node.pp transition.dst_node;
    
    debug_log "Summary TB: %a@," EdgeExp.pp transition.bound;
    let bound, cache = if EdgeExp.is_const transition.bound then (
      debug_log "Constant TB, skipping instantiation...@,";
      transition.bound, cache
    )
    else (
      instantiate_bound transition.bound transition.monotony_map arg_monotonicity_maps cache
    )
    in

    let bound_monotony_map = if EdgeExp.is_const bound then AccessExpressionMap.empty
    else EdgeExp.determine_monotonicity bound tenv active_prover
    in

    let calls, cache = List.fold transition.calls ~f:(fun (calls_acc, cache) (call : call) ->
      let call_transitions, cache = List.fold call.bounds ~init:([], cache)
      ~f:(fun (call_transitions, cache) (call_transition : transition) ->
        let instantiated_call_transition, cache = 
          instantiate_transition_summary call_transition arg_monotonicity_maps cache
        in
        instantiated_call_transition :: call_transitions, cache
      )
      in
      { call with bounds = call_transitions } :: calls_acc, cache
    ) ~init:([], cache)
    in
    let transition = { transition with 
      bound;
      calls;
      monotony_map = bound_monotony_map
    } 
    in
    debug_log "@]@,";
    transition, cache
  in

  debug_log "Summary transition count: %d@," (List.length summary.bounds);

  let transitions, new_cache = if List.is_empty summary.bounds then [], cache
  else (
    debug_log "@[<v2>[Determine monotonicity of argument expressions]@,";
    let arg_monotonicity_maps = List.map args ~f:(fun (arg_exp, arg_typ) ->
      if Typ.is_int arg_typ && (EdgeExp.is_const arg_exp |> not)
      then Some (EdgeExp.determine_monotonicity arg_exp tenv active_prover)
      else None
    )
    in
    debug_log "@]@,Monotonicities established@,";

    debug_log "Summary transition count: %d@," (List.length summary.bounds);
    List.fold summary.bounds ~f:(fun (transitions, cache) (transition : transition) ->
      let instantiated_transition, cache = 
        instantiate_transition_summary transition arg_monotonicity_maps cache
      in
      instantiated_transition :: transitions, cache
    ) ~init:([], cache)
  )
  in
  debug_log "Summary instantiated";
  transitions, new_cache


(* let pp fmt (summary : t) = EdgeExp.pp fmt (total_bound summary.bounds) *)
let pp fmt (summary : t) = ()


module TreeGraph = struct
  module Node = struct
    type t = 
    | CallNode of Procname.t * Location.t
    | TransitionNode of LTS.Node.t * EdgeExp.t * LTS.Node.t
    [@@deriving compare]

    let hash x = Hashtbl.hash_param 100 100 x
    let equal = [%compare.equal: t]
  end
  
  module Edge = struct
    type t = unit [@@deriving compare]
    let hash = Hashtbl.hash
    let equal = [%compare.equal : t]
    let default = ()
    end
  include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(Edge)
  include DefaultDot

  let edge_attributes : E.t -> 'a list = fun _ -> [`Label ""; `Color 4711]
  let vertex_attributes : V.t -> 'a list = fun node -> (
    match node with
    | CallNode (procname, loc) -> (
      let label = F.asprintf "%a: %a" Procname.pp procname Location.pp loc in
      let color : int = 0xFF0000 in
      [ `Shape `Box; `Label label; `Style `Rounded; `Color color ]
    )
    | TransitionNode (src, bound, dst) -> (
      let label = F.asprintf "{%a --> %a}\n%a" LTS.Node.pp src LTS.Node.pp dst EdgeExp.pp bound in
      let color : int = 0x0000FF in
      [ `Shape `Box; `Label label; `Color color; `Height 1.0]
    )
  )
  let vertex_name : V.t -> string = fun vertex -> string_of_int (Node.hash vertex)

  module Map = Caml.Map.Make(Node)
end


module TreeGraph_Dot = Graph.Graphviz.Dot(TreeGraph)


let to_graph (summary : t) procname loc =
  let graph = TreeGraph.create () in

  let rec construct_subtree root transitions =
    List.iter transitions ~f:(fun trans ->
      let transition_node = TreeGraph.Node.TransitionNode (trans.src_node, trans.bound, trans.dst_node) in
      TreeGraph.add_vertex graph transition_node;
      TreeGraph.add_edge graph root transition_node;
      List.iter trans.calls ~f:(fun call ->
        let call_node = TreeGraph.Node.CallNode (call.name, call.loc) in
        TreeGraph.add_vertex graph call_node;
        TreeGraph.add_edge graph transition_node call_node;
        construct_subtree call_node call.bounds
      )
    )
  in

  let root_node = TreeGraph.Node.CallNode (procname, loc) in
  TreeGraph.add_vertex graph root_node;
  construct_subtree root_node summary.bounds;
  graph