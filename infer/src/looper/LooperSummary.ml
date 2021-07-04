(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
open LooperUtils

module F = Format
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
  src_node: DCP.Node.t;
  dst_node: DCP.Node.t;
  bound: EdgeExp.t;
  monotony_map: VariableMonotony.t AccessPathMap.t;
  calls: call list
}

and t = {
  formal_map: FormalMap.t;
  bounds: transition list;
  return_bound: EdgeExp.t option;
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
      DCP.Node.pp transition.src_node DCP.Node.pp transition.dst_node 
      EdgeExp.pp transition.bound;
      transition.bound
    ) 
    else if EdgeExp.is_one cost_of_calls then (
      let value = transition.bound in
      debug_log "[Edge cost] %a ---> %a: %a * %a = %a\n" 
      DCP.Node.pp transition.src_node DCP.Node.pp transition.dst_node 
      EdgeExp.pp transition.bound EdgeExp.pp cost_of_calls EdgeExp.pp value;
      value
    )
    else (
      let value = EdgeExp.add transition.bound (EdgeExp.mult transition.bound cost_of_calls) in
      debug_log "[Edge cost] %a ---> %a: %a + %a * %a = %a\n" 
      DCP.Node.pp transition.src_node DCP.Node.pp transition.dst_node
      EdgeExp.pp transition.bound EdgeExp.pp transition.bound EdgeExp.pp cost_of_calls EdgeExp.pp value;
      value
    )
    in

    total_edge_cost
  in

  let costs = List.map transitions ~f:calculate_transition_cost in
  if List.is_empty costs then EdgeExp.zero else List.reduce_exn costs ~f:EdgeExp.add


let instantiate (summary : t) args ~upper_bound ~lower_bound tenv active_prover cache =
  debug_log "\t[Determine monotonicity of argument expressions]\n";
  let arg_monotonicity_maps = List.map args ~f:(fun (arg_exp, _) -> 
    EdgeExp.determine_monotony_why3 arg_exp tenv active_prover
  )
  in

  let maximize_argument_exp arg_exp arg_monotonicity_map cache =
    (* Bound increases with the increasing value of this parameter.
      * Maximize value of the argument expression *)
    let evaluated_arg, (cache_acc : cache) = EdgeExp.map_accesses arg_exp ~f:(fun arg_access cache_acc ->
      let var_monotony = AccessPathMap.find arg_access arg_monotonicity_map in
      match var_monotony with
      | VariableMonotony.NonDecreasing -> (
        upper_bound (EdgeExp.Access arg_access) cache_acc
      )
      | VariableMonotony.NonIncreasing -> (
        lower_bound (EdgeExp.Access arg_access) cache_acc
      )
      | VariableMonotony.NotMonotonic -> assert(false);
    ) cache
    in
    evaluated_arg, cache_acc
  in


  let minimize_arg_exp arg_exp arg_monotonicity_map cache = 
    (* Bound decreases with the increasing value of this parameter.
      * Minimize value of the argument expression *)
    let evaluated_arg, cache_acc = EdgeExp.map_accesses arg_exp ~f:(fun arg_access cache_acc ->
      let var_monotony = AccessPathMap.find arg_access arg_monotonicity_map in
      match var_monotony with
      | VariableMonotony.NonDecreasing -> (
        lower_bound (EdgeExp.Access arg_access) cache_acc
      )
      | VariableMonotony.NonIncreasing -> (
        upper_bound (EdgeExp.Access arg_access) cache_acc
      )
      | VariableMonotony.NotMonotonic -> assert(false);
    ) cache
    in
    evaluated_arg, cache_acc
  in


  let evaluate_bound_argument formal_access_base formal_monotonicity arg_exp arg_monotonicity_map cache =           
    match formal_monotonicity with
    | VariableMonotony.NonDecreasing -> (
      (* Bound increases with the increasing value of this parameter.
        * Maximize value of the argument expression *)
      debug_log "[%a] Non decreasing, maximize arg value\n" AccessPath.pp_base formal_access_base;
      debug_log "[%a] Argument: %a\n" AccessPath.pp_base formal_access_base EdgeExp.pp arg_exp;
      let evaluated_arg, cache_acc = maximize_argument_exp arg_exp arg_monotonicity_map cache in
      debug_log "[%a] Evaluated argument: %a\n" AccessPath.pp_base formal_access_base EdgeExp.pp evaluated_arg;
      evaluated_arg, cache_acc
    )
    | VariableMonotony.NonIncreasing -> (
      (* Bound decreases with the increasing value of this parameter.
        * Minimize value of the argument expression *)
      debug_log "[%a] Non increasing, minimize arg value\n" AccessPath.pp_base formal_access_base;
      debug_log "[%a] Argument: %a\n" AccessPath.pp_base formal_access_base EdgeExp.pp arg_exp;
      let evaluated_arg, cache_acc = minimize_arg_exp arg_exp arg_monotonicity_map cache in
      debug_log "[%a] Evaluated argument: %a\n" AccessPath.pp_base formal_access_base EdgeExp.pp evaluated_arg;
      evaluated_arg, cache_acc
    )
    | VariableMonotony.NotMonotonic -> (
      debug_log "[%a] Not monotonic\n" AccessPath.pp_base formal_access_base;
      debug_log "[%a] Argument: %a\n" AccessPath.pp_base formal_access_base EdgeExp.pp arg_exp;
      assert(false);
    )
  in


  let instantiate_bound bound monotony_map cache = EdgeExp.map_accesses bound ~f:(fun formal_access cache_acc ->
    let formal_access_base : AccessPath.base = fst formal_access in
    let formal_idx = Option.value_exn (FormalMap.get_formal_index formal_access_base summary.formal_map) in
    let arg_exp = List.nth_exn args formal_idx |> fst in
    let arg_monotonicity_map = List.nth_exn arg_monotonicity_maps formal_idx in
    match AccessPathMap.find_opt formal_access monotony_map with
    | Some formal_monotony -> (
      evaluate_bound_argument formal_access_base formal_monotony arg_exp arg_monotonicity_map cache_acc
    )
    | None -> assert(false);
  ) cache
  in


  let rec instantiate_transition_summary (transition : transition) cache =
    let bound, cache = if EdgeExp.is_const transition.bound then transition.bound, cache
    else instantiate_bound transition.bound transition.monotony_map cache
    in

    let calls, cache = List.fold transition.calls ~f:(fun (calls_acc, cache) (call : call) ->
      let call_transitions, cache = List.fold call.bounds ~init:([], cache)
      ~f:(fun (call_transitions, cache) (call_transition : transition) ->
        let instantiated_call_transition, cache = instantiate_transition_summary call_transition cache in
        instantiated_call_transition :: call_transitions, cache
      )
      in
      { call with bounds = call_transitions } :: calls_acc, cache
    ) ~init:([], cache)
    in
    let transition = { transition with 
      bound;
      calls;
      monotony_map = EdgeExp.determine_monotony_why3 bound tenv active_prover
    } in
    transition, cache
  in

  let transitions, new_cache = List.fold summary.bounds ~f:(fun (transitions, cache) (transition : transition) ->
    let instantiated_transition, cache = instantiate_transition_summary transition cache in
    instantiated_transition :: transitions, cache
  ) ~init:([], cache)
  in
  transitions, new_cache


let pp fmt (summary : t) = EdgeExp.pp fmt (total_bound summary.bounds)


module TreeGraph = struct
  module Node = struct
    type t = 
    | CallNode of Procname.t * Location.t
    | TransitionNode of DCP.Node.t * EdgeExp.t * DCP.Node.t
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
      let label = F.asprintf "{%a --> %a}\n%a" DCP.Node.pp src DCP.Node.pp dst EdgeExp.pp bound in
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