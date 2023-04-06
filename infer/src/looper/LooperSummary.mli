(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
open LooperUtils

module F = Format
module LTS = LabeledTransitionSystem
module DCP = DifferenceConstraintProgram


module Increments : Caml.Set.S with type elt = DCP.E.t * IntLit.t

module Decrements : Caml.Set.S with type elt = DCP.E.t * IntLit.t

module Resets : Caml.Set.S with type elt = DCP.E.t * EdgeExp.T.t * IntLit.t


type norm_updates = {
   increments: Increments.t;
   decrements: Decrements.t;
   resets: Resets.t
}

val empty_updates : norm_updates


type cache = {
  updates: norm_updates EdgeExp.Map.t;
  upper_bounds: EdgeExp.T.t EdgeExp.Map.t;
  lower_bounds: EdgeExp.T.t EdgeExp.Map.t;
  reset_chains: ResetGraph.Chain.Set.t EdgeExp.Map.t;
  positivity: bool EdgeExp.Map.t;
}

val empty_cache : cache


type call = {
  name: Procname.t;
  loc: Location.t;
  bounds: transition list;
}

and transition = {
  src_node: LTS.Node.t;
  dst_node: LTS.Node.t;
  bound: EdgeExp.T.t;
  monotony_map: Monotonicity.t AccessExpressionMap.t;
  calls: call list
}

type t = {
  formal_map: FormalMap.t;
  bounds: transition list;

  return_bound: (EdgeExp.ValuePair.pair) option;
  return_monotonicity_map : (
    Monotonicity.t AccessExpressionMap.t * 
    Monotonicity.t AccessExpressionMap.t
  );

  formal_bounds: (EdgeExp.ValuePair.pair) EdgeExp.Map.t;
  formal_monotonicity_map : (
    Monotonicity.t AccessExpressionMap.t *
    Monotonicity.t AccessExpressionMap.t
  );
}

(* module ComplexityDegree : sig
  type t =
    | Linear
    | Log
    | Linearithmic
end *)

module Model : sig
  type t = {
    (* args: EdgeExp.ValuePair.t list;
    complexity: EdgeExp.ComplexityDegree.t;
    return_bound: EdgeExp.ValuePair.t option; *)

    name: string;
    complexity: EdgeExp.ValuePair.t;
    return_bound: EdgeExp.ValuePair.t option;
  }

  val pp : F.formatter -> t -> unit
end
  
(* type model = {
  complexity: ComplexityDegree.t;
  args: EdgeExp.ValuePair.t list;
} *)

type model_summary =
  | Real of t
  | Model of Model.t

val total_bound : transition list -> EdgeExp.T.t

val instantiate : t -> (EdgeExp.T.t * Typ.t) list
    -> variable_bound:(bound_type: BoundType.t -> EdgeExp.T.t -> cache -> EdgeExp.T.t * cache)
    -> Tenv.t -> LooperUtils.prover_data -> cache -> transition list * cache

val pp : F.formatter -> t -> unit


module TreeGraph : sig
  module Node : sig
    type t = 
    | CallNode of Procname.t * Location.t
    | TransitionNode of LTS.Node.t * EdgeExp.T.t * LTS.Node.t
    [@@deriving compare]
    val hash : 'a -> int
    val equal : t -> t -> bool
  end

  module Edge : sig
    type t = unit [@@deriving compare]
    val hash : 'a -> int
    val equal : t -> t -> bool
    val default : unit
  end

  include module type of Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(Edge)
  include module type of LooperUtils.DefaultDot

  val edge_attributes : edge -> Graph.Graphviz.DotAttributes.edge list
  val vertex_attributes : vertex -> Graph.Graphviz.DotAttributes.vertex list
  val vertex_name : vertex -> string

  module Map : module type of Caml.Map.Make(Node)
end


module TreeGraph_Dot : module type of Graph.Graphviz.Dot(TreeGraph)


val to_graph : t -> Procname.t -> Location.t -> TreeGraph.t