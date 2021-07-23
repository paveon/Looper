(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd

module F = Format
module LTS = LabeledTransitionSystem
module DCP = DifferenceConstraintProgram


module Increments : Caml.Set.S with type elt = DCP.E.t * IntLit.t

module Decrements : Caml.Set.S with type elt = DCP.E.t * IntLit.t

module Resets : Caml.Set.S with type elt = DCP.E.t * EdgeExp.t * IntLit.t


type norm_updates = {
   increments: Increments.t;
   decrements: Decrements.t;
   resets: Resets.t
}

val empty_updates : norm_updates


type cache = {
  updates: norm_updates EdgeExp.Map.t;
  variable_bounds: EdgeExp.t EdgeExp.Map.t;
  lower_bounds: EdgeExp.t EdgeExp.Map.t;
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
  bound: EdgeExp.t;
  monotony_map: LooperUtils.Monotonicity.t LooperUtils.AccessPathMap.t;
  calls: call list
}

and t = {
  formal_map: FormalMap.t;
  bounds: transition list;
  return_bound: EdgeExp.t option;
}

val total_bound : transition list -> EdgeExp.t

val instantiate : t -> (EdgeExp.t * Typ.t) list 
    -> upper_bound:(EdgeExp.t -> cache -> EdgeExp.t * cache)
    -> lower_bound:(EdgeExp.t -> cache -> EdgeExp.t * cache)
    -> Tenv.t -> LooperUtils.prover_data -> cache -> transition list * cache

val pp : F.formatter -> t -> unit


module TreeGraph : sig
  module Node : sig
    type t = 
    | CallNode of Procname.t * Location.t
    | TransitionNode of LTS.Node.t * EdgeExp.t * LTS.Node.t
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