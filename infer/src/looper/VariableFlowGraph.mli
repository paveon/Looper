(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)


open! IStd
module DCP = DifferenceConstraintProgram


(* Variable flow graph *)
module Node : sig
  type t = EdgeExp.t * DCP.Node.t [@@deriving compare]
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
module NodeSet : module type of Caml.Set.Make(V)
module EdgeSet : module type of Caml.Set.Make(E)

include module type of LooperUtils.DefaultDot
val edge_attributes : edge -> Graph.Graphviz.DotAttributes.edge list
val vertex_attributes : vertex -> Graph.Graphviz.DotAttributes.vertex list
val vertex_name : vertex -> string

module Map : module type of Caml.Map.Make(Node)