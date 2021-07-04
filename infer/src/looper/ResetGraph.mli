(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
module F = Format
module DCP = DifferenceConstraintProgram


(* Reset graph *)
module Node : sig
  type t = EdgeExp.t [@@deriving compare]
  val hash : 'a -> int
  val equal : t -> t -> bool
end

module Edge : sig
  type t = {
    dcp_edge : DCP.E.t option;
    const : IntLit.t;
  } [@@deriving compare]

  val hash : 'a -> int
  val equal : t -> t -> bool
  val default : t

  val dcp_edge : t -> DCP.E.t

  val make : DCP.E.t -> IntLit.t -> t
end

include module type of Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(Edge)
include module type of LooperUtils.DefaultDot

type graph = t

val edge_attributes : edge -> Graph.Graphviz.DotAttributes.edge list
val vertex_attributes : vertex -> Graph.Graphviz.DotAttributes.vertex list
val vertex_name : vertex -> string

module Chain : sig
  type t = {
    data : E.t list;
    mutable norms : (EdgeExp.Set.t * EdgeExp.Set.t) option;
  }
  [@@deriving compare]

  val empty : t
  
  val origin : t -> EdgeExp.t

  val value : t -> IntLit.t

  val transitions : t -> DCP.EdgeSet.t

  val norms : t -> graph -> EdgeExp.Set.t * EdgeExp.Set.t

  val pp : F.formatter -> t -> unit

  module Set : Caml.Set.S with type elt = t
end

(* Finds all reset chains leading to the norm through reset graph *)
val get_reset_chains : vertex -> graph -> DCP.t -> Chain.Set.t