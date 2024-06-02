(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
module F = Format
module DC = DifferenceConstraint
module LTS = LabeledTransitionSystem

module EdgeData : sig
  type t =
    { backedge: bool
    ; branch_info: (Sil.if_kind * bool * Location.t) option
    ; mutable calls: EdgeExp.CallPair.Set.t
    ; mutable constraints: DC.t list
    ; mutable condition_norms: EdgeExp.Set.t list
    ; mutable bound: EdgeExp.T.t option
    ; mutable bound_norms: EdgeExp.Set.t list
    ; mutable computing_bound: bool }
  [@@deriving compare]

  val equal : t -> t -> bool

  val from_lts_edge : LTS.EdgeData.t -> t

  val is_reset : t -> EdgeExp.T.t -> bool

  val get_reset : t -> EdgeExp.T.t -> EdgeExp.ValuePair.t option

  val is_backedge : t -> bool

  (* Required by Graph module interface *)
  val default : t

  val branch_type : t -> bool

  val add_constraint : t -> DC.t -> unit
end

include module type of Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (LTS.Node) (EdgeData)

module EdgeSet : module type of Caml.Set.Make (E)

module EdgeMap : module type of Caml.Map.Make (E)

include module type of LooperUtils.DefaultDot

val edge_label : EdgeData.t -> string option

val vertex_attributes : LTS.Node.t -> Graph.Graphviz.DotAttributes.vertex list

val vertex_name : LTS.Node.t -> string

val edge_attributes : E.t -> Graph.Graphviz.DotAttributes.edge list

val pp_edge : Format.formatter -> E.t -> unit
