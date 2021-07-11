(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
module F = Format
module DC = DifferenceConstraint
module LTS = LabeledTransitionSystem


(* Difference Constraint Program *)
type edge_output_type = | GuardedDCP | DCP [@@deriving compare]


module EdgeData : sig
  type t = {
    backedge: bool;
    branch_info: (Sil.if_kind * bool * Location.t) option;

    mutable calls: EdgeExp.Set.t;
    mutable constraints: DC.rhs DC.Map.t;
    mutable guards: EdgeExp.Set.t;
    mutable bound: EdgeExp.t option;
    mutable bound_norm: EdgeExp.t option;
    mutable computing_bound: bool;

    mutable edge_type: edge_output_type;
  }
  [@@deriving compare]

  val equal : t -> t -> bool

  val from_lts_edge : LTS.EdgeData.t -> t

  val is_reset : t -> EdgeExp.t -> bool

  val get_reset : t -> EdgeExp.t -> EdgeExp.t option

  val is_backedge : t -> bool

  val active_guards : t -> EdgeExp.Set.t

  (* Required by Graph module interface *)
  val default : t

  val set_edge_output_type : t -> edge_output_type -> unit

  val branch_type : t -> bool

  val add_guards : t -> EdgeExp.Set.t -> unit

  val add_constraint : t -> DC.t -> unit
end

include module type of Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(LTS.Node)(EdgeData)
module EdgeSet : module type of Caml.Set.Make(E)
module EdgeMap : module type of Caml.Map.Make(E)

include module type of LooperUtils.DefaultDot
val edge_label : EdgeData.t -> string
val vertex_attributes : LTS.Node.t -> Graph.Graphviz.DotAttributes.vertex list
val vertex_name : LTS.Node.t -> string
val edge_attributes : E.t -> Graph.Graphviz.DotAttributes.edge list
