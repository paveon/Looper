(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
module L = Logging
module DC = DifferenceConstraint

module Node : sig
  type t =
    | Prune of (Sil.if_kind * Location.t * Procdesc.Node.id)
    | Start of (Procname.t * Location.t)
    | Join of (Location.t * Procdesc.Node.id)
    | Exit
  [@@deriving compare]

  val equal : t -> t -> bool

  val hash : 'a -> int

  val is_join : t -> bool

  val is_loophead : t -> bool

  val get_location : t -> Location.t

  val to_string : t -> string

  val pp : Format.formatter -> t -> unit

  module Map : Caml.Map.S with type key = t
end

module EdgeData : sig
  type t =
    { backedge: bool
    ; conditions: EdgeExp.Set.t list
    ; condition_norms: EdgeExp.Set.t list
    ; assignments: (HilExp.access_expression * EdgeExp.ValuePair.t) list
    ; branch_info: (Sil.if_kind * bool * Location.t) option
    ; calls: EdgeExp.CallPair.Set.t }
  [@@deriving compare]

  val equal : t -> t -> bool

  (* Required by Graph module interface *)
  val default : t

  val set_backedge_flag : t -> is_backedge:bool -> t

  val add_condition : t -> EdgeExp.T.t -> t

  val add_condition_norm : t -> EdgeExp.T.t -> t

  val add_assignment : t -> HilExp.access_expression -> EdgeExp.ValuePair.t -> t

  val add_invariants : t -> LooperUtils.AccessExpressionSet.t AccessPath.BaseMap.t -> t

  val get_assignment_rhs : t -> HilExp.access_expression -> EdgeExp.ValuePair.t

  val derive_guards :
    t -> (EdgeExp.T.t * Why3.Term.term) list -> Tenv.t -> Provers.prover_data -> EdgeExp.Set.t

  (* Derive difference constraint "x <= y + c" based on edge assignments *)
  val derive_constraint :
       t
    -> EdgeExp.T.t * LooperUtils.AccessExpressionSet.t
    -> AccessPath.BaseSet.t
    -> Tenv.t
    -> Procname.t
    -> LooperUtils.AccessExpressionSet.t * DC.rhs option * EdgeExp.Set.t
end

include module type of Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Node) (EdgeData)

module NodeSet : module type of Caml.Set.Make (V)

module EdgeSet : module type of Caml.Set.Make (E)

module EdgeMap : module type of Caml.Map.Make (E)

include module type of LooperUtils.DefaultDot

val edge_label : EdgeData.t -> string option

val vertex_attributes : Node.t -> Graph.Graphviz.DotAttributes.vertex list

val vertex_name : Node.t -> string

val edge_attributes : E.t -> Graph.Graphviz.DotAttributes.edge list
