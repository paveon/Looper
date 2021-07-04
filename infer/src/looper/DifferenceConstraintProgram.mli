(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
module F = Format
module DC = DifferenceConstraint


(* Difference Constraint Program *)
type edge_output_type = | LTS | GuardedDCP | DCP [@@deriving compare]

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

  val pp : F.formatter -> t -> unit

  module Map : Caml.Map.S with type key = t
end

module EdgeData : sig
  type t = {
    backedge: bool;
    conditions: EdgeExp.Set.t;
    assignments: EdgeExp.t LooperUtils.AccessPathMap.t;
    modified: LooperUtils.AccessSet.t;
    branch_info: (Sil.if_kind * bool * Location.t) option;
    exit_edge: bool;

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

  val is_reset : t -> EdgeExp.t -> bool

  val get_reset : t -> EdgeExp.t -> EdgeExp.t option

  val is_exit_edge : t -> bool

  val is_backedge : t -> bool

  val active_guards : t -> EdgeExp.Set.t

  val modified : t -> LooperUtils.AccessSet.t

  val make : EdgeExp.t LooperUtils.AccessPathMap.t -> (Sil.if_kind * bool * Location.t) option -> t

  val empty : t

  (* Required by Graph module interface *)
  val default : t

  val branch_type : t -> bool

  val set_backedge : t -> t

  val add_condition : t -> EdgeExp.t -> t

  val add_assignment : t -> AccessPath.t -> EdgeExp.t -> t

  val add_invariants : t -> LooperUtils.AccessSet.t -> t

  val get_assignment_rhs : t -> AccessPath.t -> EdgeExp.t

  val derive_guards_why3 : t -> EdgeExp.Set.t -> Tenv.t -> LooperUtils.prover_data -> unit

  (* Derive difference constraint "x <= y + c" based on edge assignments *)
  val derive_constraint : t -> EdgeExp.t -> LooperUtils.AccessSet.t -> Pvar.Set.t -> (EdgeExp.t * LooperUtils.AccessSet.t) option
end

include module type of Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(EdgeData)
module NodeSet : module type of Caml.Set.Make(V)
module EdgeSet : module type of Caml.Set.Make(E)
module EdgeMap : module type of Caml.Map.Make(E)

include module type of LooperUtils.DefaultDot
val edge_label : EdgeData.t -> string
val vertex_attributes : Node.t -> Graph.Graphviz.DotAttributes.vertex list
val vertex_name : Node.t -> string
val edge_attributes : E.t -> Graph.Graphviz.DotAttributes.edge list
