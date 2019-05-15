(*
 * Copyright (c) 2019-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module F = Format

module LocSet : module type of Caml.Set.Make(Location)

module PvarSet : sig
   include module type of Caml.Set.Make(Pvar)
   
   val pp : F.formatter -> t -> unit

   val to_string : t -> string
end

module PvarMap : sig
  include module type of Caml.Map.Make(Pvar)

  val pp : F.formatter -> 'a t -> unit

  val to_string : 'a t -> string
end

(* Difference Constraint of form "x <= y + c"
 * Example: "(len - i) <= (len - i) + 1" *)
module DC : sig
   type t = (Exp.t * Exp.t * IntLit.t) [@@deriving compare]
   type dc = t
   type rhs = (Exp.t * IntLit.t) [@@deriving compare]

   val make : ?const:IntLit.t -> Exp.t -> Exp.t -> t

   val make_rhs : ?const:IntLit.t -> Exp.t -> rhs

   val is_constant : t -> bool

   val same_norms : t -> bool

   val is_decreasing : t -> bool

   val is_increasing : t -> bool

   val to_string : t -> bool -> string
      
   val pp : F.formatter -> dc -> unit

   module Map : sig
      include module type of Exp.Map

      val get_dc : Exp.t -> rhs t -> dc option

      val add_dc : Exp.t -> rhs -> rhs t -> rhs t
   end
end

module Path : sig
   type element = (Sil.if_kind * bool * Location.t) [@@deriving compare]
   val element_equal : element -> element -> bool

   val pp_element : F.formatter -> element -> unit

   type t = element list
   val equal : t -> t -> bool
   val empty : t

   (* Creates common path prefix of provided paths *)
   val common_prefix : t -> t -> t

   val in_loop : t -> bool

   val pp : F.formatter -> t -> unit

   val path_to_string : t -> string
end

module Bound : sig
   type t =
   | BinOp of Binop.t * t * t
   | Value of Exp.t
   | Max of t list
   | Min of t list
   | Inf
   [@@deriving compare]

   val to_string : t -> string

   val pp : F.formatter -> t -> unit

   val is_zero : t -> bool

   val is_one : t -> bool
end

type graph_type = | LTS | GuardedDCP | DCP

val active_graph_type : graph_type ref 

module DefaultDot : sig
   val default_edge_attributes : 'a -> 'b list
   val get_subgraph : 'a -> 'b option
   val default_vertex_attributes : 'a -> 'b list
   val graph_attributes : 'a -> 'b list
end

(* Difference Constraint Program *)
module DCP : sig
   module Node : sig
      type t = 
      | Prune of (Sil.if_kind * Location.t)
      | Start of Location.t
      | Join of (t * t)
      | Exit
      [@@deriving compare]
      val equal : t -> t -> bool
      val hash : 'a -> int

      val is_join : t -> bool

      val to_string : t -> string

      val pp : F.formatter -> t -> unit

      module Map : Caml.Map.S with type key = t
   end

   module EdgeData : sig
      type t = {
      backedge: bool;
      conditions: Exp.Set.t;
      assignments: Exp.t PvarMap.t;
      mutable constraints: DC.rhs DC.Map.t;
      mutable guards: Exp.Set.t;
      mutable bound_cache: Bound.t option;
      mutable bound_norm: Exp.t option;
      mutable computing: bool;

      (* Last element of common path prefix *)
      path_prefix_end: Path.element option;
      }
      [@@deriving compare]

      val equal : t -> t -> bool

      val is_reset : t -> Exp.t -> bool

      val active_guards : t -> Exp.Set.t

      val modified_pvars : t -> PvarSet.t

      module Set : Caml.Set.S with type elt = t

      val make : Exp.t PvarMap.t -> Path.element option -> t

      val empty : t

      (* Required by Graph module interface *)
      val default : t

      val set_backedge : t -> t

      val add_condition : t -> Exp.t -> t

      val add_assignment : t -> Pvar.t -> Exp.t -> t

      val add_invariants : t -> PvarSet.t -> t

      val set_path_end : t -> Path.element option -> t

      val get_assignment_rhs : t -> Pvar.t -> Exp.t

      val derive_guards : t -> Exp.Set.t -> Z3.Solver.solver -> Z3.context -> unit
      
      (* Derive difference constraints "x <= y + c" based on edge assignments *)
      val derive_constraint : t -> Exp.t -> Typ.t PvarMap.t -> Exp.Set.t
   end

   include module type of Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(EdgeData)
   module NodeSet : module type of Caml.Set.Make(V)
   module EdgeSet : module type of Caml.Set.Make(E)

   include module type of DefaultDot
   val edge_label : EdgeData.t -> string
   val vertex_attributes : Node.t -> [> `Label of string | `Shape of [> `Box ] ] list
   val vertex_name : Node.t -> string
   val edge_attributes : E.t -> [> `Color of int | `Label of string ] list
end

module DCPDot : module type of Graph.Graphviz.Dot(DCP)

(* Variable flow graph *)
module VFG : sig
   module Node : sig
      type t = Exp.t * DCP.Node.t [@@deriving compare]
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
   include module type of DefaultDot

   val edge_attributes : edge -> [> `Color of int | `Label of string ] list
   val vertex_attributes : vertex -> [> `Label of string | `Shape of [> `Box ] ] list
   val vertex_name : vertex -> string

   module Map : module type of Caml.Map.Make(Node)
end

module VFG_Dot : module type of Graph.Graphviz.Dot(VFG)

(* Reset graph *)
module RG : sig
   module Node : sig
      type t = Exp.t [@@deriving compare]
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
   include module type of DefaultDot

   type graph = t

   val edge_attributes : edge -> [> `Color of int | `Label of string ] list
   val vertex_attributes : vertex -> [> `Label of string | `Shape of [> `Box ] ] list
   val vertex_name : vertex -> string

   module Chain : sig
      type t = {
      data : E.t list;
      mutable norms : (Exp.Set.t * Exp.Set.t) option;
      }
      [@@deriving compare]

      val empty : t
      
      val origin : t -> Exp.t

      val value : t -> IntLit.t

      val transitions : t -> DCP.EdgeSet.t

      val norms : t -> graph -> Exp.Set.t * Exp.Set.t

      val pp : F.formatter -> t -> unit

      module Set : Caml.Set.S with type elt = t
   end

   (* Finds all reset chains leading to the norm through reset graph *)
   val get_reset_chains : vertex -> graph -> DCP.t -> Chain.Set.t
end

module RG_Dot : module type of Graph.Graphviz.Dot(RG)

val exp_to_z3_expr : Z3.context -> Exp.t -> Z3.Expr.expr

val exp_to_str : ?braces:bool -> Exp.t -> string

val is_loop_prune : Sil.if_kind -> bool

type t = {
  path: Path.t;
  last_node: DCP.Node.t;
  potential_norms: Exp.Set.t;
  initial_norms: Exp.Set.t;
  locals: PvarSet.t;
  ident_map: Pvar.t Ident.Map.t;
  edge_modified: PvarSet.t;
  loop_modified: PvarSet.t;
  edge_data: DCP.EdgeData.t;
  graph_nodes: DCP.NodeSet.t;
  graph_edges: DCP.EdgeSet.t;
  incoming_edges: DCP.EdgeSet.t;
}

val initial : DCP.Node.t -> t

val norm_is_variable : Exp.t -> Typ.t PvarMap.t -> bool

val get_unmodified_pvars : t -> PvarSet.t

val ( <= ) : lhs:t -> rhs:t -> bool

val join : t -> t -> t

val widen : prev:t -> next:t -> num_iters:int -> t

val pp : F.formatter -> t -> unit

type summary = {
  globals: Typ.t PvarMap.t;
  bound: Bound.t;
}

val pp_summary : F.formatter -> summary -> unit