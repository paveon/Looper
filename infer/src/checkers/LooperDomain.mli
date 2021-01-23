(*
 * Copyright (c) 2019-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module F = Format

module PvarMap : sig
  include module type of Caml.Map.Make(Pvar)

  val pp : F.formatter -> 'a t -> unit

  val to_string : 'a t -> string
end

module AccessSet : Caml.Set.S with type elt = AccessPath.t

module AccessPathMap : Caml.Map.S with type key = AccessPath.t


module EdgeExp : sig
   type t =
   | BinOp of Binop.t * t * t
   | UnOp of Unop.t * t * Typ.t option
   | Access of AccessPath.t
   (* | Var of Pvar.t *)
   | Const of Const.t
   | Call of edge_call
   | Max of t list
   | Min of t list
   | Inf
   [@@deriving compare]
   
   and call_arg = (t * Typ.t) [@@deriving compare]

   and edge_call = Typ.t * Procname.t * call_arg list * summary option [@@deriving compare]

   and summary = {
      formal_map: FormalMap.t;
      bound: t;
      return_bound: t option;
   }
   [@@deriving compare]

   module Set : Caml.Set.S with type elt = t

   module Map : Caml.Map.S with type key = t

   val to_string : t -> string

   val pp : F.formatter -> t -> unit

   val equal : t -> t -> bool

   val one : t

   val zero : t

   val of_int : int -> t

   val of_int32 : int32 -> t
   
   val of_int64 : int64 -> t

   val is_zero : t -> bool

   val is_one : t -> bool

   val is_const : t -> bool

   val is_variable : t -> Pvar.Set.t -> bool

   val is_int : t -> Typ.t PvarMap.t -> Tenv.t -> bool

   val is_formal : t -> Pvar.Set.t -> bool

   val is_return : t -> bool

   val eval : Binop.t -> IntLit.t -> IntLit.t -> t

   val try_eval : Binop.t -> t -> t -> t

   val merge : t -> (Binop.t * IntLit.t) option -> t

   (* val separate : t -> (t * IntLit.t) *)

   val separate2 : t -> t * (Binop.t * IntLit.t) option

   val simplify : t -> t

   val access_path_id_resolver : t Ident.Map.t -> Var.t -> AccessPath.t option

   val of_exp : Exp.t -> t Ident.Map.t -> Typ.t -> Typ.t PvarMap.t -> t

   (* val to_z3_expr : t -> Z3.context -> Z3.Expr.expr Map.t -> (Z3.Expr.expr * Z3.Expr.expr list) *)

   val to_z3_expr : t -> Z3.context -> (AccessPath.t -> (Z3.Expr.expr * Z3.Expr.expr list)) option -> (Z3.Expr.expr * Z3.Expr.expr list)

   val always_positive : t -> Z3.context -> Z3.Solver.solver -> bool

   val get_accesses: t -> Set.t

   val map_accesses: t -> f:(AccessPath.t -> 'a -> t * 'a) -> 'a -> t * 'a

   val subst : t -> call_arg list -> FormalMap.t -> t

   val normalize_condition : t -> Tenv.t -> t

   val add : t -> t -> t

   val sub : t -> t -> t

   val mult : t -> t -> t
end

val pp_summary : F.formatter -> EdgeExp.summary -> unit


(* Difference Constraint of form "x <= y + c"
 * Example: "(len - i) <= (len - i) + 1" *)
module DC : sig
   type norm = EdgeExp.t [@@deriving compare]
   type rhs_const = Binop.t * IntLit.t [@@deriving compare]
   type rhs = norm * Binop.t * IntLit.t [@@deriving compare]

   type t = (norm * rhs) [@@deriving compare]

   val make : ?const_part:rhs_const -> norm -> norm -> t

   val make_rhs : ?const_part:rhs_const -> norm -> rhs

   val is_constant : t -> bool

   val same_norms : t -> bool

   val is_decreasing : t -> bool

   val is_increasing : t -> bool

   val to_string : t -> bool -> string
      
   val pp : F.formatter -> t -> unit

   module Map : sig
      type dc = t

      include module type of EdgeExp.Map

      val get_dc : norm -> rhs t -> dc option

      val add_dc : norm -> rhs -> rhs t -> rhs t

      val to_string : rhs EdgeExp.Map.t -> string
   end
end


module DefaultDot : sig
   val default_edge_attributes : 'a -> 'b list
   val get_subgraph : 'a -> 'b option
   val default_vertex_attributes : 'a -> 'b list
   val graph_attributes : 'a -> 'b list
end

type call_site = EdgeExp.t * Location.t

module CallSiteSet : Caml.Set.S with type elt = call_site

(* Difference Constraint Program *)
module DCP : sig
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

      val to_string : t -> string

      val pp : F.formatter -> t -> unit

      module Map : Caml.Map.S with type key = t
   end

   module EdgeData : sig
      type t = {
         backedge: bool;
         conditions: EdgeExp.Set.t;
         assignments: EdgeExp.t AccessPathMap.t;
         modified: AccessSet.t;
         branch_info: (Sil.if_kind * bool * Location.t) option;
         exit_edge: bool;
         
         mutable calls: CallSiteSet.t;
         mutable constraints: DC.rhs DC.Map.t;
         mutable guards: EdgeExp.Set.t;
         mutable bound: EdgeExp.t;
         mutable execution_cost: EdgeExp.t;
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

      val modified : t -> AccessSet.t

      val make : EdgeExp.t AccessPathMap.t -> (Sil.if_kind * bool * Location.t) option -> t

      val empty : t

      (* Required by Graph module interface *)
      val default : t

      val branch_type : t -> bool

      val set_backedge : t -> t

      val add_condition : t -> EdgeExp.t -> t

      val add_assignment : t -> AccessPath.t -> EdgeExp.t -> t

      val add_invariants : t -> AccessSet.t -> t

      val get_assignment_rhs : t -> AccessPath.t -> EdgeExp.t

      val derive_guards : t -> EdgeExp.Set.t -> Z3.Solver.solver -> Z3.context -> unit

      (* Derive difference constraints "x <= y + c" based on edge assignments *)
      val derive_constraint : (Node.t * t * Node.t) -> EdgeExp.t -> EdgeExp.Set.t -> Pvar.Set.t -> EdgeExp.Set.t
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

module DCP_Dot : module type of Graph.Graphviz.Dot(DCP)

(* Variable flow graph *)
module VFG : sig
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
   include module type of DefaultDot

   type graph = t

   val edge_attributes : edge -> [> `Color of int | `Label of string ] list
   val vertex_attributes : vertex -> [> `Label of string | `Shape of [> `Box ] ] list
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
end

module RG_Dot : module type of Graph.Graphviz.Dot(RG)

module Increments : Caml.Set.S with type elt = DCP.E.t * IntLit.t

module Resets : Caml.Set.S with type elt = DCP.E.t * EdgeExp.t * IntLit.t

type cache = {
  updates: (Increments.t * Resets.t) EdgeExp.Map.t;
  variable_bounds: EdgeExp.t EdgeExp.Map.t;
  reset_chains: RG.Chain.Set.t EdgeExp.Map.t;
}

val empty_cache : cache

val is_loop_prune : Sil.if_kind -> bool

val output_graph : string -> 'a ->(Out_channel.t -> 'a -> unit) -> unit
