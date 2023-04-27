(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
module F = Format

val debug_fmt : F.formatter list ref

module PvarMap : sig
  include module type of Caml.Map.Make (Pvar)

  val pp : F.formatter -> 'a t -> unit

  val to_string : 'a t -> string
end

module StringMap : Caml.Map.S with type key = string

module AccessSet : Caml.Set.S with type elt = AccessPath.t

module AccessPathMap : Caml.Map.S with type key = AccessPath.t

module AccessExpressionSet : Caml.Set.S with type elt = HilExp.access_expression

module AccessExpressionMap : Caml.Map.S with type key = HilExp.access_expression

module Monotonicity : sig
  type t = NonDecreasing | NonIncreasing | NotMonotonic [@@deriving compare]
end

module BoundType : sig
  type t = Upper | Lower [@@deriving compare]
end

val access_of_exp :
     include_array_indexes:bool
  -> Exp.t
  -> Typ.t
  -> f_resolve_id:(Var.t -> AccessPath.t option)
  -> AccessPath.t list

val access_of_lhs_exp :
     include_array_indexes:bool
  -> Exp.t
  -> Typ.t
  -> f_resolve_id:(Var.t -> AccessPath.t option)
  -> AccessPath.t option

module DefaultDot : sig
  val default_edge_attributes : 'a -> 'b list

  val get_subgraph : 'a -> 'b option

  val default_vertex_attributes : 'a -> 'b list

  val graph_attributes : 'a -> 'b list
end

val output_graph : string -> 'a -> (Out_channel.t -> 'a -> unit) -> unit
