(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)


open! IStd
module F = Format


(* Difference Constraint of form "x <= y + c"
 * Example: "(len - i) <= (len - i) + 1" *)
type norm = EdgeExp.T.t [@@deriving compare]
type rhs_const = Binop.t * IntLit.t [@@deriving compare]
type value_rhs = norm * Binop.t * IntLit.t [@@deriving compare]
type rhs =
  | Value of value_rhs
  | Pair of (value_rhs * value_rhs)
  [@@deriving compare]

type t = (norm * rhs) [@@deriving compare]

val make : ?const_part:rhs_const -> norm -> norm -> t

val make_value_rhs : ?const_part:rhs_const -> norm -> value_rhs

val is_constant : t -> bool

val same_norms : t -> bool

val is_reset : t -> bool

val is_decreasing : t -> bool

val is_increasing : t -> bool

val to_string_const_part : rhs_const -> string

val to_string : t -> string

val pp_const_part : F.formatter -> rhs_const -> unit
    
val pp : F.formatter -> t -> unit

val get_dc : norm -> t list -> t option

(* module Map : sig
  type dc = t

  include module type of EdgeExp.Map

  val get_dc : norm -> rhs t -> dc option

  val add_dc : norm -> rhs -> rhs t -> rhs t

  val to_string : rhs EdgeExp.Map.t -> string
end *)