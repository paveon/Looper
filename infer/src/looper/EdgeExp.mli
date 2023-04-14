(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
module F = Format

module ComplexityDegree : sig
  type t = Linear | Log | Linearithmic
end

(* module StrlenArg : sig
     type t = Variable of HilExp.access_expression | Const of string
   end *)

module rec T : sig
  type call = Typ.t * Procname.t * (t * Typ.t) list * Location.t

  and t =
    | BinOp of Binop.t * t * t
    | UnOp of Unop.t * t * Typ.t option
    | Access of HilExp.access_expression
    | Const of Const.t
    | Cast of Typ.t * t
    | Call of call
    | Max of Set.t
    | Min of Set.t
    | Inf
    | Strlen of HilExp.access_expression
    | Symbolic of ComplexityDegree.t * t
  [@@deriving compare]

  val equal : t -> t -> bool
end

and Set : (Caml.Set.S with type elt = T.t)

include T

module Map : Caml.Map.S with type key = T.t

val call_to_string : T.call -> string

val to_string : T.t -> string

val pp : F.formatter -> T.t -> unit

val pp_call : F.formatter -> T.call -> unit

val pp_list : string -> (F.formatter -> 'a -> unit) -> F.formatter -> 'a list -> unit

val list_to_string : 'a list -> string -> (F.formatter -> 'a -> unit) -> string

module ValuePair : sig
  type pair = T.t * T.t [@@deriving compare]

  type t = V of T.t | P of pair [@@deriving compare]

  val to_string : t -> string

  val pp : F.formatter -> t -> unit

  val make_pair : T.t -> t

  val make_list : T.t list -> T.t list -> t list

  val map : t -> f:(T.t -> T.t) -> t

  val merge : t -> t -> t

  val create_binop : Binop.t -> t -> t -> t

  val map_accesses : T.t -> f:(HilExp.access_expression -> t) -> t

  module Set : Caml.Set.S with type elt = t
end

module CallPair : sig
  type pair = T.call * T.call [@@deriving compare]

  type t = V of T.call | P of pair [@@deriving compare]

  val to_string : t -> string

  val pp : F.formatter -> t -> unit

  module Set : Caml.Set.S with type elt = t
end

(* type call_pair =
     | CallValue of T.call
     | CallPair of (T.call * T.call)
     [@@deriving compare]

   val call_pair_to_string : call_pair -> string

   val pp_call_pair : F.formatter -> call_pair -> unit

   module CallPairSet : Caml.Set.S with type elt = call_pair *)

(* type call_pair =
     | CallValue of T.call
     | CallPair of (T.call * T.call)
     [@@deriving compare]

   val call_pair_to_string : call_pair -> string

   val pp_call_pair : F.formatter -> call_pair -> unit

   module CallPairSet : Caml.Set.S with type elt = call_pair *)

val compare : t -> t -> int

(* type t =
   | BinOp of Binop.t * t * t
   | UnOp of Unop.t * t * Typ.t option
   | Access of HilExp.access_expression
   | Const of Const.t
   | Cast of Typ.t * t
   | Call of Typ.t * Procname.t * (t * Typ.t) list * Location.t
   | Max of t list
   | Min of t list
   | Inf
   [@@deriving compare] *)

(* module Set : Caml.Set.S with type elt = t *)

val equal : T.t -> T.t -> bool

val one : T.t

val zero : T.t

val of_int : int -> T.t

val of_int32 : int32 -> T.t

val of_int64 : int64 -> T.t

val is_zero : T.t -> bool

val is_one : T.t -> bool

val is_const : T.t -> bool

val is_formal_variable : T.t -> AccessPath.BaseSet.t -> Tenv.t -> bool

val is_variable : T.t -> AccessPath.BaseSet.t -> Tenv.t -> bool

val is_symbolic_const : T.t -> AccessPath.BaseSet.t -> Tenv.t -> bool

val is_int : T.t -> Typ.t LooperUtils.PvarMap.t -> Tenv.t -> bool

val get_typ : Tenv.t -> T.t -> Typ.t option

val is_integer_type : Typ.t -> bool

val is_integer_condition : Tenv.t -> T.t -> bool

val is_return : T.t -> bool

val eval_consts : Binop.t -> IntLit.t -> IntLit.t -> IntLit.t

val try_eval : Binop.t -> T.t -> T.t -> T.t

val evaluate : T.t -> float LooperUtils.AccessExpressionMap.t -> float -> float

val merge : T.t -> (Binop.t * IntLit.t) option -> T.t

val attach_const : T.t -> IntLit.t option -> T.t

val multiply_term_by_frac : T.t * (int * int) -> T.t

(* Simplifies expression and splits it into individual terms *)
val split_exp_new : T.t -> (T.t * (int * int)) list * (Binop.t * IntLit.t) option

(* Splits expression on +/- into terms *)
(* val split_exp : T.t -> T.t list *)

(* Merges terms into single expression *)
val merge_exp_list : T.t list -> T.t

val separate : T.t -> T.t * (Binop.t * IntLit.t) option

(* Tries to expand the expression on multiplications  *)
(* val expand_multiplication : T.t -> IntLit.t option -> T.t *)

val simplify : T.t -> T.t

val remove_casts_of_consts : T.t -> Typ.IntegerWidths.t -> T.t

val evaluate_const_exp : T.t -> IntLit.t option

(* val access_path_id_resolver : (t * Typ.t) Ident.Map.t -> Var.t -> AccessPath.t option *)

(* val of_exp : Exp.t -> (t * Typ.t) Ident.Map.t -> Typ.t -> Typ.t LooperUtils.PvarMap.t -> t *)

(* val of_hil_exp : HilExp.t -> (Ident.t -> T.t) -> T.t *)
val of_sil_exp :
     include_array_indexes:bool
  -> f_resolve_id:(Var.t -> HilExp.access_expression option)
  -> test_resolver:(Var.t -> ValuePair.t option)
  -> add_deref:bool
  -> Exp.t
  -> Typ.t
  -> ValuePair.t

val to_why3_expr : T.t -> Tenv.t -> LooperUtils.prover_data -> Why3.Term.term * Why3.Term.Sterm.t

val always_positive_why3 : T.t -> Tenv.t -> LooperUtils.prover_data -> bool

val get_accesses : T.t -> LooperUtils.AccessExpressionSet.t

val get_access_exp_set : T.t -> Set.t

val map_accesses : T.t -> f:(HilExp.access_expression -> 'a -> T.t * 'a) -> 'a -> T.t * 'a

val subst : T.t -> (T.t * Typ.t) list -> FormalMap.t -> T.t

val normalize_condition : T.t -> Tenv.t -> T.t

val deduplicate_exp_list : T.t list -> T.t list

val determine_monotonicity :
     T.t
  -> Tenv.t
  -> LooperUtils.prover_data
  -> LooperUtils.Monotonicity.t LooperUtils.AccessExpressionMap.t

val add : T.t -> T.t -> T.t

val sub : T.t -> T.t -> T.t

val mult : T.t -> T.t -> T.t
