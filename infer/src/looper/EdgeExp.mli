(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
module F = Format


type t =
| BinOp of Binop.t * t * t
| UnOp of Unop.t * t * Typ.t option
| Access of AccessPath.t
| Const of Const.t
| Call of Typ.t * Procname.t * (t * Typ.t) list * Location.t
| Max of t list
| Min of t list
| Inf
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

val is_symbolic_const : t -> Pvar.Set.t -> bool

val is_int : t -> Typ.t LooperUtils.PvarMap.t -> Tenv.t -> bool

val is_return : t -> bool

val eval_consts : Binop.t -> IntLit.t -> IntLit.t -> IntLit.t

val try_eval : Binop.t -> t -> t -> t

val evaluate : t -> float LooperUtils.AccessPathMap.t -> float -> float

val merge : t -> (Binop.t * IntLit.t) option -> t

(* Splits expression on +/- into terms *)
val split_exp : t -> t list

(* Merges terms into single expression *)
val merge_exp_parts : t list -> t

val separate : t -> t * (Binop.t * IntLit.t) option

(* Tries to expand the expression on multiplications  *)
val expand_multiplication : t -> IntLit.t option -> t

val simplify : t -> t

val evaluate_const_exp : t -> IntLit.t option

val access_path_id_resolver : t Ident.Map.t -> Var.t -> AccessPath.t option

val of_exp : Exp.t -> t Ident.Map.t -> Typ.t -> Typ.t LooperUtils.PvarMap.t -> t

val to_why3_expr : t -> Tenv.t -> LooperUtils.prover_data -> (Why3.Term.term * Why3.Term.Sterm.t)

val always_positive_why3 : t -> Tenv.t -> LooperUtils.prover_data -> bool

val get_accesses: t -> Set.t

val map_accesses: t -> f:(AccessPath.t -> 'a -> t * 'a) -> 'a -> t * 'a

val subst : t -> (t * Typ.t) list -> FormalMap.t -> t

val normalize_condition : t -> Tenv.t -> t

val determine_monotony_why3 : t -> Tenv.t -> LooperUtils.prover_data -> LooperUtils.VariableMonotony.t LooperUtils.AccessPathMap.t

val add : t -> t -> t

val sub : t -> t -> t

val mult : t -> t -> t