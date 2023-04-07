(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
open LooperUtils
module F = Format
module L = Logging


let debug_log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.fprintf (List.hd_exn !debug_fmt) fmt

let console_log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.printf fmt

module ComplexityDegree = struct
  type t =
    | Linear
    | Log
    | Linearithmic
    [@@deriving compare]
end

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
  | Symbolic of ComplexityDegree.t * t
  [@@deriving compare]

  val equal : t -> t -> bool

end = struct
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
  | Symbolic of ComplexityDegree.t * t
  [@@deriving compare]

  let equal e1 e2 = Int.equal (compare e1 e2) 0
end

and Set : Caml.Set.S with type elt = T.t = Caml.Set.Make(T)

include T

module Map = Caml.Map.Make(struct
  type nonrec t = T.t
  let compare = compare
end)

let rec call_to_string (_, callee, args, _) =
  let proc_name = String.drop_suffix (Procname.to_simplified_string callee) 2 in
  let args_string = String.concat ~sep:", " (List.map args ~f:(fun (x, _) -> to_string x)) in
  F.asprintf "%s(%s)" proc_name args_string

and to_string exp =
  let process_min_max min_max prefix ~f =
    match Set.cardinal min_max with
    | 0 -> assert(false)
    | 1 -> f (to_string (Set.min_elt min_max))
    | _ -> (
      let str_list = List.map (Set.elements min_max) ~f:(fun arg -> to_string arg) in
      F.asprintf "%s(%s)" prefix (String.concat ~sep:", " str_list)
    )
  in

  match exp with
  | BinOp (op, lhs, rhs) -> (
    F.sprintf "(%s %s %s)" (to_string lhs) (Binop.str Pp.text op) (to_string rhs)
  )
  | UnOp (op, exp, _) -> F.sprintf "%s%s" (Unop.to_string op) (to_string exp)
  | Access path -> F.asprintf "%a" HilExp.AccessExpression.pp path
  | Const const -> F.asprintf "%a" Const.(pp Pp.text) const
  | Cast (typ, subexp) -> F.asprintf "(%a) %s" (Typ.pp_full Pp.text) typ (to_string subexp)
  | Call (_, callee, args, _) -> (
    let proc_name = String.drop_suffix (Procname.to_simplified_string callee) 2 in
    let args_string = String.concat ~sep:", " (List.map args ~f:(fun (x, _) -> to_string x)) in
    F.asprintf "%s(%s)" proc_name args_string
  )
  | Max args -> process_min_max args "max" ~f:(fun str -> F.sprintf "[%s]" str)
  | Min args -> process_min_max args "min" ~f:(fun str -> F.sprintf "min(%s)" str)
  | Inf -> "Infinity"
  | Symbolic (degree, value) -> (
    let degree_str = match degree with
    | ComplexityDegree.Linear -> "N"
    | ComplexityDegree.Linearithmic -> "LogN"
    | ComplexityDegree.Log -> "Log"
    in
    F.asprintf "%s(%s)" degree_str (to_string value)
  )


let pp fmt exp = F.fprintf fmt "%s" (to_string exp)

let pp_call fmt call = F.fprintf fmt "%s" (call_to_string call)

let pp_list name pp_func fmt list = if not (List.is_empty list) then (
  F.fprintf fmt "@[<v2>%s: {" name;
  List.iter list ~f:(fun cond -> F.fprintf fmt "@,%a" pp_func cond);
  F.fprintf fmt "}@]"
)
else F.fprintf fmt "%s: {}" name

let list_to_string set name pp_func = F.asprintf "%a" (pp_list name pp_func) set

let eval_consts op c1 c2 = match op with
  | Binop.PlusA _ | Binop.PlusPI -> IntLit.add c1 c2
  | Binop.MinusA _ -> IntLit.sub c1 c2
  | Binop.Mult _ -> IntLit.mul c1 c2
  | Binop.DivI -> IntLit.div c1 c2
  | Binop.Ne -> if IntLit.eq c1 c2 then IntLit.zero else IntLit.one
  | Binop.Eq -> if IntLit.eq c1 c2 then IntLit.one else IntLit.zero
  | Binop.Shiftrt -> IntLit.shift_right c1 c2
  | Binop.Shiftlt -> IntLit.shift_left c1 c2
  | _ -> L.(die InternalError)"[EdgeExp.eval_consts] Unsupported operator %a %s %a" 
          IntLit.pp c1 (Binop.str Pp.text op) IntLit.pp c2

let zero = Const (Const.Cint IntLit.zero)

let try_eval op e1 e2 = match e1, e2 with
  | Const (Const.Cint c1), Const (Const.Cint c2) -> Const (Const.Cint (eval_consts op c1 c2))
  | Const (Const.Cint c), exp when IntLit.iszero c -> (
    match op with
    | Binop.PlusA _ -> exp
    | Binop.MinusA _ -> UnOp (Unop.Neg, exp, None)
    | Binop.Mult _ | Binop.DivI -> zero
    | _ -> BinOp (op, e1, e2)
  )
  | exp, Const (Const.Cint c) when IntLit.iszero c -> (
    match op with
    | Binop.PlusA _ -> exp | Binop.MinusA _ -> exp
    | Binop.Mult _ -> zero
    | Binop.DivI -> assert(false)
    | _ -> BinOp (op, e1, e2)
  )
  | _ -> BinOp (op, e1, e2)

let rec evaluate_const_exp exp = 
  let rec get_min_max op args = match args with
  | [] -> None
  | [x] -> evaluate_const_exp x
  | x::xs -> (
    match evaluate_const_exp x, get_min_max op xs with
    | Some x, Some y -> Some (op x y)
    | _ -> None
  )
  in

  match exp with
  | Const (Const.Cint x) -> Some x
  | BinOp (op, lexp, rexp) -> (
    let lconst_opt = evaluate_const_exp lexp in
    let rconst_opt = evaluate_const_exp rexp in
    match lconst_opt, rconst_opt with
    | Some lconst, Some rconst -> Some (eval_consts op lconst rconst)
    | _ -> None
  )
  | UnOp (Unop.Neg, exp, _) -> (
    match evaluate_const_exp exp with
    | Some value -> Some (IntLit.neg value)
    | None -> None
  )
  | Max args -> get_min_max IntLit.max (Set.elements args)
  | Min args -> get_min_max IntLit.min (Set.elements args)
  | _ -> None


let is_const exp = Option.is_some (evaluate_const_exp exp)

module ValuePair = struct
  type pair = (T.t * T.t)
    [@@deriving compare]

  type t =
    | V of T.t
    | P of pair
    [@@deriving compare]

  let to_string value_pair = match value_pair with
    | V rhs_value -> to_string rhs_value
    | P (lb, ub) -> F.asprintf "(%s; %s)" (to_string lb) (to_string ub)

  let pp fmt exp = F.fprintf fmt "%s" (to_string exp)

  let make_pair exp = P (exp, exp)

  let make_list lbs ubs =
    List.map2_exn lbs ubs ~f:(fun lb ub -> 
      if T.equal lb ub then V lb else P (lb, ub)
    )

  let map value_pair ~f = match value_pair with
    | V value -> V (f value)
    | P (lb, ub) -> P (f lb, f ub)

  let merge p1 p2 = match p1, p2 with
    | V lb, V ub -> P (lb, ub)
    | V lb, P (ub_lb, ub_ub) -> (
      let lb_set = Set.add ub_lb (Set.singleton lb) in
      let ub_set = Set.add ub_ub (Set.singleton lb) in
      P (T.Min lb_set, T.Max ub_set)
    )
    | P (lb_lb, lb_ub), V ub -> (
      let lb_set = Set.add lb_lb (Set.singleton ub) in
      let ub_set = Set.add lb_ub (Set.singleton ub) in
      P (T.Min lb_set, T.Max ub_set)
    )
    | P (lb_lb, lb_ub), P (ub_lb, ub_ub) -> (
      let lb_set = Set.add ub_lb (Set.singleton lb_lb) in
      let ub_set = Set.add ub_ub (Set.singleton lb_ub) in
      P (T.Min lb_set, T.Max ub_set)
    )
  
  let create_binop op lexp rexp =
    match lexp, rexp with
    | V lexp_value, V rexp_value -> (
      V (try_eval op lexp_value rexp_value)
    )
    | P (lexp_lb, lexp_ub), V rexp_value -> (
      P (try_eval op lexp_lb rexp_value, try_eval op lexp_ub rexp_value)
    )
    | V lexp_value, P (rexp_lb, rexp_ub) -> (
      match op with
      | Binop.PlusA _ | Binop.PlusPI | Binop.Mult _ | Binop.Shiftlt ->
          P (try_eval op lexp_value rexp_lb, try_eval op lexp_value rexp_ub)
      | Binop.MinusA _ | Binop.MinusPI | Binop.MinusPP | Binop.DivI | Binop.Shiftrt ->
          P (try_eval op lexp_value rexp_ub, try_eval op lexp_value rexp_lb)
      | _ -> L.die InternalError "[EdgeExp.create_value_pair_binop] Merge for operator '%a'
        not implemented" Binop.pp op
    )
    | P (lexp_lb, lexp_ub), P (rexp_lb, rexp_ub) -> (
      (* TODO: Shouldn't we introduce min/max expressions here
       to ensure we truly get lower/upper bounds? This seems incorrect *)
      match op with
      | Binop.PlusA _ | Binop.PlusPI | Binop.Mult _ | Binop.Shiftlt ->
          P (try_eval op lexp_lb rexp_lb, try_eval op lexp_ub rexp_ub)
      | Binop.MinusA _ | Binop.MinusPI | Binop.MinusPP | Binop.DivI | Binop.Shiftrt ->
          P (try_eval op lexp_lb rexp_ub, try_eval op lexp_ub rexp_lb)
      | _ -> L.die InternalError "[EdgeExp.create_value_pair_binop] Merge for operator '%a'
        not implemented" Binop.pp op
    )
  
  let map_accesses bound ~f =
    let rec aux bound =
      let process_min_max args ~f ~g=
        let lb_args, ub_args = Set.fold (fun arg (lb_args, ub_args) ->
          match aux arg with
          | V value -> Set.add value lb_args, Set.add value ub_args
          | P (lb, ub) -> Set.add lb lb_args, Set.add ub ub_args
        ) args (Set.empty, Set.empty) in
  
        let check_const args = if Set.for_all is_const args then f args else g args in
  
        if Set.equal lb_args ub_args then V (check_const lb_args)
        else P (check_const lb_args, check_const ub_args)
        (* let args = Set.fold (fun arg args -> Set.add (aux arg) args) args Set.empty in
    
        if Set.for_all is_const args then (
          let args = match Set.cardinal args with
          | 1 -> Set.add zero args
          | _ -> args
          in
          f args
        )
        else g args *)
      in
  
  
      match bound with
      | Access access -> (
        match f access with
        | V value -> V value
        | P (lb, ub) ->
          if equal lb ub then V lb
          else P (lb, ub)
      )
      | BinOp (op, lexp, rexp) -> create_binop op (aux lexp) (aux rexp)
      | Cast (typ, subexp) -> (
        match aux subexp with
        | V value -> V (Cast (typ, value))
        | P (lb, ub) -> P (Cast (typ, lb), Cast (typ, ub))
      )
      | UnOp (Unop.Neg, exp, typ) -> (
        let process_value value = match value with
        | UnOp (Unop.Neg, _, _) -> value
        | Const (Const.Cint const) -> Const (Const.Cint (IntLit.neg const))
        | _ -> UnOp (Unop.Neg, value, typ)
        in
  
        match aux exp with
        | V value -> V (process_value value)
        | P (lb, ub) -> P (process_value lb, process_value ub)
      )
      | UnOp _ -> assert(false)
      | Max args -> process_min_max args ~f:Set.max_elt ~g:(fun args -> Max args)
      | Min args -> process_min_max args ~f:Set.min_elt ~g:(fun args -> Min args)
      | _ -> V bound
  
  
      (* | UnOp (Unop.Neg, exp, typ) -> (
        let exp = aux exp in
        match exp with
        | UnOp (Unop.Neg, _, _) -> exp
        | Const (Const.Cint const) -> Const (Const.Cint (IntLit.neg const))
        | _ ->  UnOp (Unop.Neg, exp, typ)
      )
      | UnOp (_, _, _) -> assert(false)
      | Max args -> process_min_max args ~f:Set.max_elt ~g:(fun args -> Max args)
      | Min args -> process_min_max args ~f:Set.min_elt ~g:(fun args -> Min args)
      | _ -> bound *)
    in
    aux bound
  
  module Set = Caml.Set.Make(struct
    type nonrec t = t
    let compare = compare
  end)
end

module CallPair = struct
  type pair = (T.call * T.call)
    [@@deriving compare]

  type t =
    | V of T.call
    | P of pair
    [@@deriving compare]

  let to_string call_pair = match call_pair with
  | V call_value -> call_to_string call_value
  | P (lb_call, ub_call) -> 
      F.asprintf "(%s; %s)" 
        (call_to_string lb_call) 
        (call_to_string ub_call)

  let pp fmt call_pair = F.fprintf fmt "%s" (to_string call_pair)

  module Set = Caml.Set.Make(struct
    type nonrec t = t
    let compare = compare
  end)
end


(* type call_pair =
  | CallValue of T.call
  | CallPair of (T.call * T.call)
  [@@deriving compare]

let call_pair_to_string call_pair = match call_pair with
  | CallValue call_value -> call_to_string call_value
  | CallPair (lb_call, ub_call) -> F.asprintf "(%s; %s)" (call_to_string lb_call) (call_to_string ub_call)

let pp_call_pair fmt call_pair = F.fprintf fmt "%s" (call_pair_to_string call_pair)


module CallPairSet = Caml.Set.Make(struct
  type nonrec t = call_pair
  let compare = compare_call_pair
end) *)

let compare = T.compare

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
  [@@deriving compare]

module Set = Caml.Set.Make(struct
  type nonrec t = t
  let compare = compare
end) *)

(* module Set = Caml.Set.Make(struct
  type nonrec t = t
  let compare = compare
end) *)

let equal = [%compare.equal: T.t]

let one = Const (Const.Cint IntLit.one)

let of_int value = Const (Const.Cint (IntLit.of_int value))

let of_int32 value = Const (Const.Cint (IntLit.of_int32 value))

let of_int64 value = Const (Const.Cint (IntLit.of_int64 value))

let is_zero = function 
  | Const const
  | UnOp (Unop.Neg, Const const, _) -> Const.iszero_int_float const
  | _ -> false


let is_one = function Const (Const.Cint const) -> IntLit.isone const | _ -> false

let is_integral_typ typ = Typ.is_int typ || Typ.is_pointer typ

let rec is_formal_variable norm formals tenv = match norm with
  | Max args when Int.equal (Set.cardinal args) 1 -> (
    is_formal_variable (Set.min_elt args) formals tenv
  )
  | Access ae -> (
    let access_base = HilExp.AccessExpression.get_base ae in
    AccessPath.BaseSet.mem access_base formals && (
      (* TODO: hack for now? We want to treat pointer formals as variables
       * so we can derive DCs for them and track their value so we can then
       * calculate their variable bounds later on to track function side-effects *)
      let access_base_typ = snd access_base in
      Typ.is_pointer access_base_typ &&
      match ae with
      | HilExp.AccessExpression.FieldOffset (Dereference _, _)
      | HilExp.AccessExpression.Dereference _ -> (
        Option.exists (HilExp.AccessExpression.get_typ ae tenv) ~f:is_integral_typ
      )
      | _ -> false
    )
  )
  | _ -> false


let is_variable norm formals tenv =
  let rec traverse_exp = function
  | Access ae -> (
    let access_base = HilExp.AccessExpression.get_base ae in
    not (AccessPath.BaseSet.mem access_base formals) || (
      (* TODO: hack for now? We want to treat pointer formals as variables
       * so we can derive DCs for them and track their value so we can then
       * calculate their variable bounds later on to track function side-effects *)
      let access_base_typ = snd access_base in
      Typ.is_pointer access_base_typ &&
      match ae with
      | HilExp.AccessExpression.FieldOffset (Dereference _, _)
      | HilExp.AccessExpression.Dereference _ -> (
        Option.exists (HilExp.AccessExpression.get_typ ae tenv) ~f:is_integral_typ
      )
      | _ -> false
    )
    (* not (AccessPath.BaseSet.mem access_base formals) *)
    (* match Var.get_pvar base_var with
    | Some pvar -> not (Pvar.Set.mem pvar formals)
    | None -> true *)
  )
  | UnOp (_, exp, _) | Cast (_, exp) -> (traverse_exp exp)
  | BinOp (_, lexp, rexp) -> (traverse_exp lexp) || (traverse_exp rexp)
  | Max args | Min args -> Set.exists traverse_exp args
  | _ -> false
  in
  traverse_exp norm


let is_symbolic_const norm formals tenv = not (is_variable norm formals tenv)


let rec is_int exp type_map tenv = match exp with
  | BinOp (_, lexp, rexp) -> is_int lexp type_map tenv && is_int rexp type_map tenv
  | UnOp (_, exp, typ) -> (
    match typ with
    | Some typ -> is_integral_typ typ
    | None -> is_int exp type_map tenv
  )
  | Access access -> (
    match HilExp.AccessExpression.get_typ access tenv with
    | Some typ -> is_integral_typ typ
    | _ -> false
  )
  | Const Const.Cint _ -> true
  | Call (ret_typ, _, _, _) -> is_integral_typ ret_typ
  | _ -> false


let rec get_typ tenv = function
  | Access access_expr -> HilExp.AccessExpression.get_typ access_expr tenv
  | UnOp (_, _, typ_opt) -> typ_opt
  | BinOp ((Lt | Gt | Le | Ge | Eq | Ne | LAnd | LOr), _, _) -> Some (Typ.mk (Typ.Tint Typ.IBool))
  | BinOp (_, e1, e2) -> (
    (* TODO: taken from HilExp.get_typ, same problem as in the comment below *)
    (* TODO: doing this properly will require taking account of language-specific coercion
       semantics. Only return a type when the operands have the same type for now *)
    match get_typ tenv e1, get_typ tenv e2 with
    | Some typ1, Some typ2 when Typ.equal typ1 typ2 -> Some typ1
    | _ -> None 
  )
  | Call (ret_typ, _, _, _) -> Some ret_typ
  | Const (Cfun _) -> None
  | Const (Cint value) -> (
    (* TODO: handle signedness, hack for now *)
    Some (Typ.mk (Typ.Tint (if IntLit.isnegative value then Typ.IInt else Typ.IUInt)))
  )
  | Const (Cfloat _) -> Some (Typ.mk (Typ.Tfloat Typ.FFloat))
  | Const (Cstr _) -> (
    (* TODO: this will need to behave differently depending on whether we're in C++ or Java 
     * make it work for C/C++ for now *)
    Some (Typ.mk_ptr StdTyp.char)
  )
  | Cast (typ, _) -> Some typ
  | _ -> None

let is_integer_condition tenv = function
  | BinOp ((Lt | Gt | Le | Ge | Eq | Ne | LAnd | LOr), lhs, rhs) -> (
    match get_typ tenv lhs, get_typ tenv rhs with
    | Some lhs_typ, Some rhs_typ -> is_integral_typ lhs_typ && is_integral_typ rhs_typ
    | Some typ, None
    | None, Some typ -> is_integral_typ typ
    | _ -> false
  )
  | exp -> (
    match get_typ tenv exp with
    | Some typ -> is_integral_typ typ
    | None -> false
  )


let rec is_return exp = match exp with
  | Access access -> (match access with
    | HilExp.Base (base_var, _) -> Var.is_return base_var
    | _ -> false
  )
  | Max args when Int.equal (Set.cardinal args) 1 -> 
    is_return (Set.min_elt args)
  | _ -> false

let rec evaluate exp value_map default_value = 
  let eval_min_max args f =
    let values = List.map (Set.elements args)
      ~f:(fun arg -> evaluate arg value_map default_value) 
    in
    Option.value_exn (f values ~compare:Float.compare)
  in

  match exp with
  | Access access -> (
    match AccessExpressionMap.find_opt access value_map with
    | Some value -> value
    | None -> default_value
  )
  | Const (Const.Cint c) -> IntLit.to_float c
  | BinOp (op, lexp, rexp) -> (
    let l_value = evaluate lexp value_map default_value in
    let r_value = evaluate rexp value_map default_value in
    match op with
    | Binop.PlusA _ -> l_value +. r_value
    | Binop.MinusA _ -> l_value -. r_value
    | Binop.Mult _ -> l_value *. r_value
    | Binop.DivI -> l_value /. r_value
    | _ -> assert(false)
  )
  | Cast (_, subexp) -> (
    evaluate subexp value_map default_value

    (* TODO: this should probably be language specific *)
    (* let value = evaluate subexp value_map default_value in
    if Typ.is_int typ then (
      if Typ.is_unsigned_int typ then Float.max value 0.0 |> Float.round_down
      else Float.round_down value
    ) else value *)
  )
  | UnOp (Unop.Neg, subexp, _) -> -.(evaluate subexp value_map default_value)
  | Max args -> eval_min_max args List.max_elt
  | Min args -> eval_min_max args List.min_elt
  | _ -> assert(false)


let merge exp const_opt = match const_opt with
  | Some (op, const) -> (
    if is_zero exp then (
      match op with
      | Binop.PlusA _ -> Const (Const.Cint const)
      | Binop.MinusA _ -> Const (Const.Cint (IntLit.neg const))
      | _ -> assert(false)
    )
    else (
      if IntLit.isnegative const then (
        let const_neg = (Const (Const.Cint (IntLit.neg const))) in
        match op with
        | Binop.MinusA kind -> try_eval (Binop.PlusA kind) exp const_neg
        | Binop.PlusA kind -> try_eval (Binop.MinusA kind) exp const_neg
        | Binop.Mult kind -> (
          if IntLit.isminusone const then UnOp (Unop.Neg, exp, None)
          else try_eval (Binop.Mult kind) exp (Const (Const.Cint const))
        )
        | _ -> try_eval op exp (Const (Const.Cint const))
      )
      else try_eval op exp (Const (Const.Cint const))
    )
  )
  | None -> exp


let split_exp exp = 
  let rec aux exp last_op acc = match exp with
  | Cast (_, exp) -> aux exp last_op acc
  | BinOp (op, lexp, rexp) -> (
    match op with
    | Binop.PlusA _ -> (
      match last_op with
      | Binop.PlusA _ -> (aux lexp op acc) @ (aux rexp op acc)
      | Binop.MinusA _ -> (aux lexp last_op acc) @ (aux rexp last_op acc)
      | _ -> assert(false)
    )
    | Binop.MinusA typ -> (
      match last_op with
      | Binop.PlusA _ -> (aux lexp (Binop.PlusA typ) acc) @ (aux rexp op acc)
      | Binop.MinusA _ -> (aux lexp op acc) @ (aux rexp (Binop.PlusA typ) acc)
      | _ -> assert(false)
    )
    | _ -> (
      match last_op with
      | Binop.MinusA _ -> UnOp (Unop.Neg, exp, None) :: acc
      | _ -> exp :: acc
    )
  )
  | subexp -> (
    match last_op with
    | Binop.MinusA _ -> UnOp (Unop.Neg, subexp, None) :: acc
    | _ -> subexp :: acc
  )
  in
  aux exp (Binop.PlusA None) []


let merge_exp_parts parts = Option.value (List.reduce parts ~f:(fun lhs rhs -> 
  match lhs, rhs with
  | UnOp (Unop.Neg, _, _), UnOp (Unop.Neg, rsubexp, _) -> try_eval (Binop.MinusA None) lhs rsubexp
  | _ , UnOp (Unop.Neg, rsubexp, _) -> try_eval (Binop.MinusA None) lhs rsubexp
  | UnOp (Unop.Neg, lsubexp, _), _ -> try_eval (Binop.MinusA None) rhs lsubexp
  | _ -> try_eval (Binop.PlusA None) lhs rhs
  )) ~default:zero


let rec separate exp = 
  let symmetric_op binop = match binop with
  | Binop.PlusA ikind_opt -> Binop.MinusA ikind_opt
  | Binop.MinusA ikind_opt -> Binop.PlusA ikind_opt
  | _ -> assert(false)
  in

  match exp with
  | Access _ -> exp, None
  | Const (Const.Cint c) -> zero, Some (Binop.PlusA None, c)
  | BinOp (op, lexp, rexp) -> (
    let lexp_derived, l_const_opt = separate lexp in
    let rexp_derived, r_const_opt = separate rexp in
    let lexp_derived, rexp_derived, const_part = match op with
    | Binop.PlusA _
    | Binop.PlusPI -> (
      match l_const_opt, r_const_opt with
      | Some (l_op, l_const), Some (r_op, r_const) -> (
        match l_op, r_op with
        | Binop.PlusA _, Binop.PlusA _ -> lexp_derived, rexp_derived, Some (l_op, IntLit.add l_const r_const)
        | Binop.MinusA _, Binop.PlusA _ -> (
          lexp_derived, rexp_derived, Some (r_op, IntLit.sub r_const l_const)
        )
        | Binop.MinusA _, Binop.MinusA _ -> lexp_derived, rexp_derived, Some (l_op, IntLit.add r_const l_const)        
        | Binop.PlusA _, Binop.Mult _ -> lexp_derived, merge rexp_derived r_const_opt, Some (l_op, r_const)
        | Binop.Shiftrt, Binop.PlusA _
        | Binop.Mult _, Binop.PlusA _ -> merge lexp_derived l_const_opt, rexp_derived, Some (r_op, r_const)
        | _ -> (
          console_log "exp: %a,  lop: %s, rop: %s\n" pp exp (Binop.str Pp.text l_op) (Binop.str Pp.text r_op);
          assert(false)
        )
      )
      | Some (l_op, l_const), None -> (
        match l_op with
        | Binop.PlusA _ | Binop.MinusA _ -> lexp_derived, rexp_derived, Some (l_op, l_const)
        | Binop.Shiftrt -> (
          (* [(lexp >> l_const) + rexp] no way to go, merge l_const back to lexp *)
          merge lexp_derived l_const_opt, rexp_derived, None
        )
        | _ -> assert(false)
      )
      | None, Some (r_op, r_const) -> (
        match r_op with
        | Binop.PlusA _ | Binop.MinusA _ -> lexp_derived, rexp_derived, Some (r_op, r_const)
        | Binop.Shiftrt -> (
          lexp_derived, merge rexp_derived r_const_opt, None
          (* debug_log "LEXP: %a   REXP: %a\n" pp lexp_derived pp rexp_derived; *)
          (* assert(false) *)
        )
        | _ -> assert(false)
      )
      | None, None -> lexp_derived, rexp_derived, None
    )
    | Binop.MinusA typ_opt -> (
      match l_const_opt, r_const_opt with
      | Some (l_op, l_const), Some (r_op, r_const) -> (
        match l_op, r_op with
        | Binop.PlusA _, Binop.PlusA _ -> 
          lexp_derived, rexp_derived, Some (l_op, IntLit.sub l_const r_const)
        | Binop.MinusA _, Binop.PlusA _
        | Binop.PlusA _, Binop.MinusA _ ->
          lexp_derived, rexp_derived, Some (l_op, IntLit.add l_const r_const)
        | Binop.MinusA _, Binop.MinusA _ -> (
          let const = IntLit.add (IntLit.neg l_const) r_const in
          let const_op = if IntLit.isnegative const then Binop.MinusA typ_opt
          else Binop.PlusA typ_opt in
          lexp_derived, rexp_derived, Some (const_op, const)
        )
        | Binop.Mult _, Binop.PlusA _
        | Binop.Mult _, Binop.MinusA _ ->
          merge lexp_derived l_const_opt, rexp_derived, Some (symmetric_op r_op, r_const)
        | Binop.PlusA _, Binop.Mult _
        | Binop.MinusA _, Binop.Mult _ ->
          lexp_derived, merge rexp_derived r_const_opt, Some (l_op, l_const)
        | _ -> (
          L.die InternalError "l_op: %a, r_op: %a" Binop.pp l_op Binop.pp r_op
        )
      )
      | Some (l_op, l_const), None -> (
        match l_op with
        | Binop.PlusA _ | Binop.MinusA _ -> lexp_derived, rexp_derived, Some (l_op, l_const)
        | Binop.Mult _ | Binop.DivI | Binop.Shiftlt | Binop.Shiftrt ->
          merge lexp_derived l_const_opt, rexp_derived, None
        | _ -> assert(false)
      )
      | None, Some (r_op, r_const) -> (
        match r_op with
        | Binop.PlusA _ | Binop.MinusA _ -> lexp_derived, rexp_derived, Some (symmetric_op r_op, r_const)
        | Binop.Mult _ | Binop.DivI | Binop.Shiftlt | Binop.Shiftrt ->
          lexp_derived, merge rexp_derived r_const_opt, None
        | _ -> assert(false)
      )
      | None, None -> lexp_derived, rexp_derived, None
    )
    | Binop.Shiftrt -> (
      match l_const_opt, r_const_opt with
      | Some (l_op, l_const), Some (r_op, r_const) -> (
        match l_op, r_op with
        | Binop.PlusA _, Binop.PlusA _ -> (
          merge lexp_derived l_const_opt, rexp_derived, Some (Binop.Shiftrt, r_const)
          (* assert(false) *)
        )
        | Binop.Shiftrt, Binop.PlusA _ -> (
          lexp_derived, rexp_derived, Some (Binop.Shiftrt, IntLit.add l_const r_const)
          (* assert(false) *)
        )
        | _ -> (
          assert(false)
          (* let lexp_merged = merge lexp_derived l_const_opt in
          lexp_merged, rexp_derived, Some (Binop.Shiftrt, r_const) *)
        )
      )
      | Some (l_op, _), None -> (
        match l_op with
        | Binop.PlusA _ -> (
          (* (x + c) >> y  *)
          merge lexp_derived l_const_opt, rexp_derived, None
        )
        | _ -> (
          (* TODO *)
          assert(false)
        )
      )
      | None, Some (r_op, r_const) -> (
        match r_op with
        | Binop.PlusA _ -> (
        lexp_derived, rexp_derived, Some (Binop.Shiftrt, r_const)
        )
        | _ -> assert(false)
      )
      | None, None -> lexp_derived, rexp_derived, None
    )
    | _ -> merge lexp_derived l_const_opt, merge rexp_derived r_const_opt, None
    in
    (* zero, None *)

    (* debug_log "LEXP_DERIVED: %a   |   REXP_DERIVED: %a\n" pp lexp_derived pp rexp_derived; *)
    match is_zero lexp_derived, is_zero rexp_derived with
    | true, true -> zero, const_part
    | false, true -> lexp_derived, const_part
    | true, false -> (
      match op with
      | Binop.MinusA _ -> UnOp (Unop.Neg, rexp_derived, None), const_part
      | Binop.PlusA _ -> rexp_derived, const_part
      | Binop.Shiftrt -> zero, None
      | _ -> assert(false)
    )
    | false, false -> (
      if equal lexp_derived rexp_derived then (
        match op with
        (* | Binop.MinusA _ -> Some (zero, IntLit.add l_const (IntLit.neg r_const)) *)
        | Binop.MinusA _ -> zero, const_part
        | Binop.PlusA _ 
        | Binop.Shiftrt -> try_eval op lexp_derived rexp_derived, const_part
        | Binop.Mult _ -> (
          (* TODO: need to make sure if this is correct? *)
          try_eval op lexp_derived rexp_derived, const_part
        )
        | _ -> assert(false)
      )
      else (
        match op with
        | Binop.MinusA _
        | Binop.PlusA _
        | Binop.DivI
        | Binop.Mult _
        | Binop.Shiftrt 
        | Binop.Shiftlt -> (
          try_eval op lexp_derived rexp_derived, const_part
        )
        | Binop.PlusPI
        | Binop.MinusPI
        | Binop.MinusPP -> (
          (* TODO: Should we handle pointer arithmetic differently? *)
          try_eval op lexp_derived rexp_derived, const_part
        )
        | _ -> (
          debug_log "%a %s %a\n" pp lexp_derived (Binop.str Pp.text op) pp rexp_derived;
          match const_part with
          | Some (const_op, rhs_const) -> (
            (* debug_log "Const part: %s %a\n" (Binop.str Pp.text const_op) IntLit.pp rhs_const; *)
            assert(false)
          )
          | None -> assert(false)
        )
      )
    )
  )
  | Cast (typ, exp) -> (
    let derived_exp, const_opt = separate exp in
    Cast (typ, derived_exp), const_opt
  )
  | UnOp (unop, exp, typ) -> (
    match unop with
    | Unop.Neg -> (
      let derived_exp, const_opt = separate exp in
      (* let derived_exp = if is_zero derived_exp then derived_exp else UnOp (unop, derived_exp, typ) in *)
      match const_opt with
      | Some (binop, const) -> (
        if IntLit.iszero const then UnOp (unop, derived_exp, typ), None
        else (
          match binop with
          | Binop.PlusA ikind_opt -> UnOp (unop, derived_exp, typ), Some (Binop.MinusA ikind_opt, const)
          | Binop.MinusA ikind_opt -> UnOp (unop, derived_exp, typ), Some (Binop.PlusA ikind_opt, const)
          | _ -> assert(false)
        )
      )
      | None -> (
        let ikind = Option.value_map typ ~default:None ~f:(fun x -> Typ.get_ikind_opt x) in
        derived_exp, Some (Binop.Mult ikind, IntLit.minus_one)
      )
      (* | None -> UnOp (unop, derived_exp, typ), None *)
    )
    | _ -> assert(false)
  )
  | Max _ | Min _ -> (
    (* TODO: should we somehow separate min/max expressions? *)
    exp, None
  )
  | _ -> exp, None


let rec expand_multiplication exp const_opt =
  let process_div lexp rexp const_opt = match const_opt with
  | Some acc_const -> (
    match rexp with
    | Const (Const.Cint rexp_const) -> (
      if IntLit.iszero (IntLit.rem acc_const rexp_const) then (
        let acc_const = IntLit.div acc_const rexp_const in
        let acc_const = if IntLit.isone acc_const then None else Some acc_const in
        expand_multiplication lexp acc_const
      ) else (
        (* what the hell? fix this *)
        assert(false);
      )
    )
    | _ -> (
      let lexp = expand_multiplication lexp const_opt in
      let rexp = expand_multiplication rexp None in
      BinOp (Binop.DivI, lexp, rexp)
    )
  )
  | None -> (
    let lexp = expand_multiplication lexp None in
    let rexp = expand_multiplication rexp None in
    BinOp (Binop.DivI, lexp, rexp)
  )
  in

  match exp with
  | Const (Const.Cint c) -> (
    match const_opt with
    | Some const -> Const (Const.Cint (IntLit.mul c const))
    | None -> exp
  )
  | Cast (typ, exp) -> Cast (typ, expand_multiplication exp const_opt)
  | Max args -> (
    match Set.cardinal args with
    | 1 ->
      Max ((expand_multiplication (Set.min_elt args) const_opt) |> Set.singleton)
    | _ -> (
      (* TODO: probably leave as is, in general we cannot simply multiply each
       * argument, i.e., C * max(arg_2,arg_2, ...) != max(C * arg_1, C * arg_2, ...) *)
      let args = Set.map (fun arg -> expand_multiplication arg None) args in
      Option.value_map const_opt ~default:(Max args) ~f:(fun c -> 
        try_eval (Binop.Mult None) (Const (Const.Cint c)) (Max args)
      )
    )
  )
  | BinOp (Binop.Mult _, Const (Const.Cint c), subexp)
  | BinOp (Binop.Mult _, subexp, Const (Const.Cint c)) -> (
    let const = match const_opt with
    | Some old_const -> eval_consts (Binop.Mult None) c old_const
    | None -> c
    in
    expand_multiplication subexp (Some const)
  )
  | BinOp (Binop.Mult _ as op, lexp, rexp) -> (
    let rec multiply_sub_exps x y =
    let x_parts = split_exp x in
    let y_parts = split_exp y in
    let multiplied_parts = List.fold x_parts ~init:[] ~f:(fun acc x_part ->
      List.fold y_parts ~init:acc ~f:(fun parts_acc y_part ->
        let mult_exp = match x_part, y_part with
        | Const (Const.Cint c), _ -> (
          let exp = if IntLit.isone c then y_part else try_eval op x_part y_part in
          expand_multiplication exp const_opt
        )
        | _, Const (Const.Cint c) -> (
          let exp = if IntLit.isone c then x_part else try_eval op x_part y_part in
          expand_multiplication exp const_opt
        )
        | BinOp (Binop.DivI, lexp_numer, lexp_denom), BinOp (Binop.DivI, rexp_numer, rexp_denom) -> (
          let numerator = multiply_sub_exps lexp_numer rexp_numer in
          let denominator = multiply_sub_exps lexp_denom rexp_denom in
          let numerator_parts = split_exp numerator in
          let parts = List.map numerator_parts ~f:(fun part -> 
            match part with
            | UnOp (Unop.Neg, subexp, typ) -> UnOp (Unop.Neg, BinOp (Binop.DivI, subexp, denominator), typ)
            | _ -> BinOp (Binop.DivI, part, denominator)
          )
          in
          merge_exp_parts parts
        )
        | _ -> (
          let mult_exp = try_eval op x_part y_part in
          let mult_exp = match const_opt with
          | Some const -> try_eval op mult_exp (Const (Const.Cint const))
          | None -> mult_exp
          in
          mult_exp
        )
        in
        mult_exp :: parts_acc
      )
    ) 
    in

    let exp = merge_exp_parts multiplied_parts in
    assert(not (equal exp zero));
    exp
    in

    let lexp = expand_multiplication lexp None in
    let rexp = expand_multiplication rexp None in
    multiply_sub_exps lexp rexp
  )
  | BinOp ((Binop.PlusA _) as op, lexp, rexp)
  | BinOp ((Binop.MinusA _) as op, lexp, rexp) -> (
    let lexp = expand_multiplication lexp const_opt in
    let rexp = expand_multiplication rexp const_opt in
    BinOp (op, lexp, rexp)
  )
  | BinOp (Binop.DivI, lexp, rexp) -> process_div lexp rexp const_opt
  | BinOp (Binop.Shiftrt, lexp, Const (Const.Cint power_value)) -> (
    let lexp = expand_multiplication lexp const_opt in
    BinOp (Binop.Shiftrt, lexp, Const (Const.Cint power_value))
    (* Transform to division *)
    (* let divisor = IntLit.of_int (Int.pow 2 (IntLit.to_int_exn power_value)) in
    process_div lexp (Const (Const.Cint divisor)) const_opt *)
  )
  | BinOp (Binop.Shiftrt, lexp, rexp) -> (
    Option.value_map const_opt ~default:exp ~f:(fun c ->
      (* C * (x >> y)  --->  (C * x) >> y
       * this is probably incorrect in edge cases due to
       * the order of operations which should matter? *)
      let lexp = try_eval (Binop.Mult None) (Const (Const.Cint c)) lexp in
      BinOp (Binop.Shiftrt, lexp, rexp)
    )
    (* match const_opt with
    | Some const -> (

      let lexp = try_eval (Binop.Mult None) (Const (Const.Cint const)) lexp in
      BinOp (Binop.Shiftrt, lexp, rexp)
    )
    | None -> exp *)
  )
  | _ -> (
    Option.value_map const_opt ~default:exp ~f:(fun c ->
      try_eval (Binop.Mult None) (Const (Const.Cint c)) exp
    )
    (* match const_opt with
    | Some const -> try_eval (Binop.Mult None) (Const (Const.Cint const)) exp
    | None -> exp *)
  )


let simplify exp = 
  (* debug_log "@[<v2>[Simplify] %a@," pp exp; *)
  let expanded_exp = expand_multiplication exp None in
  (* debug_log "Expanded: %a@," pp expanded_exp; *)
  let non_const_part, const_opt = separate expanded_exp in
  let simplified_exp = merge non_const_part const_opt in
  (* debug_log "Simplified: %a@]@," pp simplified_exp; *)
  simplified_exp


let rec remove_casts_of_consts exp integer_widths = match exp with
  | Cast (typ, Const (Const.Cint c)) -> (
    (* Get rid of unnecessary casts over constants. This should be language
     * specific probably. Should work correctly for C/C++ for now (I think). *)    
    if Typ.is_unsigned_int typ && IntLit.isnegative c then (
      match Typ.get_ikind_opt typ with
      | Some ikind -> (
        let type_max_value = Z.((Typ.range_of_ikind integer_widths ikind |> snd) + ~$1) in
        let value_after_cast = IntLit.of_big_int Z.(type_max_value - (IntLit.to_big_int c)) in
        Const (Const.Cint value_after_cast)
      )
      | None -> L.die InternalError 
        "Missing ikind data of integer type: %a. Cannot remove cast of constant"
        Typ.(pp Pp.text) typ
    )
    else Const (Const.Cint c)
  )
  | BinOp (op, lexp, rexp) -> 
    BinOp (op, remove_casts_of_consts lexp integer_widths, remove_casts_of_consts rexp integer_widths)
  | UnOp (unop, exp, typ_opt) -> 
    UnOp (unop, remove_casts_of_consts exp integer_widths, typ_opt)
  | Call (typ, procname, args, loc) -> (
    let args = (List.map args ~f:(fun (arg, typ) -> remove_casts_of_consts arg integer_widths, typ)) in
    Call (typ, procname, args, loc)
  )
  | Max args -> Max (Set.map (fun arg -> remove_casts_of_consts arg integer_widths) args)
  | Min args -> Min (Set.map (fun arg -> remove_casts_of_consts arg integer_widths) args)
  | _ -> exp

let rec transform_shifts exp = match exp with
  | Max args when Int.equal (Set.cardinal args) 1 -> (
    let arg, conditions = transform_shifts (Set.min_elt args) in
    arg, Set.add (BinOp (Binop.Ge, arg, zero)) conditions
  )
  | Cast (typ, exp) -> (
    let exp, exp_conditions = transform_shifts exp in
    Cast (typ, exp), exp_conditions
  )
  | BinOp (Binop.Shiftrt, lexp, rexp) -> (
    let lexp, lexp_conditions = transform_shifts lexp in

    match evaluate_const_exp rexp with
    | Some rexp_value -> (
      assert(IntLit.isnegative rexp_value |> not);
      if IntLit.iszero rexp_value then lexp, lexp_conditions
      else (
        (* Transform to division *)
        let divisor = IntLit.of_int (Int.pow 2 (IntLit.to_int_exn rexp_value)) in
        BinOp (Binop.DivI, lexp, Const (Const.Cint divisor)), lexp_conditions
      )
    )
    | None -> (
      let rexp, rexp_conditions = transform_shifts rexp in
      let conditions = Set.union lexp_conditions rexp_conditions in
      BinOp (Binop.DivI, lexp, rexp), Set.add (BinOp (Binop.Ge, rexp, zero)) conditions
    )
  )
  | BinOp (op, lexp, rexp) -> (
    let lexp, lexp_conditions = transform_shifts lexp in
    let rexp, rexp_conditions = transform_shifts rexp in
    BinOp (op, lexp, rexp), Set.union lexp_conditions rexp_conditions
  )
  | _ -> exp, Set.empty


(* let rec of_exp exp ident_map typ type_map =
  let original_exp = exp in

  let aux exp = match exp with
  | Exp.BinOp (op, lexp, rexp) -> (
    let lexp = of_exp lexp ident_map typ type_map in
    let rexp = of_exp rexp ident_map typ type_map in
    match lexp, rexp with
    | Const Const.Cint c1, Const Const.Cint c2 -> Const (Const.Cint (eval_consts op c1 c2))
    | _ -> BinOp (op, lexp, rexp)
  )
  | Exp.UnOp (Unop.Neg, Exp.Const Const.Cint c, _) -> Const (Const.Cint (IntLit.neg c))
  | Exp.UnOp (op, sub_exp, _) -> UnOp (op, of_exp sub_exp ident_map typ type_map, Some typ)
  | Exp.Var ident -> Ident.Map.find ident ident_map |> fst
  | Exp.Cast (_, exp) -> of_exp exp ident_map typ type_map
  | Exp.Lvar pvar -> (
    let pvar_typ = match PvarMap.find_opt pvar type_map with
    | Some typ -> typ
    | None -> (
      (* A little hack-around. As far as I know, there is currently no way to query the type
       * of a global, let alone query which global variables exists at all. This case occurs
       * when there is a global variable used as a function argument and it was not used anywhere
       * else before that -> we dont have the type information in our type_map. *)
      if Exp.equal exp original_exp then typ
      else L.die InternalError "[EdgeExp.of_exp] Missing type information for Pvar '%a'" Pvar.(pp Pp.text) pvar;
    )
    in
    let ap_base = AccessPath.base_of_pvar pvar pvar_typ in
    Access (HilExp.AccessExpression.base ap_base)
  )
  | Exp.Const const -> Const const
  | Exp.Sizeof {nbytes} -> (
    match nbytes with
    | Some size -> Const (Const.Cint (IntLit.of_int size))
    | _ -> assert(false)
  )
  | Exp.Lindex _ -> (
    let resolver = access_path_id_resolver ident_map in 
    let accesses = access_of_exp ~include_array_indexes:true exp typ ~f_resolve_id:resolver in
    assert (Int.equal (List.length accesses) 1);
    let access = List.hd_exn accesses in
    Access access
  )
  | _ -> L.(die InternalError)"[EdgeExp.of_exp] Unsupported expression %a!" Exp.pp exp
  in
  aux exp *)


(* let rec of_hil_exp exp id_resolver = match exp with
  | HilExp.AccessExpression access -> (
    let base_var = HilExp.AccessExpression.get_base access |> fst in
    match Var.get_ident base_var with
    | Some ident -> (
      (* Idents should occur only for previously unsubstituted
       * return idents of function calls, try to substitute now *)
      id_resolver ident
    )
    | None -> Access access
  )
  | HilExp.Constant const -> Const const
  | HilExp.Cast (cast_type, HilExp.Constant (Const.Cint c)) -> (
    (* TODO: do something based on signedness of the int type and value of const *)
    assert(Typ.is_int cast_type || Typ.is_pointer_to_int cast_type);
    Const (Const.Cint c)
  )
  | HilExp.Cast (cast_type, subexp) -> Cast (cast_type, of_hil_exp subexp id_resolver)
  | HilExp.BinaryOperator (op, lexp, rexp) -> (
    let lexp = of_hil_exp lexp id_resolver in
    let rexp = of_hil_exp rexp id_resolver in
    BinOp (op, lexp, rexp)
  )
  | HilExp.UnaryOperator (Unop.Neg, HilExp.Constant Const.Cint c, _) ->
      Const (Const.Cint (IntLit.neg c))
  | HilExp.UnaryOperator (op, subexp, subexp_typ) ->
      UnOp (op, of_hil_exp subexp id_resolver, subexp_typ)
  | HilExp.Sizeof {nbytes} -> (
    match nbytes with
    | Some size -> Const (Const.Cint (IntLit.of_int size))
    | None -> L.die InternalError "TODO: HilExp.Sizeof missing size information"
  )
  | _ -> L.(die InternalError)"[EdgeExp.of_exp] Unsupported expression %a!" HilExp.pp exp *)


let base_of_id id typ = (Var.of_id id, typ)

let base_of_pvar pvar typ = (Var.of_pvar pvar, typ)

let of_pvar pvar typ = HilExp.AccessExpression.address_of_base (base_of_pvar pvar typ)


let why3_get_vsymbol name (prover_data : prover_data) = 
  match StringMap.find_opt name prover_data.vars with
  | Some vs -> vs
  | None -> (
    let new_symbol = Why3.Term.create_vsymbol (Why3.Ident.id_fresh name) Why3.Ty.ty_real in
    prover_data.vars <- (StringMap.add name new_symbol prover_data.vars);
    new_symbol
  )


let rec is_typ_unsigned (typ : Typ.t) = match typ.desc with
  | Typ.Tint ikind -> Typ.ikind_is_unsigned ikind
  | Typ.Tfloat _ | Tstruct _ -> false
  | Tarray {elt} -> is_typ_unsigned elt
  | Tptr (ptr_type, _) -> is_typ_unsigned ptr_type
  | _ -> (
    debug_log "Unknown type: %s\n" (Typ.desc_to_string typ.desc);
    assert(false);
  )


let rec to_why3_expr exp tenv (prover_data : prover_data) =
  (* console_log "@[Exp: %a@,@]" pp exp; *)
  let plus_symbol : Why3.Term.lsymbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix +"] in
  let minus_symbol : Why3.Term.lsymbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix -"] in
  let unary_minus_symbol : Why3.Term.lsymbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["prefix -"] in
  let mul_symbol : Why3.Term.lsymbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix *"] in
  let div_symbol : Why3.Term.lsymbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix /"] in
  let ge_symbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix >="] in
  let gt_symbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix >"] in
  let le_symbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix <="] in
  let lt_symbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix <"] in

  let two_const : Why3.Term.term = Why3.Term.t_real_const (Why3.BigInt.of_int 2) in
  let zero_const = Why3.Term.t_real_const (Why3.BigInt.of_int 0) in

  let why3_make_access_term name typ =
    let var = why3_get_vsymbol name prover_data in
    let var_term = Why3.Term.t_var var in
    if is_typ_unsigned typ then (
      let condition = Why3.Term.ps_app ge_symbol [var_term;zero_const] in
      var_term, Why3.Term.Sterm.singleton condition
    )
    else var_term, Why3.Term.Sterm.empty
  in

  let mk_const_term value = Why3.Term.t_real_const (Why3.BigInt.of_int value) in

  let convert_min_max symbol args =
    let why3_args, type_constraints = Set.fold (fun arg (args, constraints) ->
      let why3_arg, arg_type_constraints = to_why3_expr arg tenv prover_data in
      why3_arg :: args, Why3.Term.Sterm.union arg_type_constraints constraints
    ) args ([], Why3.Term.Sterm.empty)
    in
    
    assert(Set.cardinal args > 0);
    if Set.cardinal args < 2 then (
      let arg = List.hd_exn why3_args in
      let ite_condition = Why3.Term.ps_app symbol [arg; zero_const] in

      (* TODO: should we include conditions "x >= 0" for each "max(x, 0)" expression? *)
      arg, Why3.Term.Sterm.add ite_condition type_constraints
    ) else (
      (* TODO: Could we potentially extract single max(...) argument based on
       * currently examined bound parameter when checking monotony? (with some 
       * exceptions of course) This could help use get rid of max expressions in
       * Z3 altogether for those usecases.
       * This seems to be necessary if we want to avoid Z3 loops and unknown results *)
      let min_max_expr = List.reduce_exn why3_args ~f:(fun x y ->
        Why3.Term.t_if (Why3.Term.ps_app symbol [x; y]) x y
      )
      in
      min_max_expr, type_constraints
    )
  in

  match exp with
  | Const (Const.Cint const) -> mk_const_term (IntLit.to_int_exn const), Why3.Term.Sterm.empty
  | Const (Const.Cfloat const) -> mk_const_term (int_of_float const), Why3.Term.Sterm.empty
  | Call (typ, procname, _, _) -> (
    (* Treat function without summary as constant *)
    why3_make_access_term (Procname.to_string procname) typ
  )
  | Access access -> (
    match HilExp.AccessExpression.get_typ access tenv with
    | Some typ -> why3_make_access_term (F.asprintf "%a" HilExp.AccessExpression.pp access) typ
    | _ -> assert(false)
  )
  | Cast (typ, subexp) -> (
    let why3_subexp, constraints = to_why3_expr subexp tenv prover_data in
    let constraints = if Typ.is_unsigned_int typ
    then Why3.Term.Sterm.add (Why3.Term.t_app_infer ge_symbol [why3_subexp; zero_const]) constraints
    else constraints
    in
    why3_subexp, constraints
  )
  | BinOp (op, lexp, rexp) -> (
    let why3_lexp, why3_lexp_constraints = to_why3_expr lexp tenv prover_data in
    let why3_rexp, why3_rexp_constraints = to_why3_expr rexp tenv prover_data in
    
    let aux expr_why3 (typ_opt : Typ.ikind option) = match typ_opt with
    | Some ikind when Typ.ikind_is_unsigned ikind -> expr_why3, Why3.Term.Sterm.empty
    | _ -> expr_why3, Why3.Term.Sterm.empty
    in

    let eval_power exp = match exp with
    | Const (Const.Cint power_value) -> (
      let divisor = mk_const_term (Int.pow 2 (IntLit.to_int_exn power_value)) in
      divisor
    )
    | _ -> why3_rexp
    in
    
    let expr_z3, constraints = match op with
    | Binop.Lt -> Why3.Term.ps_app lt_symbol [why3_lexp;why3_rexp], Why3.Term.Sterm.empty
    | Binop.Le -> Why3.Term.ps_app le_symbol [why3_lexp;why3_rexp], Why3.Term.Sterm.empty
    | Binop.Gt -> Why3.Term.ps_app gt_symbol [why3_lexp;why3_rexp], Why3.Term.Sterm.empty
    | Binop.Ge -> Why3.Term.ps_app ge_symbol [why3_lexp;why3_rexp], Why3.Term.Sterm.empty
    | Binop.Eq -> Why3.Term.t_equ why3_lexp why3_rexp, Why3.Term.Sterm.empty
    | Binop.Ne -> Why3.Term.t_neq why3_lexp why3_rexp, Why3.Term.Sterm.empty
    | Binop.MinusA ikind_opt -> aux (Why3.Term.t_app_infer minus_symbol [why3_lexp; why3_rexp]) ikind_opt
    | Binop.PlusA ikind_opt -> aux (Why3.Term.t_app_infer plus_symbol [why3_lexp; why3_rexp]) ikind_opt
    | Binop.Mult ikind_opt -> aux (Why3.Term.t_app_infer mul_symbol [why3_lexp; why3_rexp]) ikind_opt
    | Binop.PlusPI -> Why3.Term.t_app_infer plus_symbol [why3_lexp; why3_rexp], Why3.Term.Sterm.empty
    | Binop.MinusPI | Binop.MinusPP -> Why3.Term.t_app_infer minus_symbol [why3_lexp; why3_rexp], Why3.Term.Sterm.empty
    | Binop.DivI -> (
      let conditions = if is_const rexp then (
        assert(not (is_zero rexp));
        Why3.Term.Sterm.empty
      )
      else Why3.Term.Sterm.singleton (Why3.Term.t_neq_simp why3_rexp zero_const)
      in
      Why3.Term.t_app_infer div_symbol [why3_lexp; why3_rexp], conditions
    )
    | Binop.Shiftrt -> (
      (* Assumption: valid unsigned shifting *)
      let rexp = eval_power rexp in
      let condition = Why3.Term.t_app_infer ge_symbol [why3_rexp; zero_const] in
      let expr_why3 = Why3.Term.t_app_infer div_symbol [why3_lexp; rexp] in
      expr_why3, Why3.Term.Sterm.singleton condition
    )
    | Binop.Shiftlt -> (
      (* Assumption: valid unsigned shifting *)
      let rexp = eval_power rexp in
      let condition = Why3.Term.t_app_infer ge_symbol [why3_rexp; zero_const] in
      let expr_why3 = Why3.Term.t_app_infer mul_symbol [why3_lexp; rexp] in
      expr_why3, Why3.Term.Sterm.singleton condition
    )
    | _ -> L.(die InternalError)"[EdgeExp.T.to_why3_expr] Expression '%a' contains invalid binary operator!" pp exp
    in
    expr_z3, Why3.Term.Sterm.union constraints (Why3.Term.Sterm.union why3_lexp_constraints why3_rexp_constraints)
  )
  | UnOp (Unop.Neg, subexp, _) -> (
    let subexp, conditions = to_why3_expr subexp tenv prover_data in
    Why3.Term.t_app_infer unary_minus_symbol [subexp], conditions
  )
  | Max max_args -> convert_min_max ge_symbol max_args
  | Min min_args -> convert_min_max le_symbol min_args
  | Const _ -> (
    L.(die InternalError) "[EdgeExp.T.to_why3_expr] Expression '%a' contains invalid const!" pp exp
  )
  | UnOp _ -> (
    L.(die InternalError) "[EdgeExp.T.to_why3_expr] Unsupported UnOp Expression '%a'" pp exp
  )
  | Inf -> (
    L.(die InternalError) "[EdgeExp.T.to_why3_expr] Infinity not supported'%a'" pp exp 
  )
  | Symbolic _ -> (
    L.(die InternalError) "[EdgeExp.T.to_why3_expr] Symbolic expression not supported'%a'" pp exp 
  )
  (* | exp -> L.(die InternalError)"[EdgeExp.T.to_why3_expr] Expression '%a' contains invalid element!" pp exp *)


(* TODO: rewrite to be more general, include preconditions and reference value as parameters *)
let rec always_positive_why3 exp tenv (prover_data : prover_data) =
  let aux = function 
  | Const (Const.Cint x) -> not (IntLit.isnegative x)
  | Const (Const.Cfloat x) -> Float.(x >= 0.0)
  | Access access -> (
    let access_typ_opt = HilExp.AccessExpression.get_typ access tenv in
    match access_typ_opt with
    | Some access_typ -> (
      match access_typ.desc with
      | Typ.Tint ikind -> Typ.ikind_is_unsigned ikind
      | _ -> false
    )
    | None -> false
  )
  | x -> always_positive_why3 x tenv prover_data
  in

  match exp with
  | Max args -> (
    (* let sorted_args = List.sort args ~compare:(fun x y -> match x, y with
    | Const _, Const _ | Access _, Access _ -> 0
    | Const _, _ -> -1
    | _, Const _ -> 1
    | Access _, _ -> -1
    | _, Access _ -> 1
    | _ -> 0
    ) 
    in *)
    Set.exists aux args
  )
  | Min args -> Set.for_all aux args
  | _ -> (
    match evaluate_const_exp exp with
    | Some const_value -> IntLit.geq const_value IntLit.zero
    | None -> (
      let exp_why3, type_conditions = to_why3_expr exp tenv prover_data in
      let zero_const = Why3.Term.t_real_const (Why3.BigInt.of_int 0) in
      let ge_symbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix >="] in
      let rhs = Why3.Term.t_app_infer ge_symbol [exp_why3; zero_const] in

      let formula = if Why3.Term.Sterm.is_empty type_conditions then rhs
      else (
        let lhs = Why3.Term.Sterm.elements type_conditions |> Why3.Term.t_and_l in
        Why3.Term.t_implies lhs rhs
      )
      in
      
      let free_vars = Why3.Term.Mvs.keys (Why3.Term.t_vars formula) in
      let quantified_fmla = Why3.Term.t_forall_close free_vars [] formula in

      let goal_symbol = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh "is_guard") in
      let task = Why3.Task.use_export None prover_data.theory in
      let task = Why3.Task.add_prop_decl task Why3.Decl.Pgoal goal_symbol quantified_fmla in

      let prover_call = Why3.Driver.prove_task prover_data.driver task
      ~config:prover_data.main
      ~command:prover_data.prover_conf.command
      ~limit:{Why3.Call_provers.empty_limit with limit_time = 5.0} 
      in

      match (Why3.Call_provers.wait_on_call prover_call).pr_answer with
      | Why3.Call_provers.Valid -> true
      | Why3.Call_provers.Invalid | Why3.Call_provers.Unknown _ -> false
      | _ -> assert(false)
    )
  )


let get_accesses_poly exp set ~f ~g =
  let rec aux exp set = match exp with
  | Access access -> f (g access) set
  | BinOp (_, lexp, rexp) -> aux rexp (aux lexp set)
  | UnOp (_, exp, _) -> aux exp set
  | Cast (_, exp) -> aux exp set
  | Call (_, _, args, _) -> (
    List.fold args ~init:set ~f:(fun acc (arg, _) -> aux arg acc)
  )
  | Max args -> Set.fold (fun arg acc -> aux arg acc) args set
  | Min args -> Set.fold (fun arg acc -> aux arg acc) args set
  | _ -> set
  in
  aux exp set


let get_accesses exp = get_accesses_poly exp AccessExpressionSet.empty 
  ~f:AccessExpressionSet.add ~g:(fun x -> x)

let get_access_exp_set exp = get_accesses_poly exp Set.empty ~f:Set.add ~g:(fun x -> Access x)


(* TODO: rewrite/get rid of *)
let map_accesses bound ~f acc =
  let rec aux bound acc =   
    let process_min_max args ~f ~g =
      let args, acc = Set.fold (fun arg (args, acc) ->
        let arg, acc = aux arg acc in
        Set.add arg args, acc
      ) args (Set.empty, acc)
      in

      if Set.for_all is_const args then (
        let args = match Set.cardinal args with
        | 1 -> Set.add zero args
        | _ -> args
        in
        f args, acc
      )
      else g args, acc
    in

    match bound with
    | Access access -> f access acc
    | BinOp (op, lexp, rexp) -> (
      let lexp, acc = aux lexp acc in
      let rexp, acc = aux rexp acc in
      try_eval op lexp rexp, acc
    )
    | UnOp (Unop.Neg, exp, typ) -> (
      let exp, acc = aux exp acc in
      match exp with
      | UnOp (Unop.Neg, _, _) -> exp, acc
      | Const (Const.Cint const) -> Const (Const.Cint (IntLit.neg const)), acc
      | _ ->  UnOp (Unop.Neg, exp, typ), acc
    )
    | UnOp (_, _, _) -> assert(false)
    | Max args -> process_min_max args ~f:Set.max_elt ~g:(fun args -> Max args)
    | Min args -> process_min_max args ~f:Set.min_elt ~g:(fun args -> Min args)
    | _ -> bound, acc
  in
  aux bound acc

let subst bound args formal_map =
  let rec aux bound = 
  let process_min_max args ~f ~g =
    let args_subst = Set.map aux args in
    if Set.for_all is_const args_subst 
    then f args_subst
    else g args_subst
  in

  match bound with
  | Access access -> (
    let base = HilExp.AccessExpression.get_base access in
    if HilExp.AccessExpression.is_base access then (
      match FormalMap.get_formal_index base formal_map with
      | Some idx -> List.nth_exn args idx |> fst
      | None -> (
        debug_log "[EdgeExp.subst] No formal mapping for base '%a'@," 
          HilExp.AccessExpression.pp access;
        bound
      )
    )
    else (
      (* Try to replace expression base with corresponding argument *)
      match FormalMap.get_formal_index base formal_map with
      | Some idx -> (
        let replacement = List.nth_exn args idx |> fst in
        match replacement with
        | Access arg_access -> (
          match HilExp.AccessExpression.append ~onto:arg_access access with
          | Some subst_access -> Access subst_access
          | None -> (
            L.die InternalError "HilExp.AccessExpression.append ~onto:(%a) %a"
              HilExp.AccessExpression.pp arg_access 
              HilExp.AccessExpression.pp access
            (* replacement *)
          )
        )
        | _ -> (
          debug_log "[EdgeExp.subst] Dropping rest of access specifier for '%a'@,"
            HilExp.AccessExpression.pp access;
          replacement
        )
      )
      | None -> (
        debug_log "[EdgeExp.subst] No formal mapping for base '%a'@," 
          HilExp.AccessExpression.pp access;
        bound
      )
    )
  )
  | BinOp (op, lexp, rexp) -> try_eval op (aux lexp) (aux rexp)
  | UnOp (op, exp, typ) -> (
    let subst_subexp = aux exp in
    if is_zero subst_subexp then subst_subexp else UnOp (op, subst_subexp, typ)
  )
  | Max max_args -> process_min_max max_args ~f:Set.max_elt ~g:(fun args -> Max args)
  | Min min_args -> process_min_max min_args ~f:Set.max_elt ~g:(fun args -> Min args)
  | _ -> bound
  in
  aux bound


let normalize_condition exp tenv = 
  let negate_lop (op, lexp, rexp) = match op with
  | Binop.Lt -> Binop.Ge, lexp, rexp
  | Binop.Le -> Binop.Gt, lexp, rexp
  | Binop.Gt -> Binop.Ge, rexp, lexp
  | Binop.Ge -> Binop.Gt, rexp, lexp
  | Binop.Eq -> Binop.Ne, lexp, rexp
  | Binop.Ne -> Binop.Eq, lexp, rexp
  | _ -> op, lexp, rexp
  in

  let rec create_condition exp = match exp with
  | UnOp (Unop.LNot, subexp, _) -> (
    let op, lexp, rexp = create_condition subexp in
    negate_lop (op, lexp, rexp)
  )
  | BinOp (op, lexp, rexp) -> (
    match op with
    | Binop.Lt -> Binop.Gt, rexp, lexp
    | Binop.Le -> Binop.Ge, rexp, lexp
    | Binop.Gt | Binop.Ge | Binop.Eq | Binop.Ne -> op, lexp, rexp
    | _ -> Binop.Ne, exp, zero
  )
  | _ -> Binop.Ne, exp, zero
  in
  let op, lexp, rexp = create_condition exp in
  BinOp (op, lexp, rexp)

  (* let rec aux exp = match exp with
  | Access path -> (
    match HilExp.AccessExpression.get_typ path tenv with
    | Some typ when Typ.is_int typ || Typ.is_pointer typ -> (Binop.Ne, Access path, zero)
    | _ -> assert(false)
  )
  | BinOp (op, lexp, rexp) -> (
    match op with
    | Binop.Lt -> (Binop.Gt, rexp, lexp)
    | Binop.Le -> (Binop.Ge, rexp, lexp)
    | _ -> (op, lexp, rexp)
  )
  | Const _ -> (Binop.Ne, exp, zero)
  | Call (typ, _, _, _) -> (
    assert(Typ.is_int typ);
    (Binop.Ne, exp, zero)
  )
  | UnOp (Unop.LNot, subexp, _) -> negate_lop (aux subexp)
  | _ -> L.(die InternalError)"Unsupported condition expression '%a'" pp exp
  in
  let (op, lexp, rexp) = aux exp in
  BinOp (op, lexp, rexp) *)


let determine_monotonicity exp tenv (prover_data : prover_data) =
  debug_log "@[<v2>[Determining monotonicity] %a@," pp exp;

  (* Basically expands two brackets and multiplies its terms *)
  let multiply_exps lexp_parts rexp_parts = List.fold lexp_parts ~init:[] ~f:(fun acc lexp ->
    List.fold rexp_parts ~init:acc ~f:(fun acc rexp ->
      let multiplied_exp = match lexp, rexp with
      | UnOp (Unop.Neg, lsubexp, _), UnOp (Unop.Neg, rsubexp, _) -> (
        try_eval (Binop.Mult None) lsubexp rsubexp
      )
      | _, UnOp (Unop.Neg, rsubexp, _) -> (
        UnOp (Unop.Neg, try_eval (Binop.Mult None) lexp rsubexp, None)
      )
      | UnOp (Unop.Neg, lsubexp, _), _ -> (
        UnOp (Unop.Neg, try_eval (Binop.Mult None) lsubexp rexp, None)
      )
      | _ -> try_eval (Binop.Mult None) lexp rexp
      in
      multiplied_exp :: acc
    )
  )
  in

  let transformed, conditions = transform_shifts exp in
  debug_log "@[<v2>[Transforming shifts]@,Result: %a@," pp transformed;
  if Set.is_empty conditions |> not then (
    debug_log "Value conditions: ";
    Set.iter (fun condition -> debug_log "%a@ " pp condition) conditions;

  );
  let simplified = simplify transformed in
  debug_log "@]@,[Simplified] %a@," pp simplified;

  let rec partial_derivative exp var is_root = match exp with
  | BinOp (Binop.DivI, lexp, rexp) -> (
    if not is_root then (
      (* not supported yet *)
      assert(false)
    ) 
    else (
      let numerator_parts = split_exp lexp in
      let divisor_parts = split_exp rexp in

      let derivate_div_subexp subexp_parts = List.fold subexp_parts ~f:(fun acc part ->
        match part with
        | UnOp (Unop.Neg, subexp, typ) -> (
          UnOp (Unop.Neg, partial_derivative subexp var false, typ) :: acc
        )
        | _ -> (partial_derivative part var false) :: acc
      ) ~init:[]
      in

      (* TODO: filter out "constant" exp if does not contain var *)

      (* Derivate each part of numerator and divisor and apply quotient rule *)
      let numerator_derivative = derivate_div_subexp numerator_parts in
      let divisor_derivative = derivate_div_subexp divisor_parts in

      (* TODO: use divisor op if it contains only single part, might be negative *)
      let divisor_squared = multiply_exps divisor_parts divisor_parts |> merge_exp_parts in
      let numerator_lhs = multiply_exps numerator_derivative divisor_parts |> merge_exp_parts in
      let numerator_rhs = multiply_exps numerator_parts divisor_derivative |> merge_exp_parts in
      match is_zero numerator_lhs, is_zero numerator_rhs with
      | true, true -> zero
      | true, false -> UnOp (Unop.Neg, BinOp (Binop.DivI, numerator_rhs, divisor_squared), None)
      | false, true -> BinOp (Binop.DivI, numerator_lhs, divisor_squared)
      | false, false -> (
        let numerator = BinOp (Binop.MinusA None, numerator_lhs, numerator_rhs) in
        BinOp (Binop.DivI, numerator, divisor_squared)
      )
    )
  )
  | _ -> (
    let rec get_degree exp root = match exp with
    | Const _ -> 0, Some exp
    | Access access -> if HilExp.AccessExpression.equal access var then 1, None else 0, Some exp
    | UnOp (Unop.Neg, subexp, typ) -> (
      assert(root);
      let degree, remainder_opt = get_degree subexp false in
      match remainder_opt with
      | Some remainder -> degree, Some remainder
      | None -> degree, Some (UnOp (Unop.Neg, one, typ))
    )
    | BinOp (Binop.Mult _, (Access l_access), (Access r_access)) -> (
      match HilExp.AccessExpression.equal l_access var, HilExp.AccessExpression.equal r_access var with
      | true, true -> 2, None
      | true, false -> 1, Some (Access r_access)
      | false, true -> 1, Some (Access l_access)
      | _ -> 0, Some exp
    )
    | BinOp (Binop.Mult typ, Access access, subexp)
    | BinOp (Binop.Mult typ, subexp, Access access) -> (
      let subexp_degree, subexp_opt = get_degree subexp false in

      if HilExp.AccessExpression.equal access var then subexp_degree + 1, subexp_opt
      else (
        match subexp_opt with
        | Some subexp -> subexp_degree, Some (BinOp (Binop.Mult typ, Access access, subexp))
        | None -> subexp_degree, Some (Access access)
      )
    )
    | BinOp (Binop.Mult typ, lexp, rexp) -> (
      let lexp_degree, lexp_opt = get_degree lexp false in
      let rexp_degree, rexp_opt = get_degree rexp false in
      let merged_exp = match lexp_opt, rexp_opt with
      | Some lexp, Some rexp -> Some (BinOp (Binop.Mult typ, lexp, rexp))
      | Some subexp, None 
      | None, Some subexp -> Some subexp
      | _ -> None
      in
      lexp_degree + rexp_degree, merged_exp
    )
    | BinOp (Binop.DivI, Access access, (Const (Const.Cint _) as div_const)) -> (
      if HilExp.AccessExpression.equal access var then (
        let const_one = Const (Const.Cint (IntLit.one)) in
        1, Some (BinOp (Binop.DivI, const_one, div_const))
      )
      else 0, Some exp
    )
    | Cast (_, subexp) -> get_degree subexp root
    | exp -> (
      (* TODO: implement remaining possible cases *)
      L.die InternalError "Partial derivative: case not implemented. Expression: %a" pp exp;
    )
    in

    let rec create_var_power var power = match power with
    | 0 -> one
    | 1 -> var
    | _ -> BinOp (Binop.Mult None, var, create_var_power var (power - 1))
    in

    let degree, remainder_exp_opt = get_degree exp true in
    match degree with
    | 0 -> zero
    | 1 -> Option.value remainder_exp_opt ~default:one
    | _ -> (
      let degree_const = of_int degree in
      let var_power = create_var_power (Access var) (degree - 1) in
      match remainder_exp_opt with
      | Some remainder_exp -> (
        let remainder_exp = simplify (BinOp (Binop.Mult None, degree_const, remainder_exp)) in
        BinOp (Binop.Mult None, var_power, remainder_exp)
      )
      | None -> one
    )
  )
  in

  let rec deduplicate_parts parts = match parts with
  | [] -> []
  | x::xs -> (
    let x_var, x_const = separate x in
    let x, part_count = match x_const with
    | Some (Binop.Mult _, const) -> x_var, const
    | _ -> x, IntLit.one
    in

    (* Find all duplicates of expression 'x' and store
     * just one multiplied by the number of occurences *)
    let filtered_xs, part_count = List.fold xs 
    ~f:(fun (new_list, part_count) xs_part ->
      let var, const_opt = separate xs_part in
      match const_opt with
      | Some (Binop.Mult _, const) -> (
        if equal x var then new_list, IntLit.add part_count const
        else new_list @ [xs_part], part_count
      )
      | _ -> (
        if equal x xs_part then new_list, IntLit.add part_count IntLit.one
        else new_list @ [xs_part], part_count
      )
    ) ~init:([], part_count)
    in
    if IntLit.iszero part_count then deduplicate_parts filtered_xs
    else (
      let part = if IntLit.isone part_count then x else (
        let part_count_exp = Const (Const.Cint part_count) in
        BinOp (Binop.Mult None, part_count_exp, x)
      )
      in
      part :: deduplicate_parts filtered_xs
    )
  )
  in

  let parts = split_exp simplified in
  debug_log "@[[Expression terms]@ ";
  List.iter parts ~f:(fun exp -> debug_log "%a,@ " pp exp);
  debug_log "@]@,";

  let non_const_parts = List.filter parts ~f:(fun part -> not (is_const part)) 
    |> deduplicate_parts
  in
  debug_log "@[[Non-const terms]@ ";
  List.iter non_const_parts ~f:(fun exp -> debug_log "%a,@ " pp exp);
  debug_log "@]@,";


  let why3_solve_task task =
    let prover_call = Why3.Driver.prove_task
    ~config:prover_data.main
    ~command:prover_data.prover_conf.command
    ~limit:{Why3.Call_provers.empty_limit with limit_time = 10.} prover_data.driver task
    in
    Why3.Call_provers.wait_on_call prover_call
  in


  (* Try to check monotonicity property based if no root exists  *)
  let check_monotonicity var_access monotonicity_map =
    (* TODO: needs more robust solution, this is just a "heuristic" *)
    debug_log "Var access: %a@," HilExp.AccessExpression.pp var_access;
    let value_map_one = AccessExpressionMap.singleton var_access 1.0 in
    let value_map_two = AccessExpressionMap.singleton var_access 2.0 in
    let y1, y2 = List.fold non_const_parts ~f:(fun (y1, y2) part ->
      let lhs_value = evaluate part value_map_one 1.0 in
      let rhs_value = evaluate part value_map_two 1.0 in
      y1 +. lhs_value, y2 +. rhs_value
    ) ~init:(0.0, 0.0)
    in

    debug_log "@[[Evaluating non-const parts]@ ";
    List.iter non_const_parts ~f:(fun exp -> debug_log "%a,@ " pp exp);
    debug_log "@]@,";
    debug_log "y1 =  %f, y2 = %f@," y1 y2;


    match Float.compare y2 y1 with
    | 0 -> (
      (* TODO: function can be locally constant, must come up with some
       * better way to determine if it is increasing/decreasing *)
      assert(false)
    )
    | x when x > 0 -> (
      debug_log "Monotonicity: Non-decreasing";
      AccessExpressionMap.add var_access Monotonicity.NonDecreasing monotonicity_map
    )
    | _ -> (
      debug_log "Monotonicity: Non-increasing";
      AccessExpressionMap.add var_access Monotonicity.NonIncreasing monotonicity_map
    )
  in


  let why3_conditions = Set.fold (fun condition acc -> 
    let cond, _ = to_why3_expr condition tenv prover_data in
    (* debug_log "[Why3 Condition] %a\n" Why3.Pretty.print_term cond; *)
    cond :: acc
  ) conditions []
  in

  let zero_const = Why3.Term.t_real_const (Why3.BigInt.of_int 0) in
  let ge_symbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix >="] in
  let le_symbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix <="] in
  let base_task = Why3.Task.use_export None prover_data.theory in
  let nonzero_goal = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh "nonzero_goal") in


  debug_log "@[<v2>[Calculating partial derivatives for non-const terms]@,";
  let non_const_part_exp = merge_exp_parts non_const_parts in
  (* let non_const_part_exp_variables = get_accesses non_const_part_exp in *)
  let derivative_variables = get_accesses non_const_part_exp
  in
  debug_log "Analyzed expression: %a@,%a@," pp non_const_part_exp 
  (pp_list "Derivation variables" HilExp.AccessExpression.pp) 
    (AccessExpressionSet.elements derivative_variables);

  let monotonicities = AccessExpressionSet.fold (fun var_access acc ->
    debug_log "@[<v2>[Derivation variable: %a]@," HilExp.AccessExpression.pp var_access;
    let derivative_parts = List.filter_map non_const_parts ~f:(fun part ->
      let derivative = partial_derivative part var_access true in
      if is_zero derivative then None else Some derivative
    )
    in

    let derivative = merge_exp_parts derivative_parts |> simplify in
    debug_log "Derivative: %a@," pp derivative;

    let monotonicity = if is_const derivative then check_monotonicity var_access acc
    else (
      let why3_derivative, type_constraints = to_why3_expr derivative tenv prover_data in
      let constraints = Why3.Term.t_and_simp_l ((Why3.Term.Sterm.elements type_constraints) @ why3_conditions) in
      let positive_derivative = Why3.Term.t_app_infer ge_symbol [why3_derivative; zero_const] in
      let negative_derivative = Why3.Term.t_app_infer le_symbol [why3_derivative; zero_const] in
      let positive_implication = Why3.Term.t_implies_simp constraints positive_derivative in
      let negative_implication = Why3.Term.t_implies_simp constraints negative_derivative in
      let free_vars = Why3.Term.Mvs.keys (Why3.Term.t_vars positive_implication) in
      let positive_forall = Why3.Term.t_forall_close_simp free_vars [] positive_implication in
      let negative_forall = Why3.Term.t_forall_close_simp free_vars [] negative_implication in
      let goal_formula = Why3.Term.t_or_simp positive_forall negative_forall in

      let task = Why3.Task.add_prop_decl base_task Why3.Decl.Pgoal nonzero_goal goal_formula in
      (* debug_log "@[<v2>[Why3 Info]@,Task formula: %a@,Task: %a@]@," 
        Why3.Pretty.print_term goal_formula
        Why3.Driver.(print_task prover_data.driver) task; *)

      match (why3_solve_task task).pr_answer with
      | Why3.Call_provers.Valid -> (
        debug_log "Derivative does not change sign. Checking monotonicity type@,";
        check_monotonicity var_access acc
      )
      | Why3.Call_provers.Invalid | Why3.Call_provers.Unknown _ -> (
        debug_log "Derivative changes sign. Not monotonic";
        AccessExpressionMap.add var_access Monotonicity.NotMonotonic acc
      )
      | _ -> assert(false)
    )
    in
    debug_log "@]@,";
    monotonicity

  ) derivative_variables AccessExpressionMap.empty
  in
  debug_log "@]@]@,";
  monotonicities


let add e1 e2 = match is_zero e1, is_zero e2 with
  | false, false -> try_eval (Binop.PlusA None) e1 e2
  | true, false -> e2
  | false, true -> e1
  | _ -> zero


let sub e1 e2 = match is_zero e1, is_zero e2 with
  | false, false -> try_eval (Binop.MinusA None) e1 e2
  | true, false -> UnOp (Unop.Neg, e2, None)
  | false, true -> e1
  | _ -> zero


let mult e1 e2 = if is_zero e1 || is_zero e2
  then zero
  else match is_one e1, is_one e2 with
  | true, true -> one
  | true, false -> e2
  | false, true -> e1
  | _ -> try_eval (Binop.Mult None) e1 e2



let rec array_index_of_exp ~include_array_indexes ~f_resolve_id ~add_deref exp typ =
  (* TODO: Should probably create my own AccessExpression as well in the future.
  Use HilExp in array indices for now *)
  if include_array_indexes then
    Some (HilExp.of_sil ~include_array_indexes ~f_resolve_id ~add_deref exp typ)
  else None
  
(* Adapted from AccessPath.of_exp. *)
and access_exprs_of_exp ~include_array_indexes ~f_resolve_id ~test_resolver ~add_deref exp0 typ0 =
  let rec of_exp_ 
    exp 
    typ
    (add_accesses : HilExp.AccessExpression.t -> HilExp.AccessExpression.t) 
    acc : ValuePair.t list =
    match (exp : Exp.t) with
    | Var id -> (
      match test_resolver (Var.of_id id) with
      | Some value_pair -> (
        let process_value value =
          (* TODO: This seems sketchy, we're working with more
           complex expressions instead of just access expressions
           as it was originally *)
          map_accesses value ~f:(fun ae None ->
            let ae = if add_deref then HilExp.AccessExpression.dereference ae else ae in
            Access (add_accesses ae), None
          ) None |> fst
        in

        match value_pair with
        | ValuePair.V value -> ValuePair.V (process_value value) :: acc
        | ValuePair.P (lb, ub) -> ValuePair.P (process_value lb, process_value ub) :: acc
      )
      | None -> (
        let ae = HilExp.AccessExpression.address_of_base (base_of_id id typ) in
        let ae = if add_deref then HilExp.AccessExpression.dereference ae 
        else ae in
        ValuePair.V (Access (add_accesses ae)) :: acc
      )
      (* match f_resolve_id (Var.of_id id) with
      | Some access_expr ->
          let access_expr' =
            if add_deref then HilExp.AccessExpression.dereference access_expr else access_expr
          in
          add_accesses access_expr' :: acc
      | None ->
          let access_expr = HilExp.AccessExpression.address_of_base (base_of_id id typ) in
          let access_expr' =
            if add_deref then HilExp.AccessExpression.dereference access_expr else access_expr
          in
          add_accesses access_expr' :: acc  *)
    )
    | Lvar pvar when Pvar.is_ssa_frontend_tmp pvar -> (
      match test_resolver (Var.of_pvar pvar) with
      | Some value_pair -> (
        let process_value value =
          (* TODO: This seems sketchy, we're working with more
           complex expressions instead of just access expressions
           as it was originally *)
          map_accesses value ~f:(fun ae None ->
            (* do not need to add deref here as it was added implicitly in the binding *)
            (* but need to remove it if add_deref is false *)
            let ae =
            if not add_deref then (
              match ae with 
              | HilExp.Dereference ae -> ae 
              | _ -> assert false
            )
            else ae
            in
            Access (add_accesses ae), None
          ) None |> fst
        in

        match value_pair with
        | ValuePair.V value -> ValuePair.V (process_value value) :: acc
        | ValuePair.P (lb, ub) -> ValuePair.P (process_value lb, process_value ub) :: acc
      )
      | None -> (
        let access_expr = of_pvar pvar typ in
        let access_expr = if add_deref 
        then HilExp.AccessExpression.dereference access_expr 
        else access_expr
        in
        ValuePair.V (Access (add_accesses access_expr)) :: acc
      )

      (* match f_resolve_id (Var.of_pvar pvar) with
      | Some access_expr ->
          (* do not need to add deref here as it was added implicitly in the binding *)
          (* but need to remove it if add_deref is false *)
          let access_expr' =
            if not add_deref then match access_expr with HilExp.Dereference ae -> ae | _ -> assert false
            else access_expr
          in
          add_accesses access_expr' :: acc
      | None ->
          let access_expr = of_pvar pvar typ in
          let access_expr' =
            if add_deref then HilExp.AccessExpression.dereference access_expr else access_expr
          in
          add_accesses access_expr' :: acc *)
    )
    | Lvar pvar -> (
      let ae = of_pvar pvar typ in
      let ae = if add_deref then HilExp.AccessExpression.dereference ae else ae in
      ValuePair.V (Access (add_accesses ae)) :: acc 
    )
    | Lfield (root_exp, fld, root_exp_typ) -> (
      let add_field_access_expr access_expr =
        add_accesses (HilExp.AccessExpression.field_offset access_expr fld)
      in
      of_exp_ root_exp root_exp_typ add_field_access_expr acc
    )
    | Lindex (root_exp, index_exp) ->
        let index =
          let index_typ = (* TODO: bogus *) StdTyp.void in
          array_index_of_exp ~include_array_indexes ~f_resolve_id ~add_deref
            index_exp index_typ
        in
        let add_array_access_expr access_expr =
          add_accesses (HilExp.AccessExpression.array_offset access_expr typ index)
        in
        let array_typ = Typ.mk_array typ in
        of_exp_ root_exp array_typ add_array_access_expr acc
    | Cast (cast_typ, cast_exp) ->
        of_exp_ cast_exp cast_typ Fn.id acc
    | UnOp (_, unop_exp, _) ->
        of_exp_ unop_exp typ Fn.id acc
    | Exn exn_exp ->
        of_exp_ exn_exp typ Fn.id acc
    | BinOp (_, exp1, exp2) ->
        of_exp_ exp1 typ Fn.id acc |> of_exp_ exp2 typ Fn.id
    | Const _ | Closure _ | Sizeof _ ->
        acc
  in
  of_exp_ exp0 typ0 Fn.id []
  
  
and access_expr_of_lhs_exp ~include_array_indexes ~f_resolve_id ~test_resolver ~add_deref lhs_exp typ =

  let process_lfield_lindex_access_list accesses = 
    (* TODO: Sketchy again. Working with more complex expressions instead
     of pure access expressions. How should we integrate this properly? *)
    match accesses with 
    | [ValuePair.V (Access lhs_ae)] -> (
      Option.map (HilExp.AccessExpression.address_of lhs_ae)
        ~f:(fun ae -> ValuePair.V (Access ae))
    )
    | [ValuePair.P (Access lb_ae, Access ub_ae)] -> (
      let lb_ae_opt = HilExp.AccessExpression.address_of lb_ae in
      let ub_ae_opt = HilExp.AccessExpression.address_of ub_ae in
      match lb_ae_opt, ub_ae_opt with
      | Some lb_ae, Some ub_ae -> Some (ValuePair.P (Access lb_ae, Access ub_ae))
      | _ -> L.die InternalError "TODO: Not implemented"
    )
    | [ValuePair.V _] | [ValuePair.P _] -> (
      L.die InternalError "TODO: Not implemented for more complex expressions.
        HilExp.AccessExpression was expected"
    )
    | _ -> None
  in

  match (lhs_exp : Exp.t) with
  | Lfield _ when not add_deref -> (
    let accesses = access_exprs_of_exp ~include_array_indexes 
      ~f_resolve_id ~test_resolver ~add_deref:true lhs_exp typ
    in
    process_lfield_lindex_access_list accesses
  )
  | Lindex _ when not add_deref -> (
    let accesses =
      let typ' = match typ.Typ.desc with
      | Tptr (t, _) -> t
      | _ -> (
        (* T29630813 investigate cases where this is not a pointer *)
        typ
      )
      in
      access_exprs_of_exp ~include_array_indexes ~f_resolve_id
        ~test_resolver ~add_deref:true lhs_exp typ'
    in
    process_lfield_lindex_access_list accesses
  )
  | _ -> (
    let accesses = access_exprs_of_exp ~include_array_indexes ~f_resolve_id
      ~test_resolver ~add_deref lhs_exp typ
    in
    match accesses with 
    | [lhs_ae] -> Some lhs_ae 
    | _ -> None
  )


(* convert an SIL expression into an EdgeExp expression.
  The [f_resolve_id] function should map an SSA temporary variable to the
  access path it represents. evaluating the HIL expression should produce
  the same result as evaluating the SIL expression and replacing the temporary
  variables using [f_resolve_id] *)
and of_sil_exp ~include_array_indexes 
  ~f_resolve_id ~test_resolver ~add_deref exp typ =
  (* let access_of_access_expr ae =
    let base_var = HilExp.AccessExpression.get_base ae |> fst in
    match Var.get_ident base_var with
    | Some ident -> (
      (* TODO: Replace only base, not entire AE. Will be complicated 
        Idents should occur only for previously unsubstituted
        return idents of function calls, try to substitute now *)
      id_resolver ident
    )
    | None -> Access ae
  in *)

  let rec of_sil_ (exp : Exp.t) typ = match exp with
  | Exp.Var id -> (
    match test_resolver (Var.of_id id) with
    | Some value_pair -> (
      let process_value value =
        map_accesses value ~f:(fun ae None ->
          let ae = if add_deref then HilExp.AccessExpression.dereference ae else ae in
          Access ae, None
        ) None |> fst
      in

      match value_pair with
      | ValuePair.V value -> ValuePair.V (process_value value)
      | ValuePair.P (lb, ub) -> ValuePair.P (process_value lb, process_value ub)
    )
    | None -> (
      let access_expr = HilExp.AccessExpression.of_id id typ in
      let access_expr = if add_deref
      then HilExp.AccessExpression.dereference access_expr
      else access_expr in
      ValuePair.V (Access access_expr)
    )

    (* let ae = match f_resolve_id (Var.of_id id) with
    | Some access_expr -> (
      if add_deref then HilExp.AccessExpression.dereference access_expr else access_expr
    )
    | None -> (
      let access_expr = HilExp.AccessExpression.of_id id typ in
      if add_deref then HilExp.AccessExpression.dereference access_expr else access_expr
    )
    in
    access_of_access_expr ae *)
  )
  | Exp.UnOp (Unop.Neg, Exp.Const Const.Cint c, _) ->
    ValuePair.V (Const (Const.Cint (IntLit.neg c)))
  | Exp.UnOp (op, subexp, subexp_typ) -> (
    match of_sil_ subexp typ with
    | ValuePair.V subexp -> ValuePair.V (UnOp (op, subexp, subexp_typ))
    | ValuePair.P (lb, ub) -> ValuePair.P (UnOp (op, lb, subexp_typ), UnOp (op, ub, subexp_typ))
  )
  | Exp.BinOp (op, e0, e1) -> ValuePair.create_binop op (of_sil_ e0 typ) (of_sil_ e1 typ)
  | Exp.Const c -> ValuePair.V (Const c)
  | Exp.Cast (cast_type, Exp.Const (Const.Cint c)) -> (
    (* TODO: do something based on signedness of the int type and value of const *)
    assert(Typ.is_int cast_type || Typ.is_pointer_to_int cast_type);
    ValuePair.V (Const (Const.Cint c))
  )
  | Exp.Cast (cast_type, e) -> (
    match of_sil_ e typ with
    | ValuePair.V value -> ValuePair.V (Cast (cast_type, value))
    | ValuePair.P (lb, ub) -> ValuePair.P (Cast (cast_type, lb), Cast (cast_type, ub))
  )
  | Exp.Sizeof data -> (
    match data.nbytes with
    | Some size -> ValuePair.V (Const (Const.Cint (IntLit.of_int size)))
    | None -> L.die InternalError "TODO: HilExp.Sizeof missing size information"
  )
  | Exp.Lfield (root_exp, fld, root_exp_typ) -> (
    match access_expr_of_lhs_exp ~include_array_indexes ~f_resolve_id ~test_resolver ~add_deref exp typ with
    | Some access_expr -> (
      (* access_of_access_expr access_expr *)
      access_expr
    )
    | None -> (
      (* unsupported field expression: represent with a dummy variable *)
      let dummy_id = Ident.create_normal (Ident.string_to_name (Exp.to_string root_exp)) 0 in
      of_sil_ (Exp.Lfield (Exp.Var dummy_id, fld, root_exp_typ)) typ
    )
  )
  | Exp.Lindex (Const (Cstr s), index_exp) -> (
    (* indexed string literal (e.g., "foo"[1]). represent this by introducing a dummy variable
    for the string literal. if you actually need to see the value of the string literal in the
    analysis, you should probably be using SIL. this is unsound if the code modifies the
    literal, e.g. using `const_cast<char*>` *)
    let dummy_id = Ident.create_normal (Ident.string_to_name s) 0 in
    of_sil_ (Exp.Lindex (Exp.Var dummy_id, index_exp)) typ
  )
  | Exp.Lindex (root_exp, index_exp) -> (
    match access_expr_of_lhs_exp ~include_array_indexes ~f_resolve_id ~test_resolver ~add_deref exp typ with
    | Some access_expr -> (
      (* access_of_access_expr access_expr *)
      access_expr
    )
    | None -> (
      (* unsupported index expression: represent with a dummy variable *)
      let dummy_id = (Ident.create_normal (Ident.string_to_name (Exp.to_string root_exp)) 0) in
      of_sil_ (Exp.Lindex (Var dummy_id, index_exp )) typ 
    )
  )
  | Exp.Lvar _ -> (
    match access_expr_of_lhs_exp ~include_array_indexes ~f_resolve_id ~test_resolver ~add_deref exp typ with
    | Some access_expr -> (
      (* access_of_access_expr access_expr *)
      access_expr
    )
    | None ->
        L.(die InternalError) "Couldn't convert var expression %a to access path" Exp.pp exp
  )
  | Exp.Exn _ ->
    L.(die InternalError)"[EdgeExp.of_sil_exp] Unsupported Exn expression %a!" Exp.pp exp
  | Exp.Closure _ ->
    L.(die InternalError)"[EdgeExp.of_sil_exp] Unsupported Closure expression %a!" Exp.pp exp
  | _ ->
    L.(die InternalError)"[EdgeExp.of_sil_exp] Unsupported Closure expression %a!" Exp.pp exp
  in
  of_sil_ exp typ
  