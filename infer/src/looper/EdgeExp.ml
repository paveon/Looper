(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
open LooperUtils
module F = Format
module L = Logging


let debug_log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.fprintf (List.hd_exn !debug_fmt) fmt

let console_log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.printf fmt


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


module Set = Caml.Set.Make(struct
  type nonrec t = t
  let compare = compare
end)


module Map = Caml.Map.Make(struct
  type nonrec t = t
  let compare = compare
end)


let rec to_string = function
  | BinOp (op, lhs, rhs) -> (
    F.sprintf "(%s %s %s)" (to_string lhs) (Binop.str Pp.text op) (to_string rhs)
  )
  | UnOp (op, exp, _) -> F.sprintf "%s%s" (Unop.to_string op) (to_string exp)
  | Access path -> F.asprintf "%a" AccessPath.pp path
  | Const const -> F.asprintf "%a" Const.(pp Pp.text) const
  | Call (_, callee, args, _) -> (
    let proc_name = String.drop_suffix (Procname.to_simplified_string callee) 2 in
    let args_string = String.concat ~sep:", " (List.map args ~f:(fun (x, _) -> to_string x)) in
    F.asprintf "%s(%s)" proc_name args_string
  )
  | Max args -> (
    if Int.equal (List.length args) 1 then (
      let arg = List.hd_exn args in
      let str = to_string arg in
      F.sprintf "[%s]" str
    ) 
    else (
      if List.is_empty args then assert(false)
      else F.asprintf "max(%s)" (String.concat ~sep:", " (List.map args ~f:(fun arg -> to_string arg)))
    )
  )
  | Min args -> 
    if Int.equal (List.length args) 1 then to_string (List.hd_exn args)
    else F.asprintf "min(%s)" (String.concat ~sep:", " (List.map args ~f:(fun arg -> to_string arg)))
  | Inf -> "Infinity"


let pp fmt exp = F.fprintf fmt "%s" (to_string exp)

let equal = [%compare.equal: t]

let one = Const (Const.Cint IntLit.one)

let zero = Const (Const.Cint IntLit.zero)

let of_int value = Const (Const.Cint (IntLit.of_int value))

let of_int32 value = Const (Const.Cint (IntLit.of_int32 value))

let of_int64 value = Const (Const.Cint (IntLit.of_int64 value))

let is_zero = function 
  | Const const
  | UnOp (Unop.Neg, Const const, _) -> Const.iszero_int_float const
  | _ -> false


let is_one = function Const (Const.Cint const) -> IntLit.isone const | _ -> false


let is_variable norm formals =
  let rec traverse_exp = function
  | Access ((var, _), _) -> (
    match Var.get_pvar var with
    | Some pvar -> not (Pvar.Set.mem pvar formals)
    | None -> true
  )
  | BinOp (_, lexp, rexp) -> (traverse_exp lexp) || (traverse_exp rexp)
  | UnOp (_, exp, _) -> (traverse_exp exp)
  | Max args | Min args -> List.exists args ~f:traverse_exp
  | _ -> false
  in
  traverse_exp norm


let is_symbolic_const norm formals = not (is_variable norm formals)


let rec is_int exp type_map tenv = match exp with
  | BinOp (_, lexp, rexp) -> is_int lexp type_map tenv && is_int rexp type_map tenv
  | UnOp (_, exp, typ) -> (
    match typ with
    | Some typ -> Typ.is_int typ
    | None -> is_int exp type_map tenv
  )
  | Access path -> (
    match AccessPath.get_typ path tenv with
    | Some typ -> Typ.is_int typ
    | _ -> false
  )
  | Const Const.Cint _ -> true
  | Call (ret_typ, _, _, _) -> Typ.is_int ret_typ
  | _ -> false


let rec is_return exp = match exp with
  | Access ((var, _), _) -> Var.is_return var
  | Max [arg] -> is_return arg
  | _ -> false


let eval_consts op c1 c2 = match op with
  | Binop.PlusA _ -> IntLit.add c1 c2
  | Binop.MinusA _ -> IntLit.sub c1 c2
  | Binop.Mult _ -> IntLit.mul c1 c2
  | Binop.Div -> IntLit.div c1 c2
  | Binop.Ne -> if IntLit.eq c1 c2 then IntLit.zero else IntLit.one
  | Binop.Eq -> if IntLit.eq c1 c2 then IntLit.one else IntLit.zero
  | Binop.Shiftrt -> IntLit.shift_right c1 c2
  | Binop.Shiftlt -> IntLit.shift_left c1 c2
  | _ -> L.(die InternalError)"[EdgeExp.eval_consts] Unsupported operator %a %s %a" 
          IntLit.pp c1 (Binop.str Pp.text op) IntLit.pp c2


let try_eval op e1 e2 = match e1, e2 with
  | Const (Const.Cint c1), Const (Const.Cint c2) -> Const (Const.Cint (eval_consts op c1 c2))
  | Const (Const.Cint c), exp when IntLit.iszero c -> (
    match op with
    | Binop.PlusA _ -> exp
    | Binop.MinusA _ -> UnOp (Unop.Neg, exp, None)
    | Binop.Mult _ | Binop.Div -> zero
    | _ -> BinOp (op, e1, e2)
  )
  | exp, Const (Const.Cint c) when IntLit.iszero c -> (
    match op with
    | Binop.PlusA _ -> exp | Binop.MinusA _ -> exp
    | Binop.Mult _ -> zero
    | Binop.Div -> assert(false)
    | _ -> BinOp (op, e1, e2)
  )
  | _ -> BinOp (op, e1, e2)


let rec evaluate exp value_map default_value = 
  let eval_min_max args f =
    let values = List.map args ~f:(fun arg -> evaluate arg value_map default_value) in
    Option.value_exn (f values ~compare:Float.compare)
  in

  match exp with
  | Access path -> (
    match AccessPathMap.find_opt path value_map with
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
    | Binop.Div -> l_value /. r_value
    | _ -> assert(false)
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
        | _ -> try_eval op exp (Const (Const.Cint const))
      )
      else try_eval op exp (Const (Const.Cint const))
    )
  )
  | None -> exp


let split_exp exp = 
  let rec aux exp last_op acc = match exp with
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
  (* debug_log "Separate: %a\n" pp exp; *)
  match exp with
  | Access _ -> exp, None
  | Const (Const.Cint c) -> zero, Some (Binop.PlusA None, c)
  | BinOp (op, lexp, rexp) -> (
    let lexp_derived, l_const_opt = separate lexp in
    let rexp_derived, r_const_opt = separate rexp in
    let lexp_derived, rexp_derived, const_part = match op with
    | Binop.PlusA _ -> (
      match l_const_opt, r_const_opt with
      | Some (l_op, l_const), Some (r_op, r_const) -> (
        match l_op, r_op with
        | Binop.PlusA _, Binop.PlusA _ -> lexp_derived, rexp_derived, Some (Binop.PlusA None, IntLit.add l_const r_const)
        | Binop.MinusA _, Binop.PlusA _ -> lexp_derived, rexp_derived, Some (Binop.PlusA None, IntLit.sub r_const l_const)
        | Binop.MinusA typ, Binop.MinusA _ -> lexp_derived, rexp_derived, Some (Binop.MinusA typ, IntLit.add r_const l_const)
        | Binop.Shiftrt, Binop.PlusA _ -> merge lexp_derived l_const_opt, rexp_derived, Some (Binop.PlusA None, r_const)
        | _ -> (
          (* debug_log "lop: %s, rop: %s\n" (Binop.str Pp.text l_op) (Binop.str Pp.text r_op); *)
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
        | Binop.PlusA _, Binop.PlusA _ -> lexp_derived, rexp_derived, Some (Binop.PlusA None, IntLit.sub l_const r_const)
        | Binop.MinusA _, Binop.PlusA _ -> lexp_derived, rexp_derived, Some (Binop.MinusA typ_opt, IntLit.add l_const r_const)
        | _ -> assert(false)
      )
      | Some (l_op, l_const), None -> (
        match l_op with
        | Binop.PlusA _ | Binop.MinusA _ -> lexp_derived, rexp_derived, Some (l_op, l_const)
        | _ -> assert(false)
      )
      | None, Some (r_op, r_const) -> (
        match r_op with
        | Binop.PlusA typ_opt -> lexp_derived, rexp_derived, Some (Binop.MinusA typ_opt, r_const)
        | Binop.MinusA typ_opt -> lexp_derived, rexp_derived, Some (Binop.PlusA typ_opt, r_const)
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
        | Binop.Div
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
          | Binop.PlusA typ_opt -> UnOp (unop, derived_exp, typ), Some (Binop.MinusA typ_opt, const)
          | Binop.MinusA typ_opt -> UnOp (unop, derived_exp, typ), Some (Binop.PlusA typ_opt, const)
          | _ -> assert(false)
        )
      )
      | None -> UnOp (unop, derived_exp, typ), None
    )
    | _ -> assert(false)
  )
  | Max _ -> exp, None
  | Min _ -> assert(false)
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
      BinOp (Binop.Div, lexp, rexp)
    )
  )
  | None -> (
    let lexp = expand_multiplication lexp None in
    let rexp = expand_multiplication rexp None in
    BinOp (Binop.Div, lexp, rexp)
  )
  in

  match exp with
  | Const (Const.Cint c) -> (
    match const_opt with
    | Some const -> Const (Const.Cint (IntLit.mul c const))
    | None -> exp
  )
  | Max [arg] -> Max [expand_multiplication arg const_opt]
  | Max _ -> (
    (* TODO: probably leave as is, in general we cannot simply multiply each
     * argument, i.e., C * max(arg_2,arg_2, ...) != max(C * arg_1, C * arg_2, ...) *)
    assert(false)
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
        | Const (Const.Cint _), _ 
        | _, Const (Const.Cint _) -> (
          expand_multiplication (try_eval op x_part y_part) const_opt
        )
        | BinOp (Binop.Div, lexp_numer, lexp_denom), BinOp (Binop.Div, rexp_numer, rexp_denom) -> (
          let numerator = multiply_sub_exps lexp_numer rexp_numer in
          let denominator = multiply_sub_exps lexp_denom rexp_denom in
          let numerator_parts = split_exp numerator in
          let parts = List.map numerator_parts ~f:(fun part -> 
            match part with
            | UnOp (Unop.Neg, subexp, typ) -> UnOp (Unop.Neg, BinOp (Binop.Div, subexp, denominator), typ)
            | _ -> BinOp (Binop.Div, part, denominator)
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
  | BinOp (Binop.Div, lexp, rexp) -> process_div lexp rexp const_opt
  | BinOp (Binop.Shiftrt, lexp, Const (Const.Cint power_value)) -> (
    let lexp = expand_multiplication lexp const_opt in
    BinOp (Binop.Shiftrt, lexp, Const (Const.Cint power_value))
    (* Transform to division *)
    (* let divisor = IntLit.of_int (Int.pow 2 (IntLit.to_int_exn power_value)) in
    process_div lexp (Const (Const.Cint divisor)) const_opt *)
  )
  | BinOp (Binop.Shiftrt, lexp, rexp) -> (
    match const_opt with
    | Some const -> (
      (* C * (x >> y)  --->  (C * x) >> y
       * this is probably incorrect in edge cases due to
       * the order of operations which should matter? *)
      let lexp = try_eval (Binop.Mult None) (Const (Const.Cint const)) lexp in
      BinOp (Binop.Shiftrt, lexp, rexp)
    )
    | None -> exp
  )
  | _ -> (
    match const_opt with
    | Some const -> try_eval (Binop.Mult None) (Const (Const.Cint const)) exp
    | None -> exp
  )


let simplify exp = 
  (* debug_log "@[<v2>[Simplify] %a@," pp exp; *)
  let expanded_exp = expand_multiplication exp None in
  (* debug_log "Expanded: %a@," pp expanded_exp; *)
  let non_const_part, const_opt = separate expanded_exp in
  let simplified_exp = merge non_const_part const_opt in
  (* debug_log "Simplified: %a@]@," pp simplified_exp; *)
  simplified_exp


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
  | Max args -> get_min_max IntLit.max args
  | Min args -> get_min_max IntLit.max args
  | _ -> None


let is_const exp = Option.is_some (evaluate_const_exp exp)


let rec transform_shifts exp = match exp with
  | Max [arg] -> (
    let arg, conditions = transform_shifts arg in
    arg, Set.add (BinOp (Binop.Ge, arg, zero)) conditions
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
        BinOp (Binop.Div, lexp, Const (Const.Cint divisor)), lexp_conditions
      )
    )
    | None -> (
      let rexp, rexp_conditions = transform_shifts rexp in
      let conditions = Set.union lexp_conditions rexp_conditions in
      BinOp (Binop.Div, lexp, rexp), Set.add (BinOp (Binop.Ge, rexp, zero)) conditions
    )
  )
  | BinOp (op, lexp, rexp) -> (
    let lexp, lexp_conditions = transform_shifts lexp in
    let rexp, rexp_conditions = transform_shifts rexp in
    BinOp (op, lexp, rexp), Set.union lexp_conditions rexp_conditions
  )
  | _ -> exp, Set.empty


let access_path_id_resolver ident_map var = match var with
  | Var.LogicalVar id -> (
    match Ident.Map.find id ident_map with
    | Access path -> Some path
    | _ -> assert(false)
  )
  | Var.ProgramVar _ -> assert(false)


let rec of_exp exp ident_map typ type_map =
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
  | Exp.Var ident -> Ident.Map.find ident ident_map
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
    Access (AccessPath.of_pvar pvar pvar_typ)
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
  aux exp


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

  match exp with
  | Const (Const.Cint const) -> mk_const_term (IntLit.to_int_exn const), Why3.Term.Sterm.empty
  | Const (Const.Cfloat const) -> mk_const_term (int_of_float const), Why3.Term.Sterm.empty
  | Call (typ, procname, _, _) -> (
    (* Treat function without summary as constant *)
    why3_make_access_term (Procname.to_string procname) typ
  )
  | Access access -> (
    match AccessPath.get_typ access tenv with
    | Some typ -> why3_make_access_term (F.asprintf "%a" AccessPath.pp access) typ
    | _ -> assert(false)
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
    | Binop.Div -> (
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
    | _ -> L.(die InternalError)"[EdgeExp.to_why3_expr] Expression '%a' contains invalid binary operator!" pp exp
    in
    expr_z3, Why3.Term.Sterm.union constraints (Why3.Term.Sterm.union why3_lexp_constraints why3_rexp_constraints)
  )
  | UnOp (Unop.Neg, subexp, _) -> (
    let subexp, conditions = to_why3_expr subexp tenv prover_data in
    Why3.Term.t_app_infer unary_minus_symbol [subexp], conditions
  )
  | Max max_args -> (
    let why3_args, type_constraints = List.fold max_args ~f:(fun (args, constraints) arg ->
      let why3_arg, arg_type_constraints = to_why3_expr arg tenv prover_data in
      why3_arg :: args, Why3.Term.Sterm.union arg_type_constraints constraints
    ) ~init:([], Why3.Term.Sterm.empty)
    in
    
    if List.length max_args < 2 then (
      assert(List.length max_args > 0);
      let arg = List.hd_exn why3_args in
      let ite_condition = Why3.Term.ps_app ge_symbol [arg; zero_const] in

      (* TODO: should we include conditions "x >= 0" for each "max(x, 0)" expression? *)
      arg, Why3.Term.Sterm.add ite_condition type_constraints
    ) else (
      (* TODO: Could we potentially extract single max(...) argument based on
       * currently examined bound parameter when checking monotony? (with some 
       * exceptions of course) This could help use get rid of max expressions in
       * Z3 altogether for those usecases.
       * This seems to be necessary if we want to avoid Z3 loops and unknown results *)
      let max_expr = List.reduce_exn why3_args ~f:(fun x y ->
        Why3.Term.t_if (Why3.Term.ps_app ge_symbol [x; y]) x y
      )
      in
      max_expr, type_constraints
    )
  )
  | _ -> L.(die InternalError)"[EdgeExp.to_why3_expr] Expression '%a' contains invalid element!" pp exp


(* TODO: rewrite to be more general, include preconditions and reference value as parameters *)
let rec always_positive_why3 exp tenv (prover_data : prover_data) =
  let aux = function 
  | Const (Const.Cint x) -> not (IntLit.isnegative x)
  | Const (Const.Cfloat x) -> Float.(x >= 0.0)
  | Access ((_, typ), _) -> (
    match typ.desc with
    | Typ.Tint ikind -> Typ.ikind_is_unsigned ikind
    | _ -> false
  )
  | x -> always_positive_why3 x tenv prover_data
  in

  match exp with
  | Max args -> (
    let sorted_args = List.sort args ~compare:(fun x y -> match x, y with
    | Const _, Const _ | Access _, Access _ -> 0
    | Const _, _ -> -1
    | _, Const _ -> 1
    | Access _, _ -> -1
    | _, Access _ -> 1
    | _ -> 0
    ) 
    in
    List.exists sorted_args ~f:aux
  )
  | Min args -> List.for_all args ~f:aux
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
      ~command:prover_data.prover_conf.command
      ~limit:{Why3.Call_provers.empty_limit with limit_time = 5} 
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
  | Max args -> List.fold args ~init:set ~f:(fun acc arg -> aux arg acc)
  | Min args -> List.fold args ~init:set ~f:(fun acc arg -> aux arg acc)
  | _ -> set
  in
  aux exp set


let get_accesses exp = get_accesses_poly exp AccessSet.empty ~f:AccessSet.add ~g:(fun x -> x)

let get_access_exp_set exp = get_accesses_poly exp Set.empty ~f:Set.add ~g:(fun x -> Access x)


(* TODO: rewrite/get rid of *)
let map_accesses bound ~f:f acc =
  let rec aux bound acc = match bound with
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
  | Max args -> (
    let args, acc = List.fold args ~init:([], acc) ~f:(fun (args, acc) arg ->
      let arg, acc = aux arg acc in
      args @ [arg], acc
    )
    in

    if List.for_all args ~f:is_const then (
      let args = match args with
      | [_] -> zero :: args
      | _ -> args
      in
      Option.value_exn (List.max_elt args ~compare), acc
    )
    else Max args, acc
  )
  | Min args -> (
    let args, acc = List.fold args ~init:([], acc) ~f:(fun (args, acc) arg ->
      let arg, acc = aux arg acc in
      args @ [arg], acc
    )
    in

    if List.for_all args ~f:is_const then (
      let args = match args with
      | [_] -> zero :: args
      | _ -> args
      in
      Option.value_exn (List.min_elt args ~compare), acc
    )
    else Min args, acc
  )
  | _ -> bound, acc
  in
  aux bound acc


let subst bound args formal_map =
  let rec aux bound = match bound with
  | Access (base, _) -> (
    match FormalMap.get_formal_index base formal_map with
    | Some idx -> List.nth_exn args idx |> fst
    | None -> bound
  )
  | BinOp (op, lexp, rexp) -> try_eval op (aux lexp) (aux rexp)
  | UnOp (op, exp, typ) -> (
    let subst_subexp = aux exp in
    if is_zero subst_subexp then subst_subexp else UnOp (op, subst_subexp, typ)
  )
  | Max max_args -> (
    let max_args_subst = List.map max_args ~f:aux in
    if List.for_all max_args_subst ~f:is_const 
    then Option.value_exn (List.max_elt max_args_subst ~compare:compare)
    else Max max_args_subst
  )
  | Min min_args -> (
    let min_args_subst = List.map min_args ~f:aux in
    if List.for_all min_args_subst ~f:is_const 
    then Option.value_exn (List.min_elt min_args_subst ~compare:compare)
    else Min min_args_subst
  )
  | _ -> bound
  in
  aux bound


let normalize_condition exp tenv = 
  let negate_lop (op, lexp, rexp) = match op with
  | Binop.Lt -> (Binop.Ge, lexp, rexp)
  | Binop.Le -> (Binop.Gt, lexp, rexp)
  | Binop.Gt -> (Binop.Ge, rexp, lexp)
  | Binop.Ge -> (Binop.Gt, rexp, lexp)
  | Binop.Eq -> (Binop.Ne, lexp, rexp)
  | Binop.Ne -> (Binop.Eq, lexp, rexp)
  | _ -> (op, lexp, rexp)
  in

  let rec aux exp = match exp with
  | Access path -> (
    match AccessPath.get_typ path tenv with
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
  BinOp (op, lexp, rexp)


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
  | BinOp (Binop.Div, lexp, rexp) -> (
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
      | true, false -> UnOp (Unop.Neg, BinOp (Binop.Div, numerator_rhs, divisor_squared), None)
      | false, true -> BinOp (Binop.Div, numerator_lhs, divisor_squared)
      | false, false -> (
        let numerator = BinOp (Binop.MinusA None, numerator_lhs, numerator_rhs) in
        BinOp (Binop.Div, numerator, divisor_squared)
      )
    )
  )
  | _ -> (
    let rec get_degree exp root = match exp with
    | Const _ -> 0, Some exp
    | Access access -> if AccessPath.equal access var then 1, None else 0, Some exp
    | UnOp (Unop.Neg, subexp, typ) -> (
      assert(root);
      let degree, remainder_opt = get_degree subexp false in
      match remainder_opt with
      | Some remainder -> degree, Some remainder
      | None -> degree, Some (UnOp (Unop.Neg, one, typ))
    )
    | BinOp (Binop.Mult _, (Access l_access), (Access r_access)) -> (
      match AccessPath.equal l_access var, AccessPath.equal r_access var with
      | true, true -> 2, None
      | true, false -> 1, Some (Access r_access)
      | false, true -> 1, Some (Access l_access)
      | _ -> 0, Some exp
    )
    | BinOp (Binop.Mult typ, (Access access), subexp)
    | BinOp (Binop.Mult typ, subexp, (Access access)) -> (
      let subexp_degree, subexp_opt = get_degree subexp false in

      if AccessPath.equal access var then subexp_degree + 1, subexp_opt
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
    | _ -> (
      (* TODO: implement remaining possible cases *)
      assert(false)
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

  let parts = split_exp simplified in
  debug_log "@[[Expression terms]@ ";
  List.iter parts ~f:(fun exp -> debug_log "%a,@ " pp exp);
  debug_log "@]@,";

  let non_const_parts = List.filter parts ~f:(fun part -> not (is_const part)) in
  debug_log "@[[Non-const terms]@ ";
  List.iter non_const_parts ~f:(fun exp -> debug_log "%a,@ " pp exp);
  debug_log "@]@,";


  let why3_solve_task task =
    let prover_call = Why3.Driver.prove_task ~command:prover_data.prover_conf.command
    ~limit:{Why3.Call_provers.empty_limit with limit_time = 10} prover_data.driver task
    in
    Why3.Call_provers.wait_on_call prover_call
  in


  (* Try to check monotonicity property based if no root exists  *)
  let check_monotonicity var_access monotony_map =
    (* TODO: needs more robust solution, this is just a "heuristic" *)
    let value_map_one = AccessPathMap.singleton var_access 1.0 in
    let value_map_two = AccessPathMap.singleton var_access 2.0 in
    let y1, y2 = List.fold non_const_parts ~f:(fun (y1, y2) part ->
      let lhs_value = evaluate part value_map_one 1.0 in
      let rhs_value = evaluate part value_map_two 1.0 in
      y1 +. lhs_value, y2 +. rhs_value
    ) ~init:(0.0, 0.0)
    in

    match Float.compare y2 y1 with
    | 0 -> (
      (* TODO: function can be locally constant, must come up with some
       * better way to determine if it is increasing/decreasing *)
      assert(false)
    )
    | x when x > 0 -> (
      debug_log "Monotonicity: Non-decreasing";
      AccessPathMap.add var_access Monotonicity.NonDecreasing monotony_map
    )
    | _ -> (
      debug_log "Monotonicity: Non-increasing";
      AccessPathMap.add var_access Monotonicity.NonIncreasing monotony_map
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
  let derivative_variables = get_accesses simplified in
  let monotonicities = AccessSet.fold (fun var_access acc ->
    debug_log "@[<v2>[Derivation variable: %a]@," AccessPath.pp var_access;
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
        AccessPathMap.add var_access Monotonicity.NotMonotonic acc
      )
      | _ -> assert(false)
    )
    in
    debug_log "@]@,";
    monotonicity

  ) derivative_variables AccessPathMap.empty
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