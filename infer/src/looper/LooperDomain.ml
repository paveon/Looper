(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)


open! IStd
module F = Format
module L = Logging


let debug_fmt = ref [F.std_formatter]

let debug_log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.fprintf (List.hd_exn !debug_fmt) fmt

let console_log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.printf fmt


module PvarMap = struct
  include Caml.Map.Make(Pvar)

  let to_string map =
    F.asprintf "[%s]" (String.concat ~sep:" " (List.map (bindings map) ~f:(fun (pvar, _) -> Pvar.to_string pvar)))

  let pp fmt map = F.fprintf fmt "%s" (to_string map)
end


module StringMap = Caml.Map.Make(struct
  type nonrec t = string
  let compare = compare_string
end)


type prover_data = {
  name: string;
  prover_conf: Why3.Whyconf.config_prover;
  driver: Why3.Driver.driver;
  theory: Why3.Theory.theory;
  mutable idents: Why3.Ident.preid StringMap.t;
  mutable vars: Why3.Term.vsymbol StringMap.t;
}

type prover =
  | Z3
  | CVC4
  | Vampire
  [@@deriving compare]


module ProverMap = Caml.Map.Make(struct
  type nonrec t = prover
  let compare = compare_prover
end)

module AccessSet = Caml.Set.Make(struct
  type nonrec t = AccessPath.t
  let compare = AccessPath.compare
end)

module Z3ExprSet = Caml.Set.Make(struct
  type nonrec t = Z3.Expr.expr
  let compare = Z3.Expr.compare
end)

module AccessPathMap = Caml.Map.Make(struct
  type nonrec t = AccessPath.t
  let compare = AccessPath.compare
end)

module VariableMonotony = struct
   type t =
   | NonDecreasing
   | NonIncreasing
   | NotMonotonic
   [@@deriving compare]
end


let base_of_id id typ = (Var.of_id id, typ)

let access_of_exp ~include_array_indexes exp0 typ0 ~(f_resolve_id : Var.t -> AccessPath.t option) =
  (* [typ] is the type of the last element of the access path (e.g., typeof(g) for x.f.g) *)
  let rec of_exp_ exp typ accesses acc =
    match exp with
    | Exp.Var id -> (
      match f_resolve_id (Var.of_id id) with
      | Some (base, base_accesses) ->
          (base, base_accesses @ accesses) :: acc
      | None ->
          (base_of_id id typ, accesses) :: acc )
    | Exp.Lvar pvar when Pvar.is_ssa_frontend_tmp pvar -> (
      match f_resolve_id (Var.of_pvar pvar) with
      | Some (base, base_accesses) ->
          (base, base_accesses @ accesses) :: acc
      | None ->
          (AccessPath.base_of_pvar pvar typ, accesses) :: acc )
    | Exp.Lvar pvar ->
        (AccessPath.base_of_pvar pvar typ, accesses) :: acc
    | Exp.Lfield (root_exp, fld, root_exp_typ) ->
        let field_access = AccessPath.FieldAccess fld in
        of_exp_ root_exp root_exp_typ (field_access :: accesses) acc
    | Exp.Lindex (root_exp, index_exp) ->
        let index_access_paths =
          if include_array_indexes then of_exp_ index_exp typ [] [] else []
        in
        let array_access = AccessPath.ArrayAccess (typ, index_access_paths) in
        let array_typ = Typ.mk_array typ in
        of_exp_ root_exp array_typ (array_access :: accesses) acc
    | Exp.Cast (cast_typ, cast_exp) ->
        of_exp_ cast_exp cast_typ [] acc
    | Exp.UnOp (_, unop_exp, _) ->
        of_exp_ unop_exp typ [] acc
    | Exp.Exn exn_exp ->
        of_exp_ exn_exp typ [] acc
    | Exp.BinOp (_, exp1, exp2) ->
        of_exp_ exp1 typ [] acc |> of_exp_ exp2 typ []
    | Exp.Const _ | Closure _ | Sizeof _ ->
        (* trying to make access path from an invalid expression *)
        acc
  in
  of_exp_ exp0 typ0 [] []

let access_of_lhs_exp ~include_array_indexes lhs_exp typ ~(f_resolve_id : Var.t -> AccessPath.t option) =
  match access_of_exp ~include_array_indexes lhs_exp typ ~f_resolve_id with
  | [lhs_ap] -> Some lhs_ap
  | _ -> None


module EdgeExp = struct
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
    | Const const -> Exp.to_string (Exp.Const const)
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
      ) else (
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

  let is_zero = function Const const -> Const.iszero_int_float const 
    | UnOp (Unop.Neg, Const const, _) -> Const.iszero_int_float const
    | _ -> false

  let is_one = function Const (Const.Cint const) -> IntLit.isone const | _ -> false

  let is_variable norm formals =
    let rec traverse_exp = function
    | Access ((var, _), _) -> (match Var.get_pvar var with
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
    | UnOp (_, exp, typ) -> (match typ with
      | Some typ -> Typ.is_int typ
      | None -> is_int exp type_map tenv
    )
    | Access path -> (match AccessPath.get_typ path tenv with
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
    | _ -> L.(die InternalError)"[EdgeExp.eval_consts] Unsupported operator %a %s %a" IntLit.pp c1 (Binop.str Pp.text op) IntLit.pp c2


  let try_eval op e1 e2 = match e1, e2 with
    | Const (Const.Cint c1), Const (Const.Cint c2) -> Const (Const.Cint (eval_consts op c1 c2))
    | Const (Const.Cint c), exp when IntLit.iszero c -> (match op with
      | Binop.PlusA _ -> exp
      | Binop.MinusA _ -> UnOp (Unop.Neg, exp, None)
      | Binop.Mult _ | Binop.Div -> zero
      | _ -> BinOp (op, e1, e2)
    )
    | exp, Const (Const.Cint c) when IntLit.iszero c -> (match op with
      | Binop.PlusA _ -> exp | Binop.MinusA _ -> exp
      | Binop.Mult _ -> zero
      | Binop.Div -> assert(false)
      | _ -> BinOp (op, e1, e2)
    )
    | _ -> BinOp (op, e1, e2)


  let rec evaluate exp value_map default_value = match exp with
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
    | Max args -> (
      let values = List.map args ~f:(fun arg -> evaluate arg value_map default_value) in
      Option.value_exn (List.max_elt values ~compare:Float.compare)
    )
    | Min args -> (
      let values = List.map args ~f:(fun arg -> evaluate arg value_map default_value) in
      Option.value_exn (List.min_elt values ~compare:Float.compare)
    )
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
    | _, UnOp (Unop.Neg, rsubexp, _) -> try_eval (Binop.MinusA None) lhs rsubexp
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
      | Binop.PlusA _ -> (match l_const_opt, r_const_opt with
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
      | Binop.MinusA typ_opt -> (match l_const_opt, r_const_opt with
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
      | Binop.Shiftrt -> (match l_const_opt, r_const_opt with
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
      | _ -> (
        merge lexp_derived l_const_opt, merge rexp_derived r_const_opt, None
      )
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
        if equal lexp_derived rexp_derived then match op with
          (* | Binop.MinusA _ -> Some (zero, IntLit.add l_const (IntLit.neg r_const)) *)
          | Binop.MinusA _ -> zero, const_part
          | Binop.PlusA _ 
          | Binop.Shiftrt -> try_eval op lexp_derived rexp_derived, const_part
          | Binop.Mult _ -> (
            (* TODO: need to make sure if this is correct? *)
            try_eval op lexp_derived rexp_derived, const_part
          )
          | _ -> assert(false)
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
          | _ -> (
            debug_log "%a %s %a\n" pp lexp_derived (Binop.str Pp.text op) pp rexp_derived;
            match const_part with
            | Some (const_op, rhs_const) -> (
              debug_log "Const part: %s %a\n" (Binop.str Pp.text const_op) IntLit.pp rhs_const;
              assert(false)
            )
            | None -> assert(false)
          )
        )
      )
    )
    | UnOp (unop, exp, typ) -> (match unop with
      | Unop.Neg -> (
        let derived_exp, const_opt = separate exp in
        (* let derived_exp = if is_zero derived_exp then derived_exp else UnOp (unop, derived_exp, typ) in *)
        match const_opt with
        | Some (binop, const) -> (
          if IntLit.iszero const then UnOp (unop, derived_exp, typ), None
          else (match binop with
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
           argument, i.e., C * max(arg_2,arg_2, ...) != max(C * arg_1, C * arg_2, ...) *)
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
      (* Transform to division *)
      let divisor = IntLit.of_int (Int.pow 2 (IntLit.to_int_exn power_value)) in
      process_div lexp (Const (Const.Cint divisor)) const_opt
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
    debug_log "[Simplify] Before: %a\n" pp exp;
    let expanded_exp = expand_multiplication exp None in
    debug_log "[Simplify] After expansion: %a\n" pp expanded_exp;
    let non_const_part, const_opt = separate expanded_exp in
    let simplified_exp = merge non_const_part const_opt in
    debug_log "[Simplify] After: %a\n" pp simplified_exp;
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


  let rec is_const exp = Option.is_some (evaluate_const_exp exp)


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

        if IntLit.iszero rexp_value then (
          lexp, lexp_conditions
        ) else (
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
    | Var.LogicalVar id -> (match Ident.Map.find id ident_map with
      | Access path -> Some path
      | _ -> assert(false)
    )
    | Var.ProgramVar _ -> assert(false)


  let rec of_exp exp ident_map typ type_map =   
    match exp with
    | Exp.BinOp (op, lexp, rexp) -> (
      let lexp = of_exp lexp ident_map typ type_map in
      let rexp = of_exp rexp ident_map typ type_map in
      match lexp, rexp with
      | Const Const.Cint c1, Const Const.Cint c2 -> Const (Const.Cint (eval_consts op c1 c2))
      | _ -> BinOp (op, lexp, rexp)
    )
    | Exp.UnOp (Unop.Neg, Exp.Const Const.Cint c, _) -> (
      Const (Const.Cint (IntLit.neg c))
    )
    | Exp.UnOp (op, sub_exp, _) -> 
      UnOp (op, of_exp sub_exp ident_map typ type_map, Some typ)
    | Exp.Var ident -> Ident.Map.find ident ident_map
    | Exp.Cast (_, exp) -> of_exp exp ident_map typ type_map
    | Exp.Lvar pvar -> Access (AccessPath.of_pvar pvar (PvarMap.find pvar type_map))
    | Exp.Const const -> Const const
    | Exp.Sizeof {nbytes} -> (match nbytes with
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

  
  let why3_get_vsymbol name prover_data = match StringMap.find_opt name prover_data.vars with
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


  let rec to_why3_expr exp tenv prover_data =
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
      let why3_args, type_constraints = List.fold max_args ~init:([], Why3.Term.Sterm.empty) ~f:(fun (args, constraints) arg ->
        let why3_arg, arg_type_constraints = to_why3_expr arg tenv prover_data in
        why3_arg :: args, Why3.Term.Sterm.union arg_type_constraints constraints
      )
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


  let rec always_positive_why3 exp tenv prover_data =
    let aux = function 
    | Const (Const.Cint x) -> not (IntLit.isnegative x)
    | Const (Const.Cfloat x) -> Float.(x >= 0.0)
    | Access ((_, typ), _) -> (match typ.desc with
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
        let result = Why3.Call_provers.wait_on_call prover_call in
        match result.pr_answer with
        | Why3.Call_provers.Valid -> true
        | Why3.Call_provers.Invalid | Why3.Call_provers.Unknown _ -> false
        | _ -> assert(false)
      )
    )


  let get_accesses exp =
    let rec aux exp set = match exp with
    | Access _ -> Set.add exp set
    | BinOp (_, lexp, rexp) -> aux rexp (aux lexp set)
    | UnOp (_, exp, _) -> aux exp set
    | Max args -> List.fold args ~init:set ~f:(fun acc arg -> aux arg acc)
    | Min args -> List.fold args ~init:set ~f:(fun acc arg -> aux arg acc)
    | _ -> set
    in
    aux exp Set.empty


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
      (* Max args, acc *)
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
      let max_args_subst = List.map max_args ~f:(fun arg -> aux arg) in
      if List.for_all max_args_subst ~f:is_const then (
        Option.value_exn (List.max_elt max_args_subst ~compare:compare)        
      )
      else Max max_args_subst
    )
    | Min min_args -> (
      let min_args_subst = (List.map min_args ~f:(fun arg -> aux arg)) in
      if List.for_all min_args_subst ~f:is_const then (
        Option.value_exn (List.min_elt min_args_subst ~compare:compare)
      )
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
    | Access path -> (match AccessPath.get_typ path tenv with
      | Some typ when Typ.is_int typ || Typ.is_pointer typ -> (Binop.Ne, Access path, zero)
      | _ -> assert(false)
    )
    | BinOp (op, lexp, rexp) -> (match op with
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
    
    
  let determine_monotony_why3 exp tenv (prover_data : prover_data) =
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
    

    debug_log "[Pre-transform] %a\n" pp exp;
    let transformed, conditions = transform_shifts exp in
    let simplified = simplify transformed in
    debug_log "[Simplified]\n%a\n" pp simplified;
    debug_log "[Conditions]\n";
    Set.iter (fun condition -> debug_log "\t%a\n" pp condition) conditions;

    let variables = get_accesses simplified in

    let rec partial_derivative exp var is_root = match exp with
    | BinOp (Binop.Div, lexp, rexp) -> (
      if not is_root then (
        (* not supported yet *)
        assert(false)
      ) else (
        let numerator_parts = split_exp lexp in
        let divisor_parts = split_exp rexp in

        let derivate_div_subexp subexp_parts = List.fold subexp_parts ~init:[] ~f:(fun acc part ->
          match part with
          | UnOp (Unop.Neg, subexp, typ) -> (
            UnOp (Unop.Neg, partial_derivative subexp var false, typ) :: acc
          )
          | _ -> (partial_derivative part var false) :: acc
        )
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
      | Access _ -> if equal exp var then 1, None else 0, Some exp
      | UnOp (Unop.Neg, subexp, typ) -> (
        assert(root);
        let degree, remainder_opt = get_degree subexp false in
        match remainder_opt with
        | Some remainder -> degree, Some remainder
        | None -> degree, Some (UnOp (Unop.Neg, one, typ))
      )
      | BinOp (Binop.Mult _, (Access _ as lexp), (Access _ as rexp)) -> (
        match equal lexp var, equal rexp var with
        | true, true -> 2, None
        | true, false -> 1, Some rexp
        | false, true -> 1, Some lexp
        | _ -> 0, Some exp
      )
      | BinOp (Binop.Mult typ, (Access _ as access_exp), subexp)
      | BinOp (Binop.Mult typ, subexp, (Access _ as access_exp)) -> (
        let subexp_degree, subexp_opt = get_degree subexp false in
        if equal access_exp var then (
          subexp_degree + 1, subexp_opt
        ) else (
          match subexp_opt with
          | Some subexp -> subexp_degree, Some (BinOp (Binop.Mult typ, access_exp, subexp))
          | None -> subexp_degree, Some access_exp
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
        let var_power = create_var_power var (degree - 1) in
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
    debug_log "[Parts]\n";
    List.iter parts ~f:(fun exp -> debug_log "  %a\n" pp exp);

    let non_const_parts = List.filter parts ~f:(fun part -> not (is_const part)) in
    debug_log "[Non-const parts]\n";
    List.iter non_const_parts ~f:(fun exp -> debug_log "  %a\n" pp exp);

    let derivatives = Set.fold (fun var acc ->
      let derivative_parts = List.filter_map non_const_parts ~f:(fun part ->
        let derivative = partial_derivative part var true in
        if is_zero derivative then None else Some derivative
      )
      in
      Map.add var (merge_exp_parts derivative_parts |> simplify) acc
    ) variables Map.empty in

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
      let y1, y2 = List.fold non_const_parts ~init:(0.0, 0.0) ~f:(fun (y1, y2) part ->
        let lhs_value = evaluate part value_map_one 1.0 in
        let rhs_value = evaluate part value_map_two 1.0 in
        y1 +. lhs_value, y2 +. rhs_value
      )
      in
      match Float.compare y2 y1 with
      | 0 -> (
        (* TODO: function can be locally constant, must come up with some
         * better way to determine if it is increasing/decreasing *)
        assert(false)
      )
      | x when x > 0 -> (
        debug_log "  [Variable: %a] Non-decreasing\n" AccessPath.pp var_access;
        AccessPathMap.add var_access VariableMonotony.NonDecreasing monotony_map
      )
      | _ -> (
        debug_log "  [Variable: %a] Non-increasing\n" AccessPath.pp var_access;
        AccessPathMap.add var_access VariableMonotony.NonIncreasing monotony_map
      )
    in

    let why3_conditions = Set.fold (fun condition acc -> 
      let cond, _ = to_why3_expr condition tenv prover_data in
      debug_log "[Why3 Condition] %a\n" Why3.Pretty.print_term cond;      
      cond :: acc
    ) conditions [] in

    debug_log "[Partial derivatives]\n";
    let zero_const = Why3.Term.t_real_const (Why3.BigInt.of_int 0) in
    let ge_symbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix >="] in
    let le_symbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix <="] in
    let base_task = Why3.Task.use_export None prover_data.theory in
    let nonzero_goal = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh "nonzero_goal") in

    Map.fold (fun var derivative acc ->
      debug_log "Derivative of %a ---> %a\n" pp var pp derivative;
      let var_access = match var with
      | Access path -> path
      | _ -> assert(false)
      in

      if is_const derivative then (
        debug_log "  [Variable %a] --> Monotonic\n" pp var;
        check_monotonicity var_access acc
      )
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
        debug_log "@[Task formula:@ %a@]@." Why3.Pretty.print_term goal_formula;

        debug_log "Task: %a\n" Why3.Driver.(print_task prover_data.driver) task;

        let result = why3_solve_task task in

        match result.pr_answer with
        | Why3.Call_provers.Valid -> (
          debug_log "  [Variable: %a] Root does not exist\n" pp var;
          check_monotonicity var_access acc
        )
        | Why3.Call_provers.Invalid | Why3.Call_provers.Unknown _ -> (
          debug_log "  [Variable: %a] Root might exist?\n" pp var;
          AccessPathMap.add var_access VariableMonotony.NotMonotonic acc
        )
        | _ -> assert(false)
      )
    ) derivatives AccessPathMap.empty
  

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
end


(* Difference Constraint of form "x <= y + c"
 * Example: "(len - i) <= (len - i) + 1" *)
module DC = struct
  type norm = EdgeExp.t [@@deriving compare]
  type rhs_const = Binop.t * IntLit.t [@@deriving compare]
  type rhs = norm * Binop.t * IntLit.t [@@deriving compare]

  type t = (norm * rhs) [@@deriving compare]


  let make ?(const_part = Binop.PlusA None, IntLit.zero) lhs_norm rhs_norm = 
    let op, rhs_const = const_part in
    match op with
    | Binop.PlusA _ | Binop.Shiftrt -> lhs_norm, (rhs_norm, op, rhs_const)
    | _ -> assert(false)

  let make_rhs ?(const_part = Binop.PlusA None, IntLit.zero) rhs_norm = 
    let op, rhs_const = const_part in
    match op with
    | Binop.PlusA _ | Binop.Shiftrt -> rhs_norm, op, rhs_const
    | _ -> assert(false)

  let is_constant (lhs_norm, (rhs_norm, op, const)) = match op with
    | Binop.PlusA _ -> EdgeExp.equal lhs_norm rhs_norm && IntLit.iszero const
    | _ -> assert(false)

  let same_norms (lhs_norm, (rhs_norm, _, _)) = EdgeExp.equal lhs_norm rhs_norm

  let is_reset dc = not (same_norms dc)

  let is_decreasing (_, (_, op, const)) = match op with
    | Binop.PlusA _ -> IntLit.isnegative const
    | _ -> false

  let is_increasing (_, (_, op, const)) = match op with
    | Binop.PlusA _ -> not (IntLit.isnegative const) && not (IntLit.iszero const)
    | _ -> false

  let to_string (lhs, (rhs_norm, op, rhs_const)) =
    let rhs_str = if EdgeExp.is_zero rhs_norm then (
      match op with
      | Binop.PlusA _ -> (
        if IntLit.iszero rhs_const then "0"
        else if IntLit.isnegative rhs_const then "-" ^ IntLit.to_string (IntLit.neg rhs_const)
        else IntLit.to_string rhs_const
      )
      | Binop.Shiftrt -> "0"
      | _ -> (
        L.(die InternalError)"TODO: unsupported op: %s %a" (Binop.str Pp.text op) IntLit.pp rhs_const
      )
    ) else (
      match op with
      | Binop.PlusA _ -> (
        if IntLit.iszero rhs_const then EdgeExp.to_string rhs_norm
        else if IntLit.isnegative rhs_const then F.asprintf "%a - %a" EdgeExp.pp rhs_norm IntLit.pp (IntLit.neg rhs_const)
        else F.asprintf "%a + %a" EdgeExp.pp rhs_norm IntLit.pp rhs_const
      )
      | Binop.Shiftrt -> (
        if IntLit.iszero rhs_const then EdgeExp.to_string rhs_norm
        else F.asprintf "%a >> %a" EdgeExp.pp rhs_norm IntLit.pp rhs_const
      )
      | _ -> (
        L.(die InternalError)"TODO: unsupported op: %s %a" (Binop.str Pp.text op) IntLit.pp rhs_const
      )
    )
    in
    F.asprintf "%a' <= %s" EdgeExp.pp lhs rhs_str

    
  let pp fmt dc = 
    F.fprintf fmt "%s" (to_string dc)


  module Map = struct
    type dc = t

    include EdgeExp.Map

    let get_dc key map =
      match find_opt key map with
      | Some (rhs_norm, op, rhs_const) -> Some (key, (rhs_norm, op, rhs_const))
      | None -> None

    let add_dc dc_lhs dc_rhs map =
      let rhs_norm, _, rhs_const = dc_rhs in
      if EdgeExp.equal dc_lhs rhs_norm && IntLit.iszero rhs_const then (
        (* Check if set already contains some constraint with this left hand side *)
        if mem dc_lhs map then (
          (* Do not replace [e <= expr] *)
          map
        ) else (
          add dc_lhs dc_rhs map
        )
      ) else (
        (* Replace constant dc [e <= e] with [e <= expr] *)
        add dc_lhs dc_rhs map
      )

    let to_string map =
      let tmp = fold (fun lhs_norm dc_rhs acc ->
        acc ^ (to_string (lhs_norm, dc_rhs)) ^ " "
      ) map ""
      in
      "[" ^ (String.rstrip tmp) ^ "]"
  end
end

let is_loop_prune : Sil.if_kind -> bool = function
  | Ik_dowhile | Ik_for | Ik_while -> true
  | _ -> false

let pp_element fmt (kind, branch, loc) = 
  let kind = Sil.if_kind_to_string kind in
  F.fprintf fmt "%s[%s](%B)" kind (Location.to_string loc) branch


module DefaultDot = struct
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let default_vertex_attributes _ = []
  let graph_attributes _ = []
end


(* Difference Constraint Program *)
module DCP = struct
  type edge_output_type = | LTS | GuardedDCP | DCP [@@deriving compare]

  module Node = struct
    type t = 
      | Prune of (Sil.if_kind * Location.t * Procdesc.Node.id)
      | Start of (Procname.t * Location.t)
      | Join of (Location.t * Procdesc.Node.id)
      | Exit
    [@@deriving compare]

    let equal = [%compare.equal: t]
    let hash = Hashtbl.hash

    let is_join : t -> bool = function Join _ -> true | _ -> false

    let get_location node = match node with
      | Prune (_, loc, _)
      | Start (_, loc)
      | Join (loc, _) -> loc
      | Exit -> Location.dummy

    let to_string loc = match loc with
      | Prune (kind, loc, node_id) -> 
        F.asprintf "[%s] %s (%a)" (Location.to_string loc) (Sil.if_kind_to_string kind) Procdesc.Node.pp_id node_id
      | Start (proc_name, loc) -> F.asprintf "[%s] Begin: %a" (Location.to_string loc) Procname.pp proc_name
      | Join (loc, node_id) -> F.asprintf "[%s] Join (%a)" (Location.to_string loc) Procdesc.Node.pp_id node_id
      | Exit -> F.sprintf "Exit"

    let pp fmt loc = F.fprintf fmt "%s" (to_string loc)

    module Map = Caml.Map.Make(struct
      type nonrec t = t
      let compare = compare
    end)
  end

  module EdgeData = struct
    type t = {
      backedge: bool;
      conditions: EdgeExp.Set.t;
      assignments: EdgeExp.t AccessPathMap.t;
      modified: AccessSet.t;
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

    let equal = [%compare.equal: t]

    let is_reset edge norm = match DC.Map.get_dc norm edge.constraints with
      | Some dc -> not (DC.same_norms dc)
      | None -> false

    let get_reset edge norm = match DC.Map.get_dc norm edge.constraints with
      | Some ((_, (exp, op, lit)) as dc) when not (DC.same_norms dc) -> Some (EdgeExp.merge exp (Some (op, lit)))
      | _ -> None

    let is_exit_edge edge = edge.exit_edge

    let is_backedge edge = edge.backedge

    let active_guards edge = EdgeExp.Set.fold (fun guard acc ->
      match DC.Map.get_dc guard edge.constraints with
      | Some dc ->
        if DC.is_decreasing dc && DC.same_norms dc then acc
        else EdgeExp.Set.add guard acc
      | _ -> EdgeExp.Set.add guard acc
    ) edge.guards EdgeExp.Set.empty

    let modified edge = AccessPathMap.fold (fun lhs_access rhs_exp acc -> 
      if EdgeExp.equal (EdgeExp.Access lhs_access) rhs_exp then acc
      else AccessSet.add lhs_access acc
    ) edge.assignments AccessSet.empty

    let make assignments branch_info = {
      backedge = false;
      conditions = EdgeExp.Set.empty;
      assignments = assignments;
      modified = AccessSet.empty;
      branch_info = branch_info;

      constraints = DC.Map.empty;
      calls = EdgeExp.Set.empty;
      guards = EdgeExp.Set.empty;
      bound = None;
      bound_norm = None;
      computing_bound = false;
      exit_edge = false;

      edge_type = LTS
    }

    let empty = make AccessPathMap.empty None

    (* Required by Graph module interface *)
    let default = empty

    let branch_type edge = match edge.branch_info with
      | Some (_, branch, _) -> branch
      | _ -> false

    let set_backedge edge = { edge with backedge = true }


    let add_condition edge cond = if EdgeExp.is_zero cond then edge else
      { edge with conditions = EdgeExp.Set.add cond edge.conditions }


    let add_assignment edge lhs rhs = { edge with 
        assignments = AccessPathMap.add lhs rhs edge.assignments;
        modified = AccessSet.add lhs edge.modified;
      }  


    let add_invariants edge locals =
      let with_invariants = AccessSet.fold (fun local acc ->
        if AccessPathMap.mem local acc then acc else
        AccessPathMap.add local (EdgeExp.Access local) acc
      ) locals edge.assignments
      in
      { edge with assignments = with_invariants }


    let get_assignment_rhs edge lhs_access =
      match AccessPathMap.find_opt lhs_access edge.assignments with
      | Some rhs -> rhs
      | None -> EdgeExp.Access lhs_access


    let derive_guards_why3 edge norms tenv prover_data =
      let cond_expressions = EdgeExp.Set.fold (fun cond acc -> 
        match cond with
        | EdgeExp.BinOp (_, EdgeExp.Const _, EdgeExp.Const _) -> acc
        | EdgeExp.BinOp _ -> (
          let cond_why3, type_conditions = EdgeExp.to_why3_expr cond tenv prover_data in
          Why3.Term.Sterm.add cond_why3 (Why3.Term.Sterm.union type_conditions acc)
        )
        | _ -> L.(die InternalError)"[Guards] Condition of form '%a' is not supported" EdgeExp.pp cond
      ) edge.conditions Why3.Term.Sterm.empty 
      in
      if Why3.Term.Sterm.is_empty cond_expressions then ()
      else (
        let lhs = Why3.Term.Sterm.elements cond_expressions |> Why3.Term.t_and_l in
        let zero_const = Why3.Term.t_real_const (Why3.BigInt.of_int 0) in
        let gt_symbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix >"] in
        let goal_symbol = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh "is_guard") in

        let lhs_vars = Why3.Term.Mvs.keys (Why3.Term.t_vars lhs) in

        let guards = EdgeExp.Set.fold (fun norm acc ->         
          let solve_formula rhs =
            let rhs = Why3.Term.t_app_infer gt_symbol [rhs;zero_const] in
            let formula = Why3.Term.t_implies lhs rhs in

            let rhs_vars = Why3.Term.Mvs.keys (Why3.Term.t_vars rhs) in
            let free_vars = lhs_vars @ rhs_vars in

            let quantified_fmla = Why3.Term.t_forall_close free_vars [] formula in

            let task = Why3.Task.use_export None prover_data.theory in
            let task = Why3.Task.add_prop_decl task Why3.Decl.Pgoal goal_symbol quantified_fmla in

            let prover_call = Why3.Driver.prove_task prover_data.driver task 
              ~command:prover_data.prover_conf.command
              ~limit:{Why3.Call_provers.empty_limit with limit_time = 5} 
            in
            let result = Why3.Call_provers.wait_on_call prover_call in
            match result.pr_answer with
            | Why3.Call_provers.Valid -> (
              (* Implication [conditions] => [norm > 0] always holds *)
              EdgeExp.Set.add norm acc
            )
            | Why3.Call_provers.Invalid | Why3.Call_provers.Unknown _ -> acc
            | _ -> (
              debug_log "Failed task: %a\n" Why3.Pretty.print_task task;
              debug_log "Fail: %s\n" result.pr_output;
              assert(false)
            )
          in
          if EdgeExp.is_const norm then acc
          else (
            let rhs_expr = EdgeExp.to_why3_expr norm tenv prover_data |> fst in
            solve_formula rhs_expr
          )
        ) norms EdgeExp.Set.empty
        in
        edge.guards <- guards;
      )


    let derive_constraint edge_data norm used_assignments formals =
      let get_assignment lhs_access = match AccessPathMap.find_opt lhs_access edge_data.assignments with
      | Some rhs -> Some rhs
      | None -> (
        let base_pvar = Option.value_exn (Var.get_pvar (fst (fst lhs_access))) in
        if Pvar.Set.mem base_pvar formals then Some (EdgeExp.Access lhs_access) else None
      )
      in

      let rec derive_rhs norm = match norm with
        | EdgeExp.Access access -> (
          match get_assignment access with 
          | Some rhs -> (
            if not (EdgeExp.equal norm rhs) && AccessSet.mem access used_assignments
            then AccessSet.empty, None
            else AccessSet.singleton access, get_assignment access
          )
          | None -> AccessSet.empty, None
        )
        | EdgeExp.Const (Const.Cint _) -> AccessSet.empty, Some norm
        | EdgeExp.BinOp (op, lexp, rexp) -> (
          let lexp_accesses, lexp_derived_opt = derive_rhs lexp in
          let rexp_accesses, rexp_derived_opt = derive_rhs rexp in

          AccessSet.union lexp_accesses rexp_accesses,
          match lexp_derived_opt, rexp_derived_opt with
          | Some lexp_derived, Some rexp_derived -> (
            Some (EdgeExp.BinOp (op, lexp_derived, rexp_derived))
          )
          | Some _, None
          | None, Some _ -> (
            (* Some expression variable is not defined on this edge *)
            None
          )
          | _ -> (
            (* assert(false) *)
            None
          )
        )
        | EdgeExp.UnOp (Unop.Neg, exp, typ) -> (
          let accesses, exp_derived_opt = derive_rhs exp in
          accesses, match exp_derived_opt with
          | Some exp_derived -> (
            if EdgeExp.is_zero exp_derived 
            then exp_derived_opt 
            else Some (EdgeExp.UnOp (Unop.Neg, exp_derived, typ))
          )
          | None -> None
        )
        | EdgeExp.UnOp (_, _, _) -> assert(false)
        | EdgeExp.Max _ -> assert(false)
        | EdgeExp.Min _ -> assert(false)
        | _ -> AccessSet.empty, Some norm
      in


      let add_derived_dc dc_rhs =
        debug_log "[DC derivation] Adding new DC: %a\n" DC.pp (norm, dc_rhs);
        let updated_dc_map = DC.Map.add_dc norm dc_rhs edge_data.constraints in
        edge_data.constraints <- updated_dc_map;
      in


      let substituted_accesses, derived_rhs_opt = derive_rhs norm in
      match derived_rhs_opt with
      | Some derived_rhs -> (
        if EdgeExp.equal derived_rhs norm then (
          add_derived_dc (DC.make_rhs norm);
          None
        )
        else (
          let rhs_norm, rhs_const_opt = EdgeExp.separate derived_rhs in
          let merged = EdgeExp.merge rhs_norm rhs_const_opt in

          if EdgeExp.equal merged norm then (
            add_derived_dc (DC.make_rhs norm);
            None
          )
          else (
            (* Derived RHS expression is not equal to the original norm *)
            let lhs_norm, lhs_const_opt = EdgeExp.separate norm in
            let rhs_norm, rhs_const_opt = if EdgeExp.is_zero rhs_norm then (
              match rhs_const_opt with
              | Some (rhs_op, rhs_const) -> (match rhs_op with
                | Binop.PlusA _ -> (EdgeExp.Const (Const.Cint rhs_const), None)
                | Binop.MinusA _ -> (EdgeExp.Const (Const.Cint (IntLit.neg rhs_const)), None)
                | _ -> assert(false)
              )
              | None -> (
                (* 0 + None *)
                EdgeExp.zero, None
              )
            )
            else rhs_norm, rhs_const_opt
            in

            if EdgeExp.equal lhs_norm rhs_norm then (
              let dc_rhs = match lhs_const_opt, rhs_const_opt with
              | Some (lhs_op, lhs_const), Some (rhs_op, rhs_const) -> (
                assert(Binop.equal lhs_op rhs_op);
                match lhs_op with
                | Binop.PlusA _ -> (
                  let diff = IntLit.sub rhs_const lhs_const in
                  DC.make_rhs ~const_part:(lhs_op, diff) norm
                )
                | Binop.MinusA typ_opt -> (
                  (* [lhs_norm] (-) lhs_const, [rhs_norm] (-) rhs_const --->  +(-(rhs_const - lhs_const)) *)
                  let diff = IntLit.neg (IntLit.sub rhs_const lhs_const) in
                  DC.make_rhs ~const_part:(Binop.PlusA typ_opt, diff) norm
                )
                | Binop.Shiftrt -> (
                  let diff = IntLit.sub rhs_const lhs_const in
                  DC.make_rhs ~const_part:(lhs_op, diff) norm
                )
                | _ -> assert(false)
              )
              | None, Some (rhs_op, rhs_const) -> (match rhs_op with
                | Binop.PlusA _ -> DC.make_rhs ~const_part:(rhs_op, rhs_const) norm
                | Binop.MinusA typ_opt -> DC.make_rhs ~const_part:(Binop.PlusA typ_opt, IntLit.neg rhs_const) norm
                | _ -> assert(false)
              )
              | _ -> assert(false)
              in

              add_derived_dc dc_rhs;
              None
            ) 
            else (
              let dc_rhs = match rhs_const_opt with
              | Some (rhs_op, rhs_const) -> (
                if EdgeExp.is_variable rhs_norm formals then (
                  match rhs_op with
                  | Binop.PlusA _ -> DC.make_rhs ~const_part:(rhs_op, rhs_const) rhs_norm
                  | Binop.MinusA typ_opt -> DC.make_rhs ~const_part:(Binop.PlusA typ_opt, IntLit.neg rhs_const) rhs_norm
                  | Binop.Shiftrt -> (
                    (* TODO *)
                    DC.make_rhs merged
                  )
                  | _ -> assert(false)
                )
                else DC.make_rhs merged
              )
              | None -> DC.make_rhs rhs_norm
              in

              add_derived_dc dc_rhs;
              Some (rhs_norm, substituted_accesses)
            )
          )
        )
      )
      | None -> None
  end


  include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(EdgeData)
  module NodeSet = Caml.Set.Make(V)
  module EdgeSet = Caml.Set.Make(E)
  module EdgeMap = Caml.Map.Make(E)

  include DefaultDot

  let edge_label : EdgeData.t -> string = fun edge_data ->
    match edge_data.branch_info with
    | Some prune_info -> F.asprintf "%a\n" pp_element prune_info
    | None -> ""

  let vertex_attributes node = [ `Shape `Box; `Label (Node.to_string node) ]
  let vertex_name vertex = string_of_int (Node.hash vertex)

  let edge_attributes : E.t -> 'a list = fun (_, edge_data, _) -> (
    let label = edge_label edge_data in
    let label = if edge_data.backedge then label ^ "[backedge]\n" else label in
    let call_list = List.map (EdgeExp.Set.elements edge_data.calls) ~f:(fun call ->
      match call with
      | EdgeExp.Call (_, _, _, loc) -> F.asprintf "%a : %a" EdgeExp.pp call Location.pp loc
      | _ -> assert(false)
    ) 
    in
    let calls_str = String.concat ~sep:"\n" call_list in

    match edge_data.edge_type with
    | LTS -> (
      let conditions = List.map (EdgeExp.Set.elements edge_data.conditions) ~f:(fun cond -> EdgeExp.to_string cond) in

      let assignments = List.map (AccessPathMap.bindings edge_data.assignments) ~f:(fun (lhs, rhs) ->
        F.asprintf "%a = %s" AccessPath.pp lhs (EdgeExp.to_string rhs)
      ) in

      let label = F.asprintf "%s\n%s\n%s\n%s" label (String.concat ~sep:"\n" conditions) 
        (String.concat ~sep:"\n" assignments) calls_str 
      in
      [`Label label; `Color 4711]
    )
    | GuardedDCP -> (
      let guards = List.map (EdgeExp.Set.elements edge_data.guards) ~f:(fun guard -> F.asprintf "[GUARD] %s > 0" (EdgeExp.to_string guard)) in
      let constraints = List.map (DC.Map.bindings edge_data.constraints) ~f:(fun dc -> (DC.to_string dc)) in
      let label = F.asprintf "%s\n%s\n%s\n%s" label 
      (String.concat ~sep:"\n" guards) 
      (String.concat ~sep:"\n" constraints) calls_str in
      [`Label label; `Color 4711]
    )
    | DCP -> (
      let constraints = List.map (DC.Map.bindings edge_data.constraints) ~f:(fun dc -> (DC.to_string dc)) in
      let label = F.asprintf "%s\n%s\n%s" label (String.concat ~sep:"\n" constraints) calls_str in
      [`Label label; `Color 4711]
    )
  )
end

module DCP_Dot = Graph.Graphviz.Dot(DCP)


(* Variable flow graph *)
module VFG = struct
  module Node = struct
    type t = EdgeExp.t * DCP.Node.t [@@deriving compare]
    let hash x = Hashtbl.hash_param 100 100 x
    let equal = [%compare.equal: t]
  end
  
  module Edge = struct
    type t = unit [@@deriving compare]
    let hash = Hashtbl.hash
    let equal = [%compare.equal : t]
    let default = ()
    end
  include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(Edge)
  module NodeSet = Caml.Set.Make(V)
  module EdgeSet = Caml.Set.Make(E)

  include DefaultDot

  let edge_attributes : E.t -> 'a list = fun _ -> [`Label ""; `Color 4711]
  let vertex_attributes : V.t -> 'a list = fun (norm, dcp_node) -> (
    let label = F.asprintf "%a, %a" EdgeExp.pp norm DCP.Node.pp dcp_node in
    [ `Shape `Box; `Label label ]
  )
  let vertex_name : V.t -> string = fun vertex -> string_of_int (Node.hash vertex)

  module Map = Caml.Map.Make(Node)
end

module VFG_Dot = Graph.Graphviz.Dot(VFG)


(* Reset graph *)
module RG = struct
  module Node = struct
    type t = EdgeExp.t [@@deriving compare]
    let hash x = Hashtbl.hash_param 100 100 x
    let equal = EdgeExp.equal
  end

  module Edge = struct
    type t = {
      dcp_edge : DCP.E.t option;
      const : IntLit.t;
    } [@@deriving compare]

    let hash = Hashtbl.hash
    let equal = [%compare.equal: t]
    let default = {
      dcp_edge = None;
      const = IntLit.zero;
    }

    let dcp_edge edge = match edge.dcp_edge with
    | Some dcp_edge -> dcp_edge
    | None -> assert(false)

    let make dcp_edge const = {
      dcp_edge = Some dcp_edge;
      const = const;
    }
  end
  include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(Edge)

  type graph = t

  let edge_attributes : E.t -> 'a list = fun (_, edge, _) -> (
    let label = match edge.dcp_edge with
    | Some (src, _, dst) -> F.asprintf "%a -- %a\n%a" DCP.Node.pp src DCP.Node.pp dst IntLit.pp edge.const
    | None -> ""
    in
    [`Label label; `Color 4711]
  )
  
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let vertex_attributes : V.t -> 'a list = fun node -> (
    [ `Shape `Box; `Label (EdgeExp.to_string node) ]
  )

  let vertex_name : V.t -> string = fun node -> string_of_int (Node.hash node)
    
  let default_vertex_attributes _ = []
  let graph_attributes _ = []

  module Chain = struct
    type t = {
      data : E.t list;
      mutable norms : (EdgeExp.Set.t * EdgeExp.Set.t) option;
    }
    [@@deriving compare]

    let empty = {
      data = [];
      norms = None;
    }

    let origin chain = E.src (List.hd_exn chain.data)

    let value chain = List.fold chain.data ~init:IntLit.zero 
      ~f:(fun acc (_, (data : Edge.t), _) -> IntLit.add acc data.const)

    let transitions chain = List.fold chain.data ~init:DCP.EdgeSet.empty 
      ~f:(fun acc (_, (edge_data), _) -> DCP.EdgeSet.add (Edge.dcp_edge edge_data) acc)

    let norms chain reset_graph = match chain.norms with
      | Some cache -> cache
      | None -> (
        let _, _, path_end = List.last_exn chain.data in
        let rec find_paths origin visited counter =
          if Node.equal origin path_end then counter + 1 else (
            let next = succ_e reset_graph origin in
            if List.is_empty next then counter else (
              let visited = EdgeExp.Set.add origin visited in
              List.fold next ~init:counter ~f:(fun counter (_, _, dst) ->
                if EdgeExp.Set.mem dst visited then counter else find_paths dst visited counter
              )
            )
          )
        in

        let norms = List.fold chain.data ~f:(fun (norms_1, norms_2) (_, _, (dst : Node.t)) ->
          let path_count = find_paths dst EdgeExp.Set.empty 0 in
          if path_count < 2 then EdgeExp.Set.add dst norms_1, norms_2
          else norms_1, EdgeExp.Set.add dst norms_2
        ) ~init:(EdgeExp.Set.empty, EdgeExp.Set.empty)
        in

        chain.norms <- Some norms;
        norms
      )

    let pp fmt chain = List.iter chain.data ~f:(fun ((src : Node.t), _, _) ->
        F.fprintf fmt "%a --> " EdgeExp.pp src
      );
      let _, _, (dst : Node.t) = List.last_exn chain.data in
      F.fprintf fmt "%a" EdgeExp.pp dst

    module Set = Caml.Set.Make(struct
      type nonrec t = t
      let compare = compare
    end)
  end


  (* Finds all reset chains leading to the norm through reset graph *)
  let get_reset_chains origin reset_graph dcp =
    let open Base.Continue_or_stop in
    let rec traverse_reset_graph node (chain : Chain.t) =
      let preds = pred_e reset_graph node in
      if List.is_empty preds then (
        Chain.Set.singleton chain
      ) else (
        List.fold preds ~init:Chain.Set.empty ~f:(fun chains (src, edge_data, dst) ->
          let current_chain = { chain with data = chain.data @ [(src, edge_data, dst)]} in
          let new_chains = traverse_reset_graph src current_chain in
          Chain.Set.union chains new_chains
        )
      )
    in
    let reset_chains = traverse_reset_graph origin Chain.empty in
    (* Shorten the chain until it's optimal, i.e., maximal while remaining sound *)
    Chain.Set.map (fun chain -> 
      let src, edge_data, dst = List.hd_exn chain.data in
      let path_origin = match edge_data.dcp_edge with
      | Some (_, _, dcp_dst) -> dcp_dst
      | None -> assert(false)
      in
      let optimize_chain optimal_chain (src, (edge_data : Edge.t), dst) =
        match edge_data.dcp_edge with
        | Some (_, _, path_end) -> (
          (* Find all paths from origin to end and check if they reset the end norm *)
          let current_norm = dst in
          let rec checkPaths origin current visited_nodes norm_reset =
            if DCP.Node.equal current path_end && not (DCP.NodeSet.is_empty visited_nodes) then (
              (* Found path, return info if norm was reset along the path *)
              match norm_reset with 
              | Some _ -> norm_reset
              | None -> Some false
            ) else (
              let next = DCP.succ_e dcp current in
              if List.is_empty next then (
                (* Not a path *)
                None
              ) else (
                let visited_nodes = if DCP.Node.equal origin current then (
                  visited_nodes
                ) else (DCP.NodeSet.add current visited_nodes)
                in
                List.fold_until next ~init:norm_reset ~f:(fun norm_reset (dcp_edge : DCP.E.t) ->
                  let dcp_src, dcp_data, dcp_dst = dcp_edge in
                  if DCP.NodeSet.mem dcp_dst visited_nodes || DCP.Node.equal dcp_src dcp_dst then (
                    Continue norm_reset
                  ) else (
                    let norm_reset = match norm_reset with
                    | Some _ -> norm_reset
                    | None -> if DCP.EdgeData.is_reset dcp_data current_norm then Some true else None
                    in
                    match checkPaths origin dcp_dst visited_nodes norm_reset with
                    | Some already_reset -> if already_reset then Continue (Some true) else Stop None
                    | None -> Continue norm_reset
                  )
                ) ~finish:(fun acc -> acc)
              )
            )
          in
          let all_paths_reset = checkPaths path_origin path_origin DCP.NodeSet.empty None in
          match all_paths_reset with
          | Some _ -> Continue ([(src, edge_data, dst)] @ optimal_chain)
          | None -> (
            Stop optimal_chain
          )
        )
        | None -> assert(false)
      in 
      let chain_data = List.fold_until (List.tl_exn chain.data) ~init:[(src, edge_data, dst)] 
      ~f:optimize_chain ~finish:(fun acc -> acc) 
      in
      let chain = { chain with data = chain_data} in
      chain
    ) reset_chains
end

module RG_Dot = Graph.Graphviz.Dot(RG)


module Increments = Caml.Set.Make(struct
  type nonrec t = DCP.E.t * IntLit.t
  [@@deriving compare]
end)

module Decrements = Caml.Set.Make(struct
  type nonrec t = DCP.E.t * IntLit.t
  [@@deriving compare]
end)

module Resets = Caml.Set.Make(struct
  type nonrec t = DCP.E.t * EdgeExp.t * IntLit.t
  [@@deriving compare]
end)

type norm_updates = {
   increments: Increments.t;
   decrements: Decrements.t;
   resets: Resets.t
}

let empty_updates = { 
  increments = Increments.empty;
  decrements = Decrements.empty;
  resets = Resets.empty;
}

type cache = {
  updates: norm_updates EdgeExp.Map.t;
  variable_bounds: EdgeExp.t EdgeExp.Map.t;
  lower_bounds: EdgeExp.t EdgeExp.Map.t;
  reset_chains: RG.Chain.Set.t EdgeExp.Map.t;
  positivity: bool EdgeExp.Map.t;
}

let empty_cache = { 
  updates = EdgeExp.Map.empty; 
  variable_bounds = EdgeExp.Map.empty;
  lower_bounds = EdgeExp.Map.empty;
  reset_chains = EdgeExp.Map.empty;
  positivity = EdgeExp.Map.empty;
}

let output_graph filepath graph output_fun =
  let out_c = Utils.out_channel_create_with_dir filepath in
  output_fun out_c graph;
  Out_channel.close out_c



module Summary = struct
  type call = {
    name: Procname.t;
    loc: Location.t;
    bounds: transition list;
  }

  and transition = {
    src_node: DCP.Node.t;
    dst_node: DCP.Node.t;
    bound: EdgeExp.t;
    monotony_map: VariableMonotony.t AccessPathMap.t;
    calls: call list
  }

  and t = {
    formal_map: FormalMap.t;
    bounds: transition list;
    return_bound: EdgeExp.t option;
  }


  let total_bound transitions =
    let rec calculate_transition_cost transition =
      let cost_of_calls = List.fold transition.calls ~init:EdgeExp.zero ~f:(fun bound_sum (call : call) ->
        List.fold call.bounds ~f:(fun sum (call_transition : transition) ->
          EdgeExp.add sum (calculate_transition_cost call_transition)
        ) ~init:bound_sum
      )
      in
      let total_edge_cost = if EdgeExp.is_zero cost_of_calls then (
        debug_log "[Edge cost] %a ---> %a: %a\n" 
        DCP.Node.pp transition.src_node DCP.Node.pp transition.dst_node 
        EdgeExp.pp transition.bound;
        transition.bound
      ) 
      else if EdgeExp.is_one cost_of_calls then (
        let value = transition.bound in
        debug_log "[Edge cost] %a ---> %a: %a * %a = %a\n" 
        DCP.Node.pp transition.src_node DCP.Node.pp transition.dst_node 
        EdgeExp.pp transition.bound EdgeExp.pp cost_of_calls EdgeExp.pp value;
        value
      )
      else (
        let value = EdgeExp.add transition.bound (EdgeExp.mult transition.bound cost_of_calls) in
        debug_log "[Edge cost] %a ---> %a: %a + %a * %a = %a\n" 
        DCP.Node.pp transition.src_node DCP.Node.pp transition.dst_node
        EdgeExp.pp transition.bound EdgeExp.pp transition.bound EdgeExp.pp cost_of_calls EdgeExp.pp value;
        value
      )
      in

      total_edge_cost
    in

    let costs = List.map transitions ~f:calculate_transition_cost in
    if List.is_empty costs then EdgeExp.zero else List.reduce_exn costs ~f:EdgeExp.add


  let instantiate (summary : t) args ~upper_bound ~lower_bound tenv active_prover cache =
    debug_log "\t[Determine monotonicity of argument expressions]\n";
    let arg_monotonicity_maps = List.map args ~f:(fun (arg_exp, _) -> 
      EdgeExp.determine_monotony_why3 arg_exp tenv active_prover
    )
    in

    let maximize_argument_exp arg_exp arg_monotonicity_map cache =
      (* Bound increases with the increasing value of this parameter.
       * Maximize value of the argument expression *)
      let evaluated_arg, (cache_acc : cache) = EdgeExp.map_accesses arg_exp ~f:(fun arg_access cache_acc ->
        let var_monotony = AccessPathMap.find arg_access arg_monotonicity_map in
        match var_monotony with
        | VariableMonotony.NonDecreasing -> (
          upper_bound (EdgeExp.Access arg_access) cache_acc
        )
        | VariableMonotony.NonIncreasing -> (
          lower_bound (EdgeExp.Access arg_access) cache_acc
        )
        | VariableMonotony.NotMonotonic -> assert(false);
      ) cache
      in
      evaluated_arg, cache_acc
    in


    let minimize_arg_exp arg_exp arg_monotonicity_map cache = 
      (* Bound decreases with the increasing value of this parameter.
       * Minimize value of the argument expression *)
      let evaluated_arg, cache_acc = EdgeExp.map_accesses arg_exp ~f:(fun arg_access cache_acc ->
        let var_monotony = AccessPathMap.find arg_access arg_monotonicity_map in
        match var_monotony with
        | VariableMonotony.NonDecreasing -> (
          lower_bound (EdgeExp.Access arg_access) cache_acc
        )
        | VariableMonotony.NonIncreasing -> (
          upper_bound (EdgeExp.Access arg_access) cache_acc
        )
        | VariableMonotony.NotMonotonic -> assert(false);
      ) cache
      in
      evaluated_arg, cache_acc
    in


    let evaluate_bound_argument formal_access_base formal_monotonicity arg_exp arg_monotonicity_map cache =           
      match formal_monotonicity with
      | VariableMonotony.NonDecreasing -> (
        (* Bound increases with the increasing value of this parameter.
          * Maximize value of the argument expression *)
        debug_log "[%a] Non decreasing, maximize arg value\n" AccessPath.pp_base formal_access_base;
        debug_log "[%a] Argument: %a\n" AccessPath.pp_base formal_access_base EdgeExp.pp arg_exp;
        let evaluated_arg, cache_acc = maximize_argument_exp arg_exp arg_monotonicity_map cache in
        debug_log "[%a] Evaluated argument: %a\n" AccessPath.pp_base formal_access_base EdgeExp.pp evaluated_arg;
        evaluated_arg, cache_acc
      )
      | VariableMonotony.NonIncreasing -> (
        (* Bound decreases with the increasing value of this parameter.
          * Minimize value of the argument expression *)
        debug_log "[%a] Non increasing, minimize arg value\n" AccessPath.pp_base formal_access_base;
        debug_log "[%a] Argument: %a\n" AccessPath.pp_base formal_access_base EdgeExp.pp arg_exp;
        let evaluated_arg, cache_acc = minimize_arg_exp arg_exp arg_monotonicity_map cache in
        debug_log "[%a] Evaluated argument: %a\n" AccessPath.pp_base formal_access_base EdgeExp.pp evaluated_arg;
        evaluated_arg, cache_acc
      )
      | VariableMonotony.NotMonotonic -> (
        debug_log "[%a] Not monotonic\n" AccessPath.pp_base formal_access_base;
        debug_log "[%a] Argument: %a\n" AccessPath.pp_base formal_access_base EdgeExp.pp arg_exp;
        assert(false);
      )
    in


    let instantiate_bound bound monotony_map cache = EdgeExp.map_accesses bound ~f:(fun formal_access cache_acc ->
      let formal_access_base : AccessPath.base = fst formal_access in
      let formal_idx = Option.value_exn (FormalMap.get_formal_index formal_access_base summary.formal_map) in
      let arg_exp = List.nth_exn args formal_idx |> fst in
      let arg_monotonicity_map = List.nth_exn arg_monotonicity_maps formal_idx in
      match AccessPathMap.find_opt formal_access monotony_map with
      | Some formal_monotony -> (
        evaluate_bound_argument formal_access_base formal_monotony arg_exp arg_monotonicity_map cache_acc
      )
      | None -> assert(false);
    ) cache
    in


    let rec instantiate_transition_summary (transition : transition) cache =
      let bound, cache = if EdgeExp.is_const transition.bound then transition.bound, cache
      else instantiate_bound transition.bound transition.monotony_map cache
      in

      let calls, cache = List.fold transition.calls ~f:(fun (calls_acc, cache) (call : call) ->
        let call_transitions, cache = List.fold call.bounds ~init:([], cache)
        ~f:(fun (call_transitions, cache) (call_transition : transition) ->
          let instantiated_call_transition, cache = instantiate_transition_summary call_transition cache in
          instantiated_call_transition :: call_transitions, cache
        )
        in
        { call with bounds = call_transitions } :: calls_acc, cache
      ) ~init:([], cache)
      in
      let transition = { transition with 
        bound;
        calls;
        monotony_map = EdgeExp.determine_monotony_why3 bound tenv active_prover
      } in
      transition, cache
    in

    let transitions, new_cache = List.fold summary.bounds ~f:(fun (transitions, cache) (transition : transition) ->
      let instantiated_transition, cache = instantiate_transition_summary transition cache in
      instantiated_transition :: transitions, cache
    ) ~init:([], cache)
    in
    transitions, new_cache


  let pp fmt (summary : t) = EdgeExp.pp fmt (total_bound summary.bounds)


  module TreeGraph = struct
    module Node = struct
      type t = 
      | CallNode of Procname.t * Location.t
      | TransitionNode of DCP.Node.t * EdgeExp.t * DCP.Node.t
      [@@deriving compare]

      let hash x = Hashtbl.hash_param 100 100 x
      let equal = [%compare.equal: t]
    end
    
    module Edge = struct
      type t = unit [@@deriving compare]
      let hash = Hashtbl.hash
      let equal = [%compare.equal : t]
      let default = ()
      end
    include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(Edge)
    include DefaultDot

    let edge_attributes : E.t -> 'a list = fun _ -> [`Label ""; `Color 4711]
    let vertex_attributes : V.t -> 'a list = fun node -> (
      match node with
      | CallNode (procname, loc) -> (
        let label = F.asprintf "%a: %a" Procname.pp procname Location.pp loc in
        let color : int = 0xFF0000 in
        [ `Shape `Box; `Label label; `Style `Rounded; `Color color ]
      )
      | TransitionNode (src, bound, dst) -> (
        let label = F.asprintf "{%a --> %a}\n%a" DCP.Node.pp src DCP.Node.pp dst EdgeExp.pp bound in
        let color : int = 0x0000FF in
        [ `Shape `Box; `Label label; `Color color; `Height 1.0]
      )
    )
    let vertex_name : V.t -> string = fun vertex -> string_of_int (Node.hash vertex)

    module Map = Caml.Map.Make(Node)
  end


  module TreeGraph_Dot = Graph.Graphviz.Dot(TreeGraph)


  let to_graph (summary : t) procname loc =
    let graph = TreeGraph.create () in

    let rec construct_subtree root transitions =
      List.iter transitions ~f:(fun trans ->
        let transition_node = TreeGraph.Node.TransitionNode (trans.src_node, trans.bound, trans.dst_node) in
        TreeGraph.add_vertex graph transition_node;
        TreeGraph.add_edge graph root transition_node;
        List.iter trans.calls ~f:(fun call ->
          let call_node = TreeGraph.Node.CallNode (call.name, call.loc) in
          TreeGraph.add_vertex graph call_node;
          TreeGraph.add_edge graph transition_node call_node;
          construct_subtree call_node call.bounds
        )
      )
    in

    let root_node = TreeGraph.Node.CallNode (procname, loc) in
    TreeGraph.add_vertex graph root_node;
    construct_subtree root_node summary.bounds;
    graph

end
