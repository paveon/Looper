open! IStd
module F = Format
module L = Logging

let log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.printf fmt


module PvarMap = struct
  include Caml.Map.Make(Pvar)

  let to_string map =
    F.asprintf "[%s]" (String.concat ~sep:" " (List.map (bindings map) ~f:(fun (pvar, _) -> Pvar.to_string pvar)))

  let pp fmt map = F.fprintf fmt "%s" (to_string map)
end

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
    (* | Var pvar -> Pvar.to_string pvar *)
    | Const const -> Exp.to_string (Exp.Const const)
    | Call (_, callee, args, _) -> (
      let proc_name = String.drop_suffix (Procname.to_simplified_string callee) 2 in

      let args_string = String.concat ~sep:", " (List.map args ~f:(fun (x, _) -> to_string x)) in
      F.asprintf "%s(%s)" proc_name args_string
      (* let complexity_bound_str = F.asprintf "[Complexity bound] %s" (to_string summary.bound) in
      match summary.return_bound with
      | Some bound -> str ^ F.asprintf "\n  [Return bound] %s" (to_string bound)
      | None -> str *)
    )
    | Max args -> if Int.equal (List.length args) 1 then (
      let arg = List.hd_exn args in
      let str = to_string arg in
      match arg with 
      | Access _ -> F.sprintf "[%s]" str
      | _ -> F.sprintf "max(%s, 0)" str
    ) else (
      if List.is_empty args then assert(false)
      else F.asprintf "max(%s)" (String.concat ~sep:", " (List.map args ~f:(fun arg -> to_string arg)))
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

  let is_zero = function Const const -> Const.iszero_int_float const | _ -> false

  let is_one = function Const (Const.Cint const) -> IntLit.isone const | _ -> false

  let rec is_const exp = match exp with
    | Const _ -> true
    | BinOp (_, lexp, rexp) -> is_const lexp && is_const rexp
    | UnOp (_, exp, _) -> is_const exp
    | Max args | Min args -> List.for_all args ~f:is_const
    | _ -> false

  let is_variable norm formals =
    let rec traverse_exp = function
    | Access ((var, _), _) -> (match Var.get_pvar var with
      | Some pvar -> not (Pvar.Set.mem pvar formals)
      | None -> true
    )
    | BinOp (_, lexp, rexp) -> (traverse_exp lexp) || (traverse_exp rexp)
    | UnOp (_, exp, _) -> (traverse_exp exp)
    | _ -> false
    in
    traverse_exp norm

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

  let is_formal exp formals = match exp with
    | Access ((var, _), _) -> (match Var.get_pvar var with
      | Some pvar -> Pvar.Set.mem pvar formals
      | None -> false
    )
    | _ -> false

  let is_return exp = match exp with
  | Access ((var, _), _) -> Pvar.is_return (Option.value_exn (Var.get_pvar var))
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

  let eval op c1 c2 = Const (Const.Cint (eval_consts op c1 c2))
    (* | _ -> BinOp (op, Const (Const.Cint c1), Const (Const.Cint c2)) *)


  let try_eval op e1 e2 = match e1, e2 with
    | Const (Const.Cint c1), Const (Const.Cint c2) -> eval op c1 c2
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


  let merge exp const_opt = match const_opt with
    | Some (op, const) -> (
      if IntLit.isnegative const then (
        let const_neg = (Const (Const.Cint (IntLit.neg const))) in
        match op with
        | Binop.MinusA kind -> try_eval (Binop.PlusA kind) exp const_neg
        | Binop.PlusA kind -> try_eval (Binop.MinusA kind) exp const_neg
        | _ -> try_eval op exp (Const (Const.Cint const))
      )
      else try_eval op exp (Const (Const.Cint const))
    )
    | None -> exp


  let rec separate exp = 
    log "Separate: %a\n" pp exp;
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
          | _ -> assert(false)
        )
        | Some (l_op, l_const), None -> (
          match l_op with
          | Binop.PlusA _ | Binop.MinusA _ -> lexp_derived, rexp_derived, Some (l_op, l_const)
          | _ -> assert(false)
        )
        | None, Some (r_op, r_const) -> (
          match r_op with
          | Binop.PlusA _ | Binop.MinusA _ -> lexp_derived, rexp_derived, Some (r_op, r_const)
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
        | Some (l_op, l_const), None -> assert(false)
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
            log "%a %s %a\n" pp lexp_derived (Binop.str Pp.text op) pp rexp_derived;
            match const_part with
            | Some (const_op, rhs_const) -> (
              log "Const part: %s %a\n" (Binop.str Pp.text const_op) IntLit.pp rhs_const;
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


  let simplify exp = 
    (* log "[Simplify] Before: %a\n" pp exp; *)
    let exp, const_opt = separate exp in
    let simplified_exp = merge exp const_opt in
    (* log "[Simplify] After: %a\n" pp simplified_exp; *)
    simplified_exp

  let rec simplify_const exp = match exp with
    | Const (Const.Cint x) -> x
    | BinOp (op, lexp, rexp) -> (
      let lconst = simplify_const lexp in
      let rconst = simplify_const rexp in
      eval_consts op lconst rconst
    )
    | UnOp (Unop.Neg, exp, _) -> simplify_const exp |> IntLit.neg
    | Max args -> (
      let simplified_args = List.map args ~f:(fun x -> simplify_const x) in
      Option.value_exn (List.max_elt simplified_args ~compare:IntLit.compare_value)
    )
    | Min args -> (
      let simplified_args = List.map args ~f:(fun x -> simplify_const x) in
      Option.value_exn (List.min_elt simplified_args ~compare:IntLit.compare_value)
    )
    | _ -> assert(false)


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
      | Const Const.Cint c1, Const Const.Cint c2 -> eval op c1 c2
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
      let accesses = AccessPath.of_exp ~include_array_indexes:true exp typ ~f_resolve_id:resolver in
      assert (Int.equal (List.length accesses) 1);
      let access = List.hd_exn accesses in
      Access access
      (* Ident.Map.add id (EdgeExp.Access access) graph_data.ident_map *)
      (* L.(die InternalError)"[EdgeExp.of_exp] Unsupported Lindex expression %a!" Exp.pp exp *)
    )
    | _ -> L.(die InternalError)"[EdgeExp.of_exp] Unsupported expression %a!" Exp.pp exp


  (* TODO: figure out what to do floats *)
  let rec to_z3_expr exp tenv smt_ctx access_map_func = 
    (* let int_sort = Z3.Arithmetic.Integer.mk_sort smt_ctx in *)
    let real_sort = Z3.Arithmetic.Real.mk_sort smt_ctx in
    let zero_const = Z3.Arithmetic.Real.mk_numeral_i smt_ctx 0 in

    (* let create_condition expr_z3 (typ : Typ.t) =
      match typ.desc with
      | Typ.Tint ikind when Typ.ikind_is_unsigned ikind -> [Z3.Arithmetic.mk_ge smt_ctx expr_z3 zero_const]
      | Typ.Tint _
      | Typ.Tfloat _ -> []
      | _ -> L.(die InternalError)"[EdgeExp.to_z3_expr] Unsupported type '%a' of expression '%s'" Typ.(pp Pp.text) typ (Z3.Expr.to_string expr_z3)
    in *)

    let rec make_access_term name (typ : Typ.t) = match typ.desc with
    | Tptr (ptr_type, _) -> (
      log "Tptr: %s, Type: %a\n" name Typ.(pp Pp.text) ptr_type;
      make_access_term name ptr_type
    )
    | Typ.Tint ikind -> (
      log "Tint: %s\n" name;
      let expr = Z3.Expr.mk_const_s smt_ctx name real_sort in
      if Typ.ikind_is_unsigned ikind then expr, Z3ExprSet.singleton (Z3.Arithmetic.mk_ge smt_ctx expr zero_const)
      else expr, Z3ExprSet.empty
    )
    | Typ.Tfloat _ -> Z3.Expr.mk_const_s smt_ctx name real_sort, Z3ExprSet.empty
    | Tstruct _ -> (
      Z3.Expr.mk_const_s smt_ctx name real_sort, Z3ExprSet.empty
      (* let lookup = Tenv.lookup tenv in
      let fieldname_str = String.rtake_while name ~f:(fun c -> Char.equal c '.' |> not) in
      log "Tstruct: %s (%a)\n" name Typ.Name.pp struct_name;
      log "Field: %s\n" fieldname_str;
      let fieldname = Fieldname.make struct_name fieldname_str in
      let field_info = Struct.get_field_info ~lookup fieldname typ in
      match field_info with
      | Some info -> make_access_term name info.typ
      | None -> (
        L.(die InternalError)"[EdgeExp.to_z3_expr] Missing struct field type information for '%s' access!" name
      ) *)
    )
    | TVar var_name -> (
      log "TVar: %s (%s)\n" name var_name;
      assert(false)
    )
    | Tarray {elt; length; stride} -> (
      log "Tarray: %s, Element type: %a\n" name Typ.(pp Pp.text) elt;
      make_access_term name elt
    )
    | _ -> (
      log "Unknown type: %s\n" name;
      assert(false);
      (* Z3.Expr.mk_const_s smt_ctx name int_sort, [] *)
    )
    (* | _ -> L.(die InternalError)"[EdgeExp.to_z3_expr] Unsupported access type '%a'" Typ.(pp Pp.text) typ *)
    in

    match exp with
    | Const (Const.Cint const) -> Z3.Arithmetic.Real.mk_numeral_i smt_ctx (IntLit.to_int_exn const), Z3ExprSet.empty
    | Const (Const.Cfloat const) -> Z3.Arithmetic.Real.mk_numeral_i smt_ctx (int_of_float const), Z3ExprSet.empty
    | Call (typ, procname, _, _) -> (
      (* Treat function without summary as constant *)
      make_access_term (Procname.to_string procname) typ
    )
    | Access access -> (
      match access_map_func with
      | Some func ->(
        match func access with
        | Some var -> var, Z3ExprSet.empty
        | None -> (
          match AccessPath.get_typ access tenv with
          | Some typ -> make_access_term (F.asprintf "%a" AccessPath.pp access) typ
          | _ -> assert(false)  
        )
      )
      | None -> (
        match AccessPath.get_typ access tenv with
        | Some typ -> make_access_term (F.asprintf "%a" AccessPath.pp access) typ
        | _ -> assert(false)
      )
    )
    (* | Access (((_, typ), access_list) as access) -> (
      match access_map_func with
      | Some func -> func access
      | None -> (
        List.iter access_list ~f:(fun sub_access -> log "Sub-access: %a\n" AccessPath.pp_access sub_access);
        make_access_term (F.asprintf "%a" AccessPath.pp access) typ
      )
    ) *)
    | BinOp (op, lexp, rexp) -> (
      let z3_lexp, z3_lexp_constraints = to_z3_expr lexp tenv smt_ctx access_map_func in
      let z3_rexp, z3_rexp_constraints = to_z3_expr rexp tenv smt_ctx access_map_func in
      
      (* let aux expr_z3 (typ_opt : Typ.ikind option) = match typ_opt with
      | Some ikind when Typ.ikind_is_unsigned ikind -> expr_z3, [Z3.Arithmetic.mk_ge smt_ctx expr_z3 zero_const]
      | _ -> expr_z3, []
      in *)
      let aux expr_z3 (typ_opt : Typ.ikind option) = match typ_opt with
      | Some ikind when Typ.ikind_is_unsigned ikind -> expr_z3, Z3ExprSet.empty
      | _ -> expr_z3, Z3ExprSet.empty
      in

      let eval_power exp = match exp with
      | Const (Const.Cint power_value) -> (
        let divisor = Int.pow 2 (IntLit.to_int_exn power_value) in
        Z3.Arithmetic.Real.mk_numeral_i smt_ctx divisor
      )
      | _ -> (
        let two_const = Z3.Arithmetic.Real.mk_numeral_i smt_ctx 2 in
        Z3.Arithmetic.mk_power smt_ctx two_const z3_rexp
      )
      in
      
      let expr_z3, constraints = match op with
      | Binop.Lt -> Z3.Arithmetic.mk_lt smt_ctx z3_lexp z3_rexp, Z3ExprSet.empty
      | Binop.Le -> Z3.Arithmetic.mk_le smt_ctx z3_lexp z3_rexp, Z3ExprSet.empty
      | Binop.Gt -> Z3.Arithmetic.mk_gt smt_ctx z3_lexp z3_rexp, Z3ExprSet.empty
      | Binop.Ge -> Z3.Arithmetic.mk_ge smt_ctx z3_lexp z3_rexp, Z3ExprSet.empty
      | Binop.Eq -> Z3.Boolean.mk_eq smt_ctx z3_lexp z3_rexp, Z3ExprSet.empty
      | Binop.Ne -> Z3.Boolean.mk_not smt_ctx (Z3.Boolean.mk_eq smt_ctx z3_lexp z3_rexp), Z3ExprSet.empty
      | Binop.MinusA ikind_opt -> aux (Z3.Arithmetic.mk_sub smt_ctx [z3_lexp; z3_rexp]) ikind_opt
      | Binop.PlusA ikind_opt -> aux (Z3.Arithmetic.mk_add smt_ctx [z3_lexp; z3_rexp]) ikind_opt
      | Binop.Mult ikind_opt -> aux (Z3.Arithmetic.mk_mul smt_ctx [z3_lexp; z3_rexp]) ikind_opt
      | Binop.Div  -> Z3.Arithmetic.mk_div smt_ctx z3_lexp z3_rexp, Z3ExprSet.empty
      | Binop.Shiftrt -> (
        (* Assumption: valid unsigned shifting *)
        let rexp = eval_power rexp in
        (* let two_const = Z3.Arithmetic.Integer.mk_numeral_i smt_ctx 2 in
        let rexp = Z3.Arithmetic.mk_power smt_ctx two_const z3_rexp in *)
        let expr_z3 = Z3.Arithmetic.mk_div smt_ctx z3_lexp rexp in
        (* expr_z3, [Z3.Arithmetic.mk_ge smt_ctx expr_z3 zero_const] *)
        expr_z3, Z3ExprSet.empty
      )
      | Binop.Shiftlt -> (
        (* Assumption: valid unsigned shifting *)
        let rexp = eval_power rexp in
        let expr_z3 = Z3.Arithmetic.mk_mul smt_ctx [z3_lexp; rexp] in
        (* expr_z3, [Z3.Arithmetic.mk_ge smt_ctx expr_z3 zero_const] *)
        expr_z3, Z3ExprSet.empty
      )
      | _ -> L.(die InternalError)"[EdgeExp.to_z3_expr] Expression '%a' contains invalid binary operator!" pp exp
      in
      expr_z3, Z3ExprSet.union constraints (Z3ExprSet.union z3_lexp_constraints z3_rexp_constraints)
    )
    | UnOp (Unop.Neg, subexp, _) -> (
      let subexp, conditions = to_z3_expr subexp tenv smt_ctx access_map_func in
      Z3.Arithmetic.mk_unary_minus smt_ctx subexp, conditions
    )
    | Max max_args -> (
      let z3_args, type_constraints = List.fold max_args ~init:([], Z3ExprSet.empty) ~f:(fun (args, constraints) arg ->
        let z3_arg, arg_type_constraints = to_z3_expr arg tenv smt_ctx access_map_func in
        z3_arg :: args, Z3ExprSet.union arg_type_constraints constraints
      )
      in
      if List.length max_args < 2 then (
        assert(List.length max_args > 0);
        let arg = List.hd_exn z3_args in
        let ite_condition = Z3.Arithmetic.mk_ge smt_ctx arg zero_const in
        (* let max_expr = Z3.Boolean.mk_ite smt_ctx ite_condition arg zero_const in *)
        (* max_expr, type_constraints *)

        (* TODO: should we include conditions "x >= 0" for each "max(x, 0)" expression? *)
        arg, Z3ExprSet.add ite_condition type_constraints
      ) else (
        (* TODO: Could we potentially extract single max(...) argument based on
         * currently examined bound parameter when checking monotony? (with some 
         * exceptions of course) This could help use get rid of max expressions in
         * Z3 altogether for those usecases.
         * This seems to be necessary if we want to avoid Z3 loops and unknown results *)
        let max_expr = List.reduce_exn z3_args ~f:(fun x y ->
          Z3.Boolean.mk_ite smt_ctx (Z3.Arithmetic.mk_ge smt_ctx x y) x y
        )
        in
        max_expr, type_constraints
      )
    )
    | _ -> L.(die InternalError)"[EdgeExp.to_z3_expr] Expression '%a' contains invalid element!" pp exp


  let rec always_positive exp tenv smt_ctx solver =
    let aux = function 
    | Const (Const.Cint x) -> not (IntLit.isnegative x)
    | Const (Const.Cfloat x) -> Float.(x >= 0.0)
    | Access ((_, typ), _) -> (match typ.desc with
      | Typ.Tint ikind -> Typ.ikind_is_unsigned ikind
      | _ -> false
    )
    | x -> always_positive x tenv smt_ctx solver
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
      if is_const exp then IntLit.geq (simplify_const exp) IntLit.zero
      else (
        let exp_z3, type_conditions = to_z3_expr exp tenv smt_ctx None in
        let zero_const = Z3.Arithmetic.Real.mk_numeral_i smt_ctx 0 in
        let rhs = Z3.Arithmetic.mk_ge smt_ctx exp_z3 zero_const in

        let formula = if Z3ExprSet.is_empty type_conditions then (
          Z3.Boolean.mk_not smt_ctx rhs
        ) else (
          let lhs = Z3ExprSet.elements type_conditions |> Z3.Boolean.mk_and smt_ctx in
          Z3.Boolean.mk_not smt_ctx (Z3.Boolean.mk_implies smt_ctx lhs rhs)
        )
        in
        let goal = (Z3.Goal.mk_goal smt_ctx true false false) in
        Z3.Goal.add goal [formula];
        Z3.Solver.reset solver;
        Z3.Solver.add solver (Z3.Goal.get_formulas goal);
        phys_equal (Z3.Solver.check solver []) Z3.Solver.UNSATISFIABLE
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


  let map_accesses bound ~f:f acc =
    let rec aux bound acc = match bound with
    | Access access -> f access acc
    | BinOp (op, lexp, rexp) -> (
      let lexp, acc = aux lexp acc in
      let rexp, acc = aux rexp acc in
      try_eval op lexp rexp, acc
      (* BinOp (op, lexp, rexp), acc *)
    )
    | UnOp (op, exp, typ) -> (
      let exp, acc = aux exp acc in
      UnOp (op, exp, typ), acc
    )
    | Max args -> (
      let args, acc = List.fold args ~init:([], acc) ~f:(fun (args, acc) arg ->
        let arg, acc = aux arg acc in
        args @ [arg], acc
      )
      in
      Max args, acc
    )
    | Min args -> (
      let args, acc = List.fold args ~init:([], acc) ~f:(fun (args, acc) arg ->
        let arg, acc = aux arg acc in
        args @ [arg], acc
      )
      in
      Min args, acc
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


  let determine_monotony exp tenv z3_ctx solver =
    try
      let exp_variables = Set.elements (get_accesses exp) in
      let real_sort = Z3.Arithmetic.Real.mk_sort z3_ctx in
      let param_sorts, param_symbols, bound_accesses = List.fold exp_variables ~init:([], [], [])
      ~f:(fun (sorts, symbols, accesses) variable ->
        match variable with
        | Access access -> (
          let access_str = F.asprintf "%a" AccessPath.pp access in
          let access_symbol = Z3.Symbol.mk_string z3_ctx access_str in
          match AccessPath.get_typ access tenv with
          | Some typ when Typ.is_int typ -> (
            sorts @ [real_sort], 
            symbols @ [access_symbol],
            accesses @ [access]
          )
          | _ -> assert(false)
        )
        | _ -> assert(false)
      )
      in

      if is_const exp then Map.empty
      else (
        let bound_func_decl = Z3.FuncDecl.mk_func_decl_s z3_ctx "bound_function" param_sorts real_sort in
        let params = List.map param_symbols ~f:(fun symbol -> Z3.Expr.mk_const z3_ctx symbol real_sort) in
        let func_app = Z3.Expr.mk_app z3_ctx bound_func_decl params in
        let q_bound_var = Z3.Quantifier.mk_bound z3_ctx 0 real_sort in

        let tmp_var_symbol = Z3.Symbol.mk_string z3_ctx "tmp_var" in
        let tmp_var_exp = Z3.Expr.mk_const z3_ctx tmp_var_symbol real_sort in

        List.foldi param_symbols ~init:Map.empty ~f:(fun replace_idx acc current_symbol ->
          let current_variable_exp = List.nth_exn exp_variables replace_idx in
          let param_access = List.nth_exn bound_accesses replace_idx in
          let param_sort = List.nth_exn param_sorts replace_idx in
          let param_name = Z3.Symbol.to_string current_symbol in
          let param_expr = Z3.Expr.mk_const z3_ctx current_symbol real_sort in

          let new_params = List.mapi params ~f:(fun param_idx param ->
            if Int.equal param_idx replace_idx then tmp_var_exp else param
          )
          in
          let z3_func_app_2 = Z3.Expr.mk_app z3_ctx bound_func_decl new_params in

          (* Construct Z3 bound with bound variable for the current parameter *)
          let bound_access_map access = if AccessPath.equal access param_access 
          then Some q_bound_var 
          else None
          in
          let z3_bound = to_z3_expr exp tenv z3_ctx (Some bound_access_map) |> fst in
          let type_constraints = to_z3_expr exp tenv z3_ctx None |> snd |> Z3ExprSet.elements in

          (* Use constructed bound in quantified expression to define function over all arguments *)
          let args = List.mapi params ~f:(fun param_idx param ->
            if Int.equal param_idx replace_idx then q_bound_var else param
          )
          in

          (* ForAll[x]: bound_func(.., x, ..) = bound_expr *)
          let q_func_app = Z3.Expr.mk_app z3_ctx bound_func_decl args in
          let q_body = Z3.Boolean.mk_eq z3_ctx q_func_app z3_bound in
          let quantifier = Z3.Quantifier.mk_forall z3_ctx [param_sort] [current_symbol] q_body None [] [] None None in
          let quantifier_expr = Z3.Expr.simplify (Z3.Quantifier.expr_of_quantifier quantifier) None in
          let solver_base_assertions = quantifier_expr :: type_constraints in

          (* debug_log "\n  [Z3 Quantifier body] %s\n" (Z3.Expr.to_string quantifier_body);
          debug_log "\n  [Z3 Bound function] %s\n" (Z3.Expr.to_string func_constraint); *)
          
          let antecedent = Z3.Arithmetic.mk_gt z3_ctx tmp_var_exp param_expr in
          let non_decreasing_consequent = Z3.Arithmetic.mk_ge z3_ctx z3_func_app_2 func_app in
          let non_decreasing_implication = Z3.Boolean.mk_implies z3_ctx antecedent non_decreasing_consequent in
          let non_decreasing_goal = Z3.Expr.simplify (Z3.Boolean.mk_not z3_ctx non_decreasing_implication) None in

          let non_increasing_consequent = Z3.Arithmetic.mk_le z3_ctx z3_func_app_2 func_app in
          let non_increasing_implication = Z3.Boolean.mk_implies z3_ctx antecedent non_increasing_consequent in
          let non_increasing_goal = Z3.Expr.simplify (Z3.Boolean.mk_not z3_ctx non_increasing_implication) None in

          (* debug_log "  [Z3 Goal] %s\n" (Z3.Expr.to_string goal); *)
          (* List.iter type_constraints ~f:(fun expr -> 
            debug_log "  [Z3 Type constraint] %s\n" (Z3.Expr.to_string expr);
          ); *)

          try
            (* Check for non-decreasing property first *)
            Z3.Solver.reset solver;
            Z3.Solver.add solver (non_decreasing_goal :: solver_base_assertions);

            match Z3.Solver.check solver [] with
            | Z3.Solver.UNSATISFIABLE -> (
              log "  [Variable: %s] Non-decreasing\n" param_name;
              Map.add current_variable_exp VariableMonotony.NonDecreasing acc
            )
            | Z3.Solver.SATISFIABLE -> (
              let decreasing_model = match Z3.Solver.get_model solver with
              | Some model -> Z3.Model.to_string model
              | None -> assert(false)
              in

              (* Check for non-increasing property next *)
              Z3.Solver.reset solver;
              Z3.Solver.add solver (non_increasing_goal :: solver_base_assertions);

              match Z3.Solver.check solver [] with
              | Z3.Solver.UNSATISFIABLE -> (
                log "  [Variable: %s] Non-increasing\n" param_name;
                Map.add current_variable_exp VariableMonotony.NonIncreasing acc
              )
              | Z3.Solver.SATISFIABLE -> (
                log "  [Variable: %s] Not Monotonic\n" param_name;
                Map.add current_variable_exp VariableMonotony.NotMonotonic acc
              ) 
              | Z3.Solver.UNKNOWN -> (
                (* EdgeExp.Map.add formal_exp FormalBoundMonotony.NotMonotonic acc *)
                L.die InternalError "[Monotony Check] Unknown Z3 result: %s\n" (Z3.Solver.get_reason_unknown solver)
              )
            )
            | Z3.Solver.UNKNOWN -> (
              (* EdgeExp.Map.add formal_exp FormalBoundMonotony.NotMonotonic acc *)
              L.die InternalError "[Monotony Check] Unknown Z3 result: %s\n" (Z3.Solver.get_reason_unknown solver)
            )
          with Z3.Error str -> (
            (* This should hopefully be only caused by potential Z3 timeout *)
            (* EdgeExp.Map.add formal_exp FormalBoundMonotony.NonDecreasing acc *)
            L.die InternalError "[Z3 Error] %s\n" str
          )
        )
      );
    with Z3.Error str -> (
      L.die InternalError "[Z3 Error] %s\n" str
    )


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

  (* type dc = t *)

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

  let is_decreasing (_, (_, op, const)) = match op with
    | Binop.PlusA _ -> IntLit.isnegative const
    | _ -> false
    (* | _ -> assert(false) *)

  let is_increasing (_, (_, op, const)) = match op with
    | Binop.PlusA _ -> not (IntLit.isnegative const) && not (IntLit.iszero const)
    | _ -> false
    (* | _ -> assert(false) *)

  let to_string (lhs, (rhs_norm, op, rhs_const)) guarded =
    let dc = if guarded then F.asprintf "%a' <= %a" EdgeExp.pp lhs EdgeExp.pp rhs_norm
    else F.asprintf "[%a]' <= [%a]" EdgeExp.pp lhs EdgeExp.pp rhs_norm
    in
    match op with
    | Binop.PlusA _ -> (
      if IntLit.iszero rhs_const then dc
      else if IntLit.isnegative rhs_const then dc ^ " - " ^ IntLit.to_string (IntLit.neg rhs_const)
      else dc ^ " + " ^ IntLit.to_string rhs_const
    )
    | Binop.Shiftrt -> (
      if IntLit.iszero rhs_const then dc
      else dc ^ F.asprintf " %s %a" (Binop.str Pp.text op) IntLit.pp rhs_const
    )
    | _ -> (
      L.(die InternalError)"TODO: unsupported op: %s %a" (Binop.str Pp.text op) IntLit.pp rhs_const
    )
    
  let pp fmt dc = 
    F.fprintf fmt "%s" (to_string dc false)

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

    (* let pp fmt map = iter (fun pvar _ -> F.fprintf fmt " %s " (Pvar.to_string pvar)) map *)

    let to_string map =
      let tmp = fold (fun lhs_norm dc_rhs acc ->
        acc ^ (to_string (lhs_norm, dc_rhs) false) ^ " "
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
      mutable bound: EdgeExp.t;
      mutable execution_cost: EdgeExp.t;
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
      bound = EdgeExp.Inf;
      execution_cost = EdgeExp.one;
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

    let derive_guards edge norms tenv smt_ctx solver =
      let cond_expressions = EdgeExp.Set.fold (fun cond acc -> 
        match cond with
        | EdgeExp.BinOp (_, EdgeExp.Const _, EdgeExp.Const _) -> acc
        | EdgeExp.BinOp _ -> (
          let cond_z3, type_conditions = EdgeExp.to_z3_expr cond tenv smt_ctx None in
          Z3ExprSet.add cond_z3 (Z3ExprSet.union type_conditions acc)
        )
        | _ -> L.(die InternalError)"[Guards] Condition of form '%a' is not supported" EdgeExp.pp cond
      ) edge.conditions Z3ExprSet.empty 
      in
      if Z3ExprSet.is_empty cond_expressions then (
        ()
      ) else (
        let lhs = Z3ExprSet.elements cond_expressions |> Z3.Boolean.mk_and smt_ctx in
        let zero_const = Z3.Arithmetic.Real.mk_numeral_i smt_ctx 0 in

        let guards = EdgeExp.Set.fold (fun norm acc ->         
          let solve_formula rhs =
            let rhs = Z3.Arithmetic.mk_gt smt_ctx rhs zero_const in
            let formula = Z3.Boolean.mk_not smt_ctx (Z3.Boolean.mk_implies smt_ctx lhs rhs) in
            let goal = (Z3.Goal.mk_goal smt_ctx true false false) in
            Z3.Goal.add goal [formula];
            Z3.Solver.reset solver;
            Z3.Solver.add solver (Z3.Goal.get_formulas goal);
            let solve_status = Z3.Solver.check solver [] in
            if phys_equal solve_status Z3.Solver.UNSATISFIABLE then (
              (* Implication [conditions] => [norm > 0] always holds *)
              EdgeExp.Set.add norm acc
            )
            else acc
          in
          match norm with
          (* TODO: add norm type conditions to condition set? *)
          | EdgeExp.BinOp _ | EdgeExp.Access _ -> solve_formula (fst (EdgeExp.to_z3_expr norm tenv smt_ctx None))
          | EdgeExp.Const Const.Cint _ -> acc
          | _ -> L.(die InternalError)"[Guards] Norm expression %a is not supported!" EdgeExp.pp norm

        ) norms EdgeExp.Set.empty
        in
        edge.guards <- guards;
      )


    let derive_constraint (_, edge_data, _) norm existing_norms formals =
      let dc_map = edge_data.constraints in

      let get_assignment lhs_access = match AccessPathMap.find_opt lhs_access edge_data.assignments with
      | Some rhs -> Some rhs
      | None -> (
        let base_pvar = Option.value_exn (Var.get_pvar (fst (fst lhs_access))) in
        if Pvar.Set.mem base_pvar formals then Some (EdgeExp.Access lhs_access) else None
      )
      in

      (* let process_assignment lhs_access rhs = match rhs with
        | EdgeExp.BinOp (op, (EdgeExp.Access _ as rhs_access_exp), EdgeExp.Const Const.Cint rhs_const) -> (
            let const_part = match op with
            | Binop.MinusA _ -> IntLit.neg rhs_const
            | Binop.PlusA _ -> rhs_const
            | _ -> assert(false)
            in
            rhs_access_exp, Some (Binop.PlusA None, const_part)
        )
        | EdgeExp.BinOp (op, EdgeExp.Const Const.Cint rhs_const, (EdgeExp.Access _ as rhs_access_exp)) -> (
          (* TODO: fix this for MinusA *)
            match op with
            | Binop.MinusA _ | Binop.PlusA _ -> rhs_access_exp, Some (Binop.PlusA None, rhs_const)
            | _ -> assert(false)
        )
        | EdgeExp.BinOp (_, EdgeExp.Access _, EdgeExp.Access _) -> (
          (* TODO *)
          rhs, None
        )
        | EdgeExp.BinOp _ -> EdgeExp.separate2 rhs
        | EdgeExp.Const (Const.Cint const) -> EdgeExp.zero, Some (Binop.PlusA None, const)
        | EdgeExp.Max _
        | EdgeExp.Min _
        | EdgeExp.Access _
        | EdgeExp.Call _ -> rhs, None
        | _ -> L.(die InternalError)"[TODO] Unsupported asssignment: %a = %a" AccessPath.pp lhs_access EdgeExp.pp rhs
      in *)

      let rec derive_rhs norm = match norm with
        | EdgeExp.Access access -> get_assignment access
        | EdgeExp.Const (Const.Cint _) -> Some norm
        | EdgeExp.BinOp (op, lexp, rexp) -> (
          log "Deriving for: %a %s %a\n" EdgeExp.pp lexp (Binop.str Pp.text op) EdgeExp.pp rexp;
          match derive_rhs lexp, derive_rhs rexp with
          | Some lexp_derived, Some rexp_derived -> Some (EdgeExp.BinOp (op, lexp_derived, rexp_derived))
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
          let exp_derived_opt = derive_rhs exp in
          match exp_derived_opt with
          | Some exp_derived -> (if EdgeExp.is_zero exp_derived 
            then exp_derived_opt 
            else Some (EdgeExp.UnOp (Unop.Neg, exp_derived, typ))
          )
          | None -> None
        )
        | EdgeExp.UnOp (_, _, _) -> assert(false)
        | EdgeExp.Max _ -> assert(false)
        | EdgeExp.Min _ -> assert(false)
        | _ -> Some norm
      in

      let rec is_new_norm rhs = not (EdgeExp.Set.mem rhs existing_norms) && match rhs with
        | EdgeExp.BinOp (op, lexp, EdgeExp.Const _) -> (
          match op with
          | Binop.Shiftrt -> (
            (* TODO: figure out a better way? *)
            true
          )
          | _ -> is_new_norm lexp
        )
        | EdgeExp.BinOp (op, EdgeExp.Const _, rexp) -> (
          match op with
          | Binop.Shiftrt -> assert(false)
          | _ -> is_new_norm rexp
        )
        | EdgeExp.BinOp (op, lexp, rexp) -> (
          match op with
          | Binop.Shiftrt -> true
          | _ -> is_new_norm lexp && is_new_norm rexp
        )
        | EdgeExp.UnOp (_, subexp, _) -> is_new_norm subexp
        | EdgeExp.Const _
        | EdgeExp.Max _
        | EdgeExp.Min _ -> false
        | _ -> true
        (* | EdgeExp.Access _ -> EdgeExp.Set.mem rhs existing_norms
        | EdgeExp.Const _ -> false
        | EdgeExp.Call _ -> false
        | EdgeExp.Max _ -> false
        | EdgeExp.Min _ -> false *)
      in

      if EdgeExp.is_variable norm formals then (match derive_rhs norm with
        | Some derived_rhs -> (
          let rhs_norm, rhs_const_opt = EdgeExp.separate derived_rhs in
          let merged = EdgeExp.merge rhs_norm rhs_const_opt in
          log "Derived RHS: %a\n" EdgeExp.pp merged;
          if EdgeExp.equal merged norm then (
            (* Norm doesn't change it's value on this edge *)
            let updated_dc_map = DC.Map.add_dc norm (DC.make_rhs norm) dc_map in
            edge_data.constraints <- updated_dc_map;
            EdgeExp.Set.empty
          )
          else (
            (* Derived RHS expression is not equal to the original norm *)
            log "Derived RHS is different\n";
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
              log "Derived lhs_norm == rhs_norm: %a == %a\n" EdgeExp.pp lhs_norm EdgeExp.pp rhs_norm;
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
                  (* DC.make_rhs merged *)
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
              let rhs_norm, op, rhs_const = dc_rhs in
              log "Adding DC: %a <= %a %s (%a)\n" EdgeExp.pp norm EdgeExp.pp rhs_norm (Binop.str Pp.text op) IntLit.pp rhs_const;
              let updated_dc_map = DC.Map.add_dc norm dc_rhs dc_map in
              edge_data.constraints <- updated_dc_map;
              EdgeExp.Set.empty

            ) else (
              log "Derived lhs_norm != rhs_norm: %a != %a\n" EdgeExp.pp lhs_norm EdgeExp.pp rhs_norm;
              let rhs_norm, op, rhs_const = match rhs_const_opt with
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
              let updated_dc_map = DC.Map.add_dc norm (rhs_norm, op, rhs_const) dc_map in
              edge_data.constraints <- updated_dc_map;
              let is_variable = EdgeExp.is_variable rhs_norm formals in
              (* let is_new = is_variable && is_new_norm rhs_norm in *)
              let is_new = is_new_norm rhs_norm in
              log "Derived: %a + (%a), [Variable norm: %B] [New norm: %B]\n" EdgeExp.pp rhs_norm IntLit.pp rhs_const is_variable is_new;
              if is_new then (
                log "Existing norms:\n";
                EdgeExp.Set.iter (fun norm -> log "  %a\n" EdgeExp.pp norm) existing_norms;
                EdgeExp.Set.singleton rhs_norm
              ) else EdgeExp.Set.empty
            )
          )
        )
        | None -> EdgeExp.Set.empty
      )
      else EdgeExp.Set.empty
  end

  include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(EdgeData)
  module NodeSet = Caml.Set.Make(V)
  module EdgeSet = Caml.Set.Make(E)

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
      let non_const_assignments = List.filter (AccessPathMap.bindings edge_data.assignments) ~f:(fun (lhs, rhs) ->
        not (EdgeExp.equal (EdgeExp.Access lhs) rhs)
      ) in

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
      let constraints = List.map (DC.Map.bindings edge_data.constraints) ~f:(fun dc -> (DC.to_string dc true)) in
      let label = F.asprintf "%s\n%s\n%s\n%s" label 
      (String.concat ~sep:"\n" guards) 
      (String.concat ~sep:"\n" constraints) calls_str in
      [`Label label; `Color 4711]
    )
    | DCP -> (
      let constraints = List.map (DC.Map.bindings edge_data.constraints) ~f:(fun dc -> (DC.to_string dc false)) in
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
        let norms = List.fold chain.data ~init:(EdgeExp.Set.empty, EdgeExp.Set.empty) 
        ~f:(fun (norms_1, norms_2) (_, _, (dst : Node.t)) ->
          let path_count = find_paths dst EdgeExp.Set.empty 0 in
          if path_count < 2 then EdgeExp.Set.add dst norms_1, norms_2
          else norms_1, EdgeExp.Set.add dst norms_2
        )
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

module Resets = Caml.Set.Make(struct
  type nonrec t = DCP.E.t * EdgeExp.t * IntLit.t
  [@@deriving compare]
end)

type cache = {
  updates: (Increments.t * Resets.t) EdgeExp.Map.t;
  variable_bounds: EdgeExp.t EdgeExp.Map.t;
  reset_chains: RG.Chain.Set.t EdgeExp.Map.t;
  positivity: bool EdgeExp.Map.t;
}

let empty_cache = { 
  updates = EdgeExp.Map.empty; 
  variable_bounds = EdgeExp.Map.empty;
  reset_chains = EdgeExp.Map.empty;
  positivity = EdgeExp.Map.empty;
}

let output_graph filepath graph output_fun =
  let out_c = Utils.out_channel_create_with_dir filepath in
  (* let fmt = F.formatter_of_out_channel out_c in *)
  (* ({ fname=filepath; out_c; fmt} : Utils.outfile) *)
  (* let out_file = create_graph_file filepath in *)
  output_fun out_c graph;
  Out_channel.close out_c


type summary = {
  formal_map: FormalMap.t;
  monotony_map: VariableMonotony.t EdgeExp.Map.t;
  bound: EdgeExp.t;
  return_bound: EdgeExp.t option;
}
[@@deriving compare]

let pp_summary fmt summary = EdgeExp.pp fmt summary.bound
