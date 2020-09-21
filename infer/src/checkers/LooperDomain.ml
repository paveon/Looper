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


module EdgeExp = struct
  type t =
  | BinOp of Binop.t * t * t
  | UnOp of Unop.t * t * Typ.t option
  | Access of AccessPath.t
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
    globals: Typ.t PvarMap.t;
    bound: t;
    return_bound: t option;
  }
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

  let is_const = function Const _ -> true | _ -> false

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

  let eval_consts op c1 c2 = match op with
    | Binop.PlusA _ -> IntLit.add c1 c2
    | Binop.MinusA _ -> IntLit.sub c1 c2
    | Binop.Mult _ -> IntLit.mul c1 c2
    | Binop.Div -> IntLit.div c1 c2
    | Binop.Ne -> if IntLit.eq c1 c2 then IntLit.zero else IntLit.one
    | Binop.Eq -> if IntLit.eq c1 c2 then IntLit.one else IntLit.zero
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


  (* let merge exp const = if IntLit.isnegative const 
      then try_eval (Binop.MinusA None) exp (Const (Const.Cint (IntLit.neg const)))
      else try_eval (Binop.PlusA None) exp (Const (Const.Cint const)) *)

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


  (* let rec separate exp = match exp with
    | Access _ -> exp, IntLit.zero
    | Const (Const.Cint c) -> zero, c
    | BinOp (op, lexp, rexp) -> (
      let (lexp_derived, l_const) = separate lexp in
      let (rexp_derived, r_const) = separate rexp in
      let lexp_derived, rexp_derived, const = match op with
      | Binop.PlusA _ -> (lexp_derived, rexp_derived, IntLit.add l_const r_const)
      | Binop.MinusA _ -> (lexp_derived, rexp_derived, IntLit.sub l_const r_const)
      | _ -> (
        (merge lexp_derived l_const, merge rexp_derived r_const, IntLit.zero)
      )
      in

      match is_zero lexp_derived, is_zero rexp_derived with
      | true, true -> (zero, const)
      | false, true -> (lexp_derived, const)
      | true, false -> (
        match op with
        | Binop.MinusA _ -> (UnOp (Unop.Neg, rexp_derived, None), const)
        | Binop.PlusA _ -> (rexp_derived, const)
        | _ -> assert(false)
      )
      | _ -> (
        if equal lexp_derived rexp_derived then match op with
          (* | Binop.MinusA _ -> Some (zero, IntLit.add l_const (IntLit.neg r_const)) *)
          | Binop.MinusA _ -> (zero, const)
          | Binop.PlusA _ -> (try_eval op lexp_derived rexp_derived, const)
          | _ -> assert(false)
        else (
          match op with
          | Binop.MinusA _ -> (try_eval op lexp_derived rexp_derived, const)
          | Binop.PlusA _ -> (try_eval op lexp_derived rexp_derived, const)
          | Binop.Div
          | Binop.Shiftrt 
          | Binop.Shiftlt -> (
            (try_eval op lexp_derived rexp_derived, const)
          )
          | _ -> assert(false)
        )
      )
    )
    | UnOp (op, exp, typ) -> (
      let (derived_exp, const) = separate exp in
      (UnOp (op, derived_exp, typ), const)
    )
    | Max _ | Min _ -> assert(false)
    | _ -> (exp, IntLit.zero) *)


  let rec separate2 exp = match exp with
    | Access _ -> exp, None
    | Const (Const.Cint c) -> zero, Some (Binop.PlusA None, c)
    | BinOp (op, lexp, rexp) -> (
      let lexp_derived, l_const_opt = separate2 lexp in
      let rexp_derived, r_const_opt = separate2 rexp in
      let lexp_derived, rexp_derived, const_part = match op with
      | Binop.PlusA _ -> (match l_const_opt, r_const_opt with
        | Some (l_op, l_const), Some (r_op, r_const) -> (
            match l_op, r_op with
          | Binop.PlusA _, Binop.PlusA _ -> lexp_derived, rexp_derived, Some (Binop.PlusA None, IntLit.add l_const r_const)
          | _ -> assert(false)
        )
        | _ -> assert(false)
      )
      | Binop.MinusA _ -> (match l_const_opt, r_const_opt with
        | Some (l_op, l_const), Some (r_op, r_const) -> (
          match l_op, r_op with
          | Binop.PlusA _, Binop.PlusA _ -> lexp_derived, rexp_derived, Some (Binop.PlusA None, IntLit.sub l_const r_const)
          | _ -> assert(false)
        )
        | _ -> assert(false)
      )
      | Binop.Shiftrt -> (match l_const_opt, r_const_opt with
        | Some (l_op, l_const), Some (r_op, r_const) -> (
          match l_op, r_op with
          | _, Binop.PlusA _ -> (
            let lexp_merged = merge lexp_derived l_const_opt in
            lexp_merged, rexp_derived, Some (Binop.Shiftrt, r_const)
          )
          | _ -> assert(false)
        )
        | _ -> assert(false)
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
      | _ -> (
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
          | Binop.Shiftrt 
          | Binop.Shiftlt -> (
            try_eval op lexp_derived rexp_derived, const_part
          )
          | _ -> assert(false)
        )
      )
    )
    | UnOp (op, exp, typ) -> (
      let derived_exp, const_opt = separate2 exp in
      UnOp (op, derived_exp, typ), const_opt
    )
    | Max _ | Min _ -> assert(false)
    | _ -> exp, None


  let simplify exp = 
    (* log "[Simplify] Before: %a\n" pp exp; *)
    let exp, const_opt = separate2 exp in
    let simplified_exp = merge exp const_opt in
    (* log "[Simplify] After: %a\n" pp simplified_exp; *)
    simplified_exp


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
  let rec to_z3_expr exp smt_ctx = 
    let int_sort = Z3.Arithmetic.Integer.mk_sort smt_ctx in
    let zero_const = Z3.Arithmetic.Integer.mk_numeral_i smt_ctx 0 in

    (* let create_condition expr_z3 (typ : Typ.t) =
      match typ.desc with
      | Typ.Tint ikind when Typ.ikind_is_unsigned ikind -> [Z3.Arithmetic.mk_ge smt_ctx expr_z3 zero_const]
      | Typ.Tint _
      | Typ.Tfloat _ -> []
      | _ -> L.(die InternalError)"[EdgeExp.to_z3_expr] Unsupported type '%a' of expression '%s'" Typ.(pp Pp.text) typ (Z3.Expr.to_string expr_z3)
    in *)

    let make_access_term name (typ : Typ.t) = match typ.desc with
      | Typ.Tint ikind -> (
        let expr = Z3.Expr.mk_const_s smt_ctx name int_sort in
        if Typ.ikind_is_unsigned ikind then expr, [Z3.Arithmetic.mk_ge smt_ctx expr zero_const]
        else expr, []
      )
      | Typ.Tfloat _ -> Z3.Expr.mk_const_s smt_ctx name int_sort, []
      | _ -> Z3.Expr.mk_const_s smt_ctx name int_sort, []
      (* | _ -> L.(die InternalError)"[EdgeExp.to_z3_expr] Unsupported access type '%a'" Typ.(pp Pp.text) typ *)
    in

    match exp with
    | Const (Const.Cint const) -> Z3.Arithmetic.Integer.mk_numeral_i smt_ctx (IntLit.to_int_exn const), []
    | Const (Const.Cfloat const) -> Z3.Arithmetic.Integer.mk_numeral_i smt_ctx (int_of_float const), []
    | Call (typ, procname, _, None) -> (
      (* Treat function without summary as constant *)
      make_access_term (Procname.to_string procname) typ
    )
    | Access (((_, typ), _) as access) -> make_access_term (F.asprintf "%a" AccessPath.pp access) typ
    | BinOp (op, lexp, rexp) -> (
      let lexp, lexp_type_conditions = to_z3_expr lexp smt_ctx in
      let rexp, rexp_type_conditions = to_z3_expr rexp smt_ctx in

      let aux expr_z3 (typ_opt : Typ.ikind option) = match typ_opt with
      | Some ikind when Typ.ikind_is_unsigned ikind -> expr_z3, [Z3.Arithmetic.mk_ge smt_ctx expr_z3 zero_const]
      | _ -> expr_z3, []
      in
      
      let expr_z3, condition = match op with
      | Binop.Lt -> Z3.Arithmetic.mk_lt smt_ctx lexp rexp, []
      | Binop.Le -> Z3.Arithmetic.mk_le smt_ctx lexp rexp, []
      | Binop.Gt -> Z3.Arithmetic.mk_gt smt_ctx lexp rexp, []
      | Binop.Ge -> Z3.Arithmetic.mk_ge smt_ctx lexp rexp, []
      | Binop.Eq -> Z3.Boolean.mk_eq smt_ctx lexp rexp, []
      | Binop.Ne -> Z3.Boolean.mk_not smt_ctx (Z3.Boolean.mk_eq smt_ctx lexp rexp), []
      | Binop.MinusA ikind_opt -> aux (Z3.Arithmetic.mk_sub smt_ctx [lexp; rexp]) ikind_opt
      | Binop.PlusA ikind_opt -> aux (Z3.Arithmetic.mk_add smt_ctx [lexp; rexp]) ikind_opt
      | Binop.Mult ikind_opt -> aux (Z3.Arithmetic.mk_mul smt_ctx [lexp; rexp]) ikind_opt
      | Binop.Div  -> Z3.Arithmetic.mk_div smt_ctx lexp rexp, []
      | Binop.Shiftrt -> (
        (* Assumption: valid unsigned shifting *)
        let two_const = Z3.Arithmetic.Integer.mk_numeral_i smt_ctx 2 in
        let rexp = Z3.Arithmetic.mk_power smt_ctx two_const rexp in
        let expr_z3 = Z3.Arithmetic.mk_div smt_ctx lexp rexp in
        expr_z3, [Z3.Arithmetic.mk_ge smt_ctx expr_z3 zero_const]
      )
      | Binop.Shiftlt -> (
        (* Assumption: valid unsigned shifting *)
        let two_const = Z3.Arithmetic.Integer.mk_numeral_i smt_ctx 2 in
        let rexp = Z3.Arithmetic.mk_power smt_ctx two_const rexp in
        let expr_z3 = Z3.Arithmetic.mk_mul smt_ctx [lexp; rexp] in
        expr_z3, [Z3.Arithmetic.mk_ge smt_ctx expr_z3 zero_const]
      )
      | _ -> L.(die InternalError)"[EdgeExp.to_z3_expr] Expression '%a' contains invalid binary operator!" pp exp
      in
      expr_z3, condition @ lexp_type_conditions @ rexp_type_conditions
    )
    | UnOp (Unop.Neg, subexp, _) -> (
      let subexp, conditions = to_z3_expr subexp smt_ctx in
      Z3.Arithmetic.mk_unary_minus smt_ctx subexp, conditions
    )
    | _ -> L.(die InternalError)"[EdgeExp.to_z3_expr] Expression '%a' contains invalid element!" pp exp


  let rec always_positive exp smt_ctx solver =
    let aux = function 
    | Const (Const.Cint x) -> not (IntLit.isnegative x)
    | Const (Const.Cfloat x) -> Float.(x >= 0.0)
    | Access ((_, typ), _) -> (match typ.desc with
      | Typ.Tint ikind -> Typ.ikind_is_unsigned ikind
      | _ -> false
    )
    | x -> always_positive x smt_ctx solver
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
      let exp_z3, type_conditions = to_z3_expr exp smt_ctx in
      let zero_const = Z3.Arithmetic.Integer.mk_numeral_i smt_ctx 0 in
      let rhs = Z3.Arithmetic.mk_ge smt_ctx exp_z3 zero_const in

      let formula = if List.is_empty type_conditions then (
        Z3.Boolean.mk_not smt_ctx rhs
      ) else (
        let lhs = Z3.Boolean.mk_and smt_ctx type_conditions in
        Z3.Boolean.mk_not smt_ctx (Z3.Boolean.mk_implies smt_ctx lhs rhs)
      )
      in
      let goal = (Z3.Goal.mk_goal smt_ctx true false false) in
      Z3.Goal.add goal [formula];
      Z3.Solver.reset solver;
      Z3.Solver.add solver (Z3.Goal.get_formulas goal);
      phys_equal (Z3.Solver.check solver []) Z3.Solver.UNSATISFIABLE
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
      BinOp (op, lexp, rexp), acc
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
    | UnOp (op, exp, typ) -> UnOp (op, aux exp, typ)
    | Max max_args -> Max (List.map max_args ~f:(fun arg -> aux arg))
    | Min min_args -> Min (List.map min_args ~f:(fun arg -> aux arg))
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


let pp_summary fmt (summary : EdgeExp.summary) = EdgeExp.pp fmt summary.bound


(* Difference Constraint of form "x <= y + c"
 * Example: "(len - i) <= (len - i) + 1" *)
module DC = struct
  type t = (EdgeExp.t * EdgeExp.t * IntLit.t)
  [@@deriving compare]

  type dc = t
  type rhs = (EdgeExp.t * IntLit.t)
  [@@deriving compare]

  let make ?(const = IntLit.zero) lhs rhs_norm = (lhs, rhs_norm, const)

  let make_rhs ?(const = IntLit.zero) rhs_norm = (rhs_norm, const)

  let is_constant (lhs, rhs, const) = EdgeExp.equal lhs rhs && IntLit.iszero const

  let same_norms (lhs, rhs, _) = EdgeExp.equal lhs rhs

  let is_decreasing (_, _, const) = IntLit.isnegative const

  let is_increasing (_, _, const) = not (IntLit.isnegative const) && not (IntLit.iszero const)

  let to_string (lhs, rhs_norm, rhs_const) guarded =
    let dc = if guarded then F.asprintf "%a' <= %a" EdgeExp.pp lhs EdgeExp.pp rhs_norm
    else F.asprintf "[%a]' <= [%a]" EdgeExp.pp lhs EdgeExp.pp rhs_norm
    in
    if IntLit.iszero rhs_const then dc
    else if IntLit.isnegative rhs_const then dc ^ " - " ^ IntLit.to_string (IntLit.neg rhs_const)
    else dc ^ " + " ^ IntLit.to_string rhs_const
    
  let pp fmt dc = 
    F.fprintf fmt "%s" (to_string dc false)

  module Map = struct
    include EdgeExp.Map

    let get_dc key map =
      match find_opt key map with
      | Some (rhs_norm, const) -> Some (key, rhs_norm, const)
      | None -> None

    let add_dc dc_lhs dc_rhs map =
      let rhs_norm, rhs_const = dc_rhs in
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
      let tmp = fold (fun lhs (rhs, const) acc ->
        acc ^ F.asprintf "(%a <= %a + %a)" EdgeExp.pp lhs EdgeExp.pp rhs IntLit.pp const  ^ " "
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

type call_site = EdgeExp.t * Location.t [@@deriving compare]

module CallSiteSet = Caml.Set.Make(struct
  type nonrec t = call_site
  let compare = compare_call_site
end)

module AccessSet = Caml.Set.Make(struct
  type nonrec t = AccessPath.t
  let compare = AccessPath.compare
end)

module AssignmentMap = Caml.Map.Make(struct
  type nonrec t = AccessPath.t
  let compare = AccessPath.compare
end)


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
      assignments: EdgeExp.t AssignmentMap.t;
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

    let equal = [%compare.equal: t]

    let is_reset edge norm = match DC.Map.get_dc norm edge.constraints with
      | Some dc -> not (DC.same_norms dc)
      | None -> false

    let is_exit_edge edge = edge.exit_edge

    let is_backedge edge = edge.backedge

    let active_guards edge = EdgeExp.Set.fold (fun guard acc ->
      match DC.Map.get_dc guard edge.constraints with
      | Some dc ->
        if DC.is_decreasing dc && DC.same_norms dc then acc
        else EdgeExp.Set.add guard acc
      | _ -> EdgeExp.Set.add guard acc
    ) edge.guards EdgeExp.Set.empty

    let modified edge = AssignmentMap.fold (fun lhs_access rhs_exp acc -> 
      if EdgeExp.equal (EdgeExp.Access lhs_access) rhs_exp then acc
      else AccessSet.add lhs_access acc
    ) edge.assignments AccessSet.empty

    let make assignments branch_info = {
      backedge = false;
      conditions = EdgeExp.Set.empty;
      assignments = assignments;
      modified = AccessSet.empty;
      branch_info = branch_info;

      calls = CallSiteSet.empty;
      constraints = DC.Map.empty;
      guards = EdgeExp.Set.empty;
      bound = EdgeExp.Inf;
      execution_cost = EdgeExp.one;
      bound_norm = None;
      computing_bound = false;
      exit_edge = false;

      edge_type = LTS
    }

    let empty = make AssignmentMap.empty None

    (* Required by Graph module interface *)
    let default = empty

    let branch_type edge = match edge.branch_info with
      | Some (_, branch, _) -> branch
      | _ -> false

    let set_backedge edge = { edge with backedge = true }

    let add_condition edge cond = if EdgeExp.is_zero cond then edge else
      { edge with conditions = EdgeExp.Set.add cond edge.conditions }

    let add_assignment edge lhs rhs = { edge with 
      assignments = AssignmentMap.add lhs rhs edge.assignments;
      modified = AccessSet.add lhs edge.modified;
    }  

    let add_invariants edge locals =
      let with_invariants = AccessSet.fold (fun local acc ->
        if AssignmentMap.mem local acc then acc else
        AssignmentMap.add local (EdgeExp.Access local) acc
      ) locals edge.assignments
      in
      { edge with assignments = with_invariants }

    let get_assignment_rhs edge lhs_access =
      match AssignmentMap.find_opt lhs_access edge.assignments with
      | Some rhs -> rhs
      | None -> EdgeExp.Access lhs_access

    let derive_guards edge norms solver smt_ctx =
      let cond_expressions = EdgeExp.Set.fold (fun cond acc -> 
        match cond with
        | EdgeExp.BinOp (_, EdgeExp.Const _, EdgeExp.Const _) -> acc
        | EdgeExp.BinOp _ -> (
          let cond_z3, type_conditions = EdgeExp.to_z3_expr cond smt_ctx in
          cond_z3 :: type_conditions @ acc
        )
        | _ -> L.(die InternalError)"[Guards] Condition of form '%a' is not supported" EdgeExp.pp cond
      ) edge.conditions [] 
      in
      if List.is_empty cond_expressions then (
        ()
      ) else (
        let lhs = Z3.Boolean.mk_and smt_ctx cond_expressions in
        let zero_const = Z3.Arithmetic.Integer.mk_numeral_i smt_ctx 0 in

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
          | EdgeExp.BinOp _ | EdgeExp.Access _ -> solve_formula (fst (EdgeExp.to_z3_expr norm smt_ctx))
          | EdgeExp.Const Const.Cint _ -> acc
          | _ -> L.(die InternalError)"[Guards] Norm expression %a is not supported!" EdgeExp.pp norm

        ) norms EdgeExp.Set.empty
        in
        edge.guards <- guards;
      )


    let derive_constraint2 (_, edge_data, _) norm existing_norms formals =
      let dc_map = edge_data.constraints in

      let get_assignment lhs_access = match AssignmentMap.find_opt lhs_access edge_data.assignments with
      | Some rhs -> Some rhs
      | None -> (
        let base_pvar = Option.value_exn (Var.get_pvar (fst (fst lhs_access))) in
        if Pvar.Set.mem base_pvar formals then Some (EdgeExp.Access lhs_access) else None
      )
      in

      let process_assignment lhs_access rhs = match rhs with
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
      in


      let rec derive_rhs norm = match norm with
        | EdgeExp.Access access -> (
          match get_assignment access with
          | Some assignment_rhs -> Some (process_assignment access assignment_rhs)
          | None -> None
          (* | None -> norm, IntLit.zero *)
        )
        | EdgeExp.Const (Const.Cint c) -> Some (EdgeExp.zero, Some (Binop.PlusA None, c))
        | EdgeExp.BinOp (op, lexp, rexp) -> (
          match derive_rhs lexp, derive_rhs rexp with
          | Some (lexp_derived, l_const_opt), Some (rexp_derived, r_const_opt) -> (
            (* let const = EdgeExp.eval_consts op l_const r_const in *)
            (* log "[Before] (%a + [%a]) %s (%a + [%a])\n" EdgeExp.pp lexp_derived IntLit.pp l_const (Binop.str Pp.text op) EdgeExp.pp rexp_derived IntLit.pp r_const; *)

            let lexp_derived, rexp_derived, const = match op with
            | Binop.PlusA _ -> (lexp_derived, rexp_derived, IntLit.add l_const r_const)
            | Binop.MinusA _ -> (lexp_derived, rexp_derived, IntLit.sub l_const r_const)
            | _ -> (
              merge lexp_derived l_const_opt, merge rexp_derived r_const_opt, None
            )
            in
            (* log "[After] (%a %s %a) + [%a]\n" EdgeExp.pp lexp_derived (Binop.str Pp.text op) EdgeExp.pp rexp_derived IntLit.pp const; *)

            match EdgeExp.is_zero lexp_derived, EdgeExp.is_zero rexp_derived with
            | true, true -> Some (EdgeExp.zero, const)
            | false, true -> Some (lexp_derived, const)
            | true, false -> (
              match op with
              | Binop.MinusA _ -> Some (EdgeExp.UnOp (Unop.Neg, rexp_derived, None), const)
              | Binop.PlusA _ -> Some (rexp_derived, const)
              | _ -> assert(false)
            )
            | _ -> (
              if EdgeExp.equal lexp_derived rexp_derived then match op with
                (* | Binop.MinusA _ -> Some (EdgeExp.zero, IntLit.add l_const (IntLit.neg r_const)) *)
                | Binop.MinusA _ -> Some (EdgeExp.zero, Some (Binop.PlusA None, const))
                | Binop.PlusA _ -> Some (EdgeExp.try_eval op lexp_derived rexp_derived, Some (Binop.PlusA None, const))
                | _ -> assert(false)
              else (
                match op with
                | Binop.MinusA _ -> Some (EdgeExp.try_eval op lexp_derived rexp_derived, const)
                | Binop.PlusA _ -> Some (EdgeExp.try_eval op lexp_derived rexp_derived, const)
                | Binop.Div
                | Binop.Shiftrt 
                | Binop.Shiftlt -> (
                  Some (EdgeExp.try_eval op lexp_derived rexp_derived, const)
                )
                | _ -> assert(false)
              )
            )
          )
          | _ -> None
        )
        (* | EdgeExp.UnOp (op, exp, typ) -> (match derive_rhs exp with
          | Some (derived_exp, const) -> Some (EdgeExp.UnOp (op, derived_exp, typ), const)
          | None -> None
        ) *)
        | EdgeExp.UnOp (Unop.Neg, exp, typ) -> (match derive_rhs exp with
          | Some (derived, const_opt) ->
            let derived = if EdgeExp.is_zero derived then derived else EdgeExp.UnOp (Unop.Neg, derived, typ) in
            let const_part = match const_opt with
            | Some (op, const) -> match op with
              | Binop.PlusA _ -> if IntLit.iszero const then Some (op, const) else Some (op, IntLit.neg const)
              | _ -> assert(false)
            | None -> None
            in
            Some (derived, const_part)
          | None -> None
        )
        | EdgeExp.UnOp (_, _, _) -> assert(false)
        | EdgeExp.Max _ -> assert(false)
        | EdgeExp.Min _ -> assert(false)
        | _ -> Some (norm, None)
      in

      let rec is_new_norm rhs = not (EdgeExp.Set.mem rhs existing_norms) && match rhs with
        | EdgeExp.BinOp (_, lexp, EdgeExp.Const _) -> is_new_norm lexp
        | EdgeExp.BinOp (_, EdgeExp.Const _, rexp) -> is_new_norm rexp
        | EdgeExp.BinOp (op, lexp, rexp) -> (match op with
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

      (* if EdgeExp.is_variable norm formals then match derive_rhs2 norm with
        | Some rhs_norm -> (
          if EdgeExp.equal norm rhs_norm then EdgeExp.Set.empty
          else (
            let is_variable = EdgeExp.is_variable rhs_norm formals in
            let is_new = is_variable && is_new_norm rhs_norm in
            log "Derived: %a, [Variable norm: %B] [New norm: %B]\n" EdgeExp.pp rhs_norm is_variable is_new;
            EdgeExp.Set.empty
            (* let dc_rhs = DC.make_rhs ~const:rhs_const rhs_norm in
            let updated_dc_map = DC.Map.add_dc norm dc_rhs dc_map in
            edge_data.constraints <- updated_dc_map;
            if is_new then EdgeExp.Set.singleton rhs_norm else EdgeExp.Set.empty *)
          )
        )
        | None -> EdgeExp.Set.empty
      else EdgeExp.Set.empty *)

      EdgeExp.Set.empty
      (* if EdgeExp.is_variable norm formals then match derive_rhs norm with
        | Some (rhs_norm, rhs_const) -> (
          let lhs_norm, lhs_const = EdgeExp.separate norm in
          let rhs_norm, rhs_const = if EdgeExp.is_zero rhs_norm 
            then (EdgeExp.Const (Const.Cint rhs_const), IntLit.zero)
            else rhs_norm, rhs_const
          in
          if EdgeExp.equal lhs_norm rhs_norm then (
            let diff = IntLit.sub rhs_const lhs_const in
            let dc_rhs = DC.make_rhs ~const:diff norm in
            let updated_dc_map = DC.Map.add_dc norm dc_rhs dc_map in
            edge_data.constraints <- updated_dc_map;
            EdgeExp.Set.empty
          ) else (
            let merged = EdgeExp.merge rhs_norm rhs_const in

            let dc_rhs = DC.make_rhs ~const:rhs_const rhs_norm in
            let updated_dc_map = DC.Map.add_dc norm dc_rhs dc_map in
            edge_data.constraints <- updated_dc_map;
            if (EdgeExp.equal norm rhs_norm && IntLit.iszero rhs_const) || EdgeExp.equal merged norm then (
              EdgeExp.Set.empty
            ) else (
              let is_variable = EdgeExp.is_variable rhs_norm formals in
              let is_new = is_variable && is_new_norm rhs_norm in
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
      else EdgeExp.Set.empty *)

    
    (* TODO: Completely rewrite in more general and elegant way, this is not maintainable *)
    (* Derive difference constraints "x <= y + c" based on edge assignments *)
    let derive_constraint (src, edge_data, dst) norm existing_norms formals =
      let dc_map = edge_data.constraints in
      let norm_set = EdgeExp.Set.empty in
      let get_assignment lhs_access = match AssignmentMap.find_opt lhs_access edge_data.assignments with
      | Some rhs -> Some rhs
      | None -> (
        let base_pvar = Option.value_exn (Var.get_pvar (fst (fst lhs_access))) in
        if Pvar.Set.mem base_pvar formals then Some (EdgeExp.Access lhs_access) else None
      )
      in
      let dc_map, norm_set = match norm with
      | EdgeExp.Access x_access -> (
        (* Norm [x] *)

        let x_pvar = Option.value_exn (Var.get_pvar (fst (fst x_access))) in
        if Pvar.Set.mem x_pvar formals then (
          (* Ignore norms that are formal parameters *)
          dc_map, norm_set
        ) else match AssignmentMap.find_opt x_access edge_data.assignments with
          | Some x_rhs -> (
            if EdgeExp.equal norm x_rhs then (
              (* [x = x], unchanged *)
              DC.Map.add_dc norm (DC.make_rhs norm) dc_map, norm_set
            ) else match x_rhs with
              | EdgeExp.BinOp (op, (EdgeExp.Access rhs_access as rhs_access_exp), EdgeExp.Const Const.Cint increment) -> (
                let const = match op with
                | Binop.PlusA _ -> increment
                | Binop.MinusA _ -> IntLit.neg increment
                | _ -> L.(die InternalError)"[TODO] currently unsupported binop operator!"
                in
                if AccessPath.equal x_access rhs_access then (
                  (* [x = x OP const] *)
                  let dc_rhs = DC.make_rhs ~const norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                ) else (
                  (* [x = z OP const] *)
                  let dc_rhs = DC.make_rhs ~const rhs_access_exp in
                  DC.Map.add_dc norm dc_rhs dc_map, EdgeExp.Set.add rhs_access_exp norm_set
                )
              )
              | EdgeExp.BinOp(op, EdgeExp.Access _, EdgeExp.Access _) -> (
                (* TODO: temporary work around, should figure out how to do this properly *)
                DC.Map.add_dc norm (DC.make_rhs x_rhs) dc_map, norm_set
                (* match op with
                | Binop.Shiftrt -> (
                  
                )
                | Binop.PlusA _ | Binop.MinusA _ -> (
                  DC.Map.add_dc norm (DC.make_rhs x_rhs) dc_map, norm_set
                ) *)
              )
              | EdgeExp.Access _ | EdgeExp.Const Const.Cint _-> (
                DC.Map.add_dc norm (DC.make_rhs x_rhs) dc_map, EdgeExp.Set.add x_rhs norm_set
              )
              | EdgeExp.Max _ | EdgeExp.Min _ -> (
                DC.Map.add_dc norm (DC.make_rhs x_rhs) dc_map, norm_set
              )
              | _ -> (
                DC.Map.add_dc norm (DC.make_rhs x_rhs) dc_map, norm_set
                (* L.(die InternalError)"[TODO] currently unsupported assignment expression [%a = %a]!" AccessPath.pp x_access EdgeExp.pp x_rhs *)
              )
          )
          | None -> dc_map, norm_set
      )
      | EdgeExp.BinOp (Binop.MinusA _, x, y) -> (
        match x, y with
        | EdgeExp.Const (Const.Cint _), EdgeExp.Access y_access -> (
          match get_assignment y_access with
          | Some y_rhs -> (
            if EdgeExp.equal y y_rhs then DC.Map.add_dc norm (DC.make_rhs norm) dc_map, norm_set
            else (
              (* [x_const - y] *)
              match y_rhs with
              | EdgeExp.BinOp (op, EdgeExp.Access y_rhs_access, EdgeExp.Const Const.Cint y_rhs_const) -> (
                assert(AccessPath.equal y_rhs_access y_access);
                match op with
                | Binop.PlusA _ -> (
                  (* norm [x_const - y], assignment [y = y + const] -> [(x_const - y) - const] *)

                  log "  [Edge] %a ---> %a\n" Node.pp src Node.pp dst;
                  log "    [New DC] (%a - %a), (%a = %a + %a) ---> (%a - %a) - %a\n" 
                  EdgeExp.pp x EdgeExp.pp y 
                  EdgeExp.pp y EdgeExp.pp y IntLit.pp y_rhs_const 
                  EdgeExp.pp x EdgeExp.pp y IntLit.pp y_rhs_const;

                  let dc_rhs = DC.make_rhs ~const:(IntLit.neg y_rhs_const) norm in
                  let dc_map = DC.Map.add_dc norm dc_rhs dc_map in 
                  dc_map, norm_set
                )
                | Binop.MinusA _ -> (
                  (* norm [x_const - y], assignment [y = y - const] -> [(x_const - y) + const] *)
                  let dc_rhs = DC.make_rhs ~const:y_rhs_const norm in
                  let dc_map = DC.Map.add_dc norm dc_rhs dc_map in
                  dc_map, norm_set
                )
                | _ -> (
                  L.(die InternalError)"[TODO] currently unsupported binop operator!"
                )
              )
              | EdgeExp.Access _ -> (
                (* norm [x_const - y], assignment [y = z] -> [x_const - z] *)
                let new_norm = EdgeExp.BinOp (Binop.MinusA None, x, y_rhs) in
                DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
              )
              | EdgeExp.Const (Const.Cint _) -> (
                (* norm [x_const - y], assignment [y = const] -> [eval_const] *)
                let eval_const = EdgeExp.try_eval (Binop.MinusA None) x y_rhs in
                DC.Map.add_dc norm (DC.make_rhs eval_const) dc_map, EdgeExp.Set.add eval_const norm_set
              )
              | _ -> L.(die InternalError)"[TODO] currently unsupported assignment expression!"
            )
          )
          | None -> dc_map, norm_set
        )
        | EdgeExp.Access x_access, EdgeExp.Const (Const.Cint _) -> (
          match get_assignment x_access with
          | Some x_rhs -> (
            if EdgeExp.equal x x_rhs then DC.Map.add_dc norm (DC.make_rhs norm) dc_map, norm_set
            else (
              (* [x - y_const] *)
              match x_rhs with
              | EdgeExp.BinOp (op, EdgeExp.Access x_rhs_access, EdgeExp.Const Const.Cint x_rhs_const) -> (
                assert(AccessPath.equal x_rhs_access x_access);
                match op with
                | Binop.PlusA _ -> (
                  (* norm [x - y_const], assignment [x = x + const] -> [(x - y_const) + const] *)
                  let dc_rhs = DC.make_rhs ~const:(x_rhs_const) norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | Binop.MinusA _ -> (
                  (* norm [x - y_const], assignment [x = x - const] -> [(x - y_const) - const] *)
                  let dc_rhs = DC.make_rhs ~const:(IntLit.neg x_rhs_const) norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | _ -> (
                  L.(die InternalError)"[TODO] currently unsupported binop operator!"
                )
              )
              | EdgeExp.Access _ -> (
                (* norm [x - y_const], assignment [x = z] -> [z - y_const] *)
                let new_norm = EdgeExp.BinOp (Binop.MinusA None, x_rhs, y) in
                DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
              )
              | EdgeExp.Const (Const.Cint _) -> (
                (* norm [x - y_const], assignment [x = const] -> [eval_const] *)
                let eval_const = EdgeExp.try_eval (Binop.MinusA None) x_rhs y in
                DC.Map.add_dc norm (DC.make_rhs eval_const) dc_map, EdgeExp.Set.add eval_const norm_set
              )
              | _ -> L.(die InternalError)"[TODO] currently unsupported assignment expression!"
            )
          )
          | None -> dc_map, norm_set
        )
        | EdgeExp.Access x_access, EdgeExp.Access y_access -> (
          (* Most common form of norm, obtained from condition of form [x > y] -> norm [x - y] *)

          match get_assignment x_access, get_assignment y_access with
          | Some x_rhs, Some y_rhs -> (
            match EdgeExp.equal x x_rhs, EdgeExp.equal y y_rhs with
            | true, true -> (
              (* assignments [x = x] and [y = y] *)
              DC.Map.add_dc norm (DC.make_rhs norm) dc_map, norm_set
            )
            | true, false -> (
              (* assignments [x = x] and [y = expr] *)
              match y_rhs with
              | EdgeExp.BinOp (op, EdgeExp.Access y_rhs_access, EdgeExp.Const Const.Cint y_rhs_const) -> (
                assert(not (AccessPath.equal y_rhs_access x_access));
                assert(AccessPath.equal y_rhs_access y_access);
                match op with
                | Binop.PlusA _ -> (
                  (* norm [x - y], assignment [y = y + const] -> [(x - y) - const] *)
                  let dc_rhs = DC.make_rhs ~const:(IntLit.neg y_rhs_const) norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | Binop.MinusA _ -> (
                  (* norm [x - y], assignment [y = y - const] -> [(x - y) + const] *)
                  let dc_rhs = DC.make_rhs ~const:y_rhs_const norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | _ -> (
                  L.(die InternalError)"[TODO] currently unsupported binop operator!"
                )
              )
              | EdgeExp.Access y_rhs_access -> (
                if AccessPath.equal y_rhs_access x_access then (
                  (* norm [x - y], assignment [y = x], zero interval *)
                  DC.Map.add_dc norm (DC.make_rhs EdgeExp.zero) dc_map, EdgeExp.Set.add EdgeExp.zero norm_set
                ) else (
                  (* norm [x - y], assignment [y = z] -> [x - z] *)
                  let new_norm = EdgeExp.BinOp (Binop.MinusA None, x, y_rhs) in
                  DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
                )
              )
              | EdgeExp.Const (Const.Cint const) -> (
                if IntLit.iszero const then (
                  (* norm [x - y], assignment [y = 0] -> [x] *)
                  DC.Map.add_dc norm (DC.make_rhs x) dc_map, EdgeExp.Set.add x norm_set
                ) else if IntLit.isone const then (
                  (* norm [x - y], assignment [y = 1] -> [x - 1] *)
                  DC.Map.add_dc norm (DC.make_rhs ~const:(IntLit.neg const) x) dc_map, EdgeExp.Set.add x norm_set
                ) else (
                  L.(die InternalError)"[TODO] currently unsupported assignment expression [%a = %a]!" AccessPath.pp y_access EdgeExp.pp y_rhs
                )
              )
              | _ -> L.(die InternalError)"[TODO] currently unsupported assignment expression [%a = %a]!" AccessPath.pp y_access EdgeExp.pp y_rhs
            )
            | false, true -> (
              (* assignments [y = y] and [x = expr] *)
              match x_rhs with
              | EdgeExp.BinOp (op, EdgeExp.Access x_rhs_access, EdgeExp.Const Const.Cint x_rhs_const) -> (
                assert(not (AccessPath.equal x_rhs_access y_access));
                assert(AccessPath.equal x_rhs_access x_access);
                match op with
                | Binop.PlusA _ -> (
                  (* norm [x - y], assignment [x = x + const] -> [(x - y) + const] *)
                  let dc_rhs = DC.make_rhs ~const:x_rhs_const norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | Binop.MinusA _ -> (
                  (* norm [x - y], assignment [x = x - const] -> [(x - y) - const] *)
                  let dc_rhs = DC.make_rhs ~const:(IntLit.neg x_rhs_const) norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | _ -> (
                  L.(die InternalError)"[TODO] currently unsupported binop operator!"
                )
              )
              | EdgeExp.Access x_rhs_access -> (
                if AccessPath.equal x_rhs_access x_access then (
                  (* norm [x - y], assignment [x = y], zero interval *)
                  DC.Map.add_dc norm (DC.make_rhs EdgeExp.zero) dc_map, EdgeExp.Set.add EdgeExp.zero norm_set
                ) else (
                  (* norm [x - y], assignment [x = z] -> [z - y] *)
                  let new_norm = EdgeExp.BinOp (Binop.MinusA None, x_rhs, y) in
                  DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
                )
              )
              | EdgeExp.Const (Const.Cint const) when IntLit.iszero const -> (
                (* norm [x - y], assignment [x = 0] -> [-y] *)
                log "-----------------------TEST--------------------";
                let new_norm = EdgeExp.UnOp (Unop.Neg, y, None) in
                DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
              )
              | _ -> L.(die InternalError)"[TODO] currently unsupported assignment expression!"
            )
            | _ -> (
              if EdgeExp.equal x_rhs y_rhs then (
                (* norm [x - y], assignments [x = expr] and [y = expr] -> 0 *)  
                DC.Map.add_dc norm (DC.make_rhs EdgeExp.zero) dc_map, EdgeExp.Set.add EdgeExp.zero norm_set
              )
              else (
                (* TODO: [x = e1] && [y = e2] -> [e1 - e2] *)
                match x_rhs, y_rhs with
                | EdgeExp.Const Const.Cint x_rhs_const, EdgeExp.Access _ -> (
                  let new_norm = EdgeExp.UnOp (Unop.Neg, y_rhs, None) in
                  if IntLit.iszero x_rhs_const then (
                    DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
                  ) else (
                    let dc_rhs = DC.make_rhs ~const:x_rhs_const new_norm in
                    DC.Map.add_dc norm dc_rhs dc_map, EdgeExp.Set.add new_norm norm_set
                  )
                )
                | EdgeExp.Access _, EdgeExp.Const Const.Cint y_rhs_const -> (
                  if IntLit.iszero y_rhs_const then (
                    DC.Map.add_dc norm (DC.make_rhs x_rhs) dc_map, EdgeExp.Set.add x_rhs norm_set
                  ) else dc_map, norm_set
                )
                | EdgeExp.Const Const.Cint x_const, EdgeExp.Const Const.Cint y_const -> (
                  let dc_rhs = DC.make_rhs (EdgeExp.Const (Const.Cint (IntLit.sub x_const y_const))) in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | _ -> L.(die InternalError)"[TODO] currently unsupported assignments '%a', '%a' !" EdgeExp.pp x_rhs EdgeExp.pp y_rhs
              )
            )
          )
          | _ -> (
            (* Both variables constituting the norm must be defined on edge
            * ie. the edge must at least contain constant assignment [var = var]
            * for both norm variables in order to derive difference constraint
            * for this norm *)
            dc_map, norm_set
          )
        )
        | EdgeExp.BinOp (Binop.PlusA _, (EdgeExp.Access x_access as x), (EdgeExp.Const Const.Cint const as c)), (EdgeExp.Access y_access as y) -> (
          (* TODO: rewrite entire derivation code for [x - y] exp as recursive
           * function which will determine if the overall value of a norm
           * increases/decreases. Current approach is hideous. *)

          match get_assignment x_access, get_assignment y_access with
          | Some x_rhs, Some y_rhs -> (
            match EdgeExp.equal x x_rhs, EdgeExp.equal y y_rhs with
            | true, false -> (
              match y_rhs with
              | EdgeExp.BinOp (op, EdgeExp.Access y_rhs_access, EdgeExp.Const Const.Cint y_rhs_const) -> (
                assert(AccessPath.equal y_access y_rhs_access);
                match op with
                | Binop.PlusA _ -> (
                  (* norm [x - y], assignment [y = y + const] -> [(x - y) - const] *)
                  let dc_rhs = DC.make_rhs ~const:(IntLit.neg y_rhs_const) norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | Binop.MinusA _ -> (
                  (* norm [x - y], assignment [y = y - const] -> [(x - y) + const] *)
                  let dc_rhs = DC.make_rhs ~const norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | _ -> (
                  L.(die InternalError)"[TODO] currently unsupported binop operator!"
                )
              )
              | EdgeExp.Access y_rhs_access when AccessPath.equal x_access y_rhs_access -> (
                DC.Map.add_dc norm (DC.make_rhs c) dc_map, EdgeExp.Set.add c norm_set
              )
              | _ -> L.(die InternalError)"[TODO] currently unsupported assignment '%a' !" EdgeExp.pp y_rhs
            )
            | _ -> DC.Map.add_dc norm (DC.make_rhs norm) dc_map, norm_set
          )
          | _ -> dc_map, norm_set
        )
        | x_exp, EdgeExp.Access y_access -> (
          (* TODO: fix this hack *)
          match get_assignment y_access with
          | Some y_rhs -> (
            if EdgeExp.equal y y_rhs then DC.Map.add_dc norm (DC.make_rhs norm) dc_map, norm_set
            else (
              (* [x_exp - y] *)
              match y_rhs with
              | EdgeExp.BinOp (op, EdgeExp.Access y_rhs_access, EdgeExp.Const Const.Cint y_rhs_const) -> (
                assert(AccessPath.equal y_rhs_access y_access);
                match op with
                | Binop.PlusA _ -> (
                  (* norm [x_exp - y], assignment [y = y + const] -> [(x_exp - y) - const] *)

                  log "  [Edge] %a ---> %a\n" Node.pp src Node.pp dst;
                  log "    [New DC] (%a - %a), (%a = %a + %a) ---> (%a - %a) - %a\n" 
                  EdgeExp.pp x EdgeExp.pp y 
                  EdgeExp.pp y EdgeExp.pp y IntLit.pp y_rhs_const 
                  EdgeExp.pp x EdgeExp.pp y IntLit.pp y_rhs_const;

                  let dc_rhs = DC.make_rhs ~const:(IntLit.neg y_rhs_const) norm in
                  let dc_map = DC.Map.add_dc norm dc_rhs dc_map in 
                  dc_map, norm_set
                )
                | Binop.MinusA _ -> (
                  (* norm [x_exp - y], assignment [y = y - const] -> [(x_exp - y) + const] *)
                  let dc_rhs = DC.make_rhs ~const:y_rhs_const norm in
                  let dc_map = DC.Map.add_dc norm dc_rhs dc_map in
                  dc_map, norm_set
                )
                | _ -> (
                  L.(die InternalError)"[TODO] currently unsupported binop operator!"
                )
              )
              | EdgeExp.Access _ -> (
                (* norm [x_exp - y], assignment [y = z] -> [x_exp - z] *)
                let new_norm = EdgeExp.BinOp (Binop.MinusA None, x, y_rhs) in
                DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
              )
              | EdgeExp.Const (Const.Cint _) -> (
                (* norm [x_exp - y], assignment [y = const] -> [x_exp - const] *)
                let new_norm = EdgeExp.BinOp (Binop.MinusA None, x, y_rhs) in
                DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add x norm_set
              )
              | y_rhs_exp -> (
                let new_norm = EdgeExp.BinOp (Binop.MinusA None, x, y_rhs_exp) in
                DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
              )
              | _ -> L.(die InternalError)"[TODO] currently unsupported assignment expression %a = %a!" EdgeExp.pp y EdgeExp.pp y_rhs
            )
          )
          | None -> dc_map, norm_set
        )
        | x_exp, y_exp -> (
          (* TODO: fix this hack *)
          dc_map, norm_set
        )
        (* | EdgeExp.Const Const.Cint x_const, EdgeExp.Access y_access -> (
          (* [x_const - y_pvar] *)

          match get_assignment y_access with
          | Some rhs -> (
            if not (EdgeExp.equal y rhs) then (
              match rhs with
              | EdgeExp.BinOp (op, EdgeExp.Access rhs_access, EdgeExp.Const Const.Cint const) -> (
                assert(AccessPath.equal y_access rhs_access);
                match op with
                | Binop.PlusA _ -> (
                  (* norm [x - y], assignment [y = y + const] -> [(x - y) - const] *)
                  let dc_rhs = DC.make_rhs ~const:(IntLit.neg const) norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | Binop.MinusA _ -> (
                  (* norm [x - y], assignment [y = y - const] -> [(x - y) + const] *)
                  let dc_rhs = DC.make_rhs ~const norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | _ -> (
                  L.(die InternalError)"[TODO] currently unsupported binop operator!"
                )
              )
              | EdgeExp.Const Const.Cint y_const -> (
                (* norm [x_const - y], assignment [y = const] -> [x_const - const] *)
                let new_norm = EdgeExp.Const (Const.Cint (IntLit.sub x_const y_const)) in
                DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
              )
              | EdgeExp.UnOp (Unop.Neg, EdgeExp.Const Const.Cint y_const, _) -> (
                let new_norm = EdgeExp.Const (Const.Cint (IntLit.add x_const y_const)) in
                DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
              )
              | _ -> L.(die InternalError)"[TODO] currently unsupported assignment '%a' !" EdgeExp.pp rhs
            ) else (
              DC.Map.add_dc norm (DC.make_rhs norm) dc_map, norm_set
            )
          )
          | _ -> (
            dc_map, norm_set
          )
        ) *)
        | _ -> L.(die InternalError)"[TODO] currently unsupported type of norm '%a' !" EdgeExp.pp norm
      )
      | EdgeExp.Const Const.Cint _ -> dc_map, norm_set
      | _ -> L.(die InternalError)"[TODO] currently unsupported type of norm '%a' !" EdgeExp.pp norm
      in
      edge_data.constraints <- dc_map;
      norm_set
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
    let call_list = List.map (CallSiteSet.elements edge_data.calls) ~f:(fun (call, loc) -> 
      F.asprintf "%a : %a" EdgeExp.pp call Location.pp loc
    ) 
    in
    let calls_str = String.concat ~sep:"\n" call_list in

    match edge_data.edge_type with
    | LTS -> (
      let conditions = List.map (EdgeExp.Set.elements edge_data.conditions) ~f:(fun cond -> EdgeExp.to_string cond) in
      let non_const_assignments = List.filter (AssignmentMap.bindings edge_data.assignments) ~f:(fun (lhs, rhs) ->
        not (EdgeExp.equal (EdgeExp.Access lhs) rhs)
      ) in

      let assignments = List.map (AssignmentMap.bindings edge_data.assignments) ~f:(fun (lhs, rhs) ->
        F.asprintf "%a = %s" AccessPath.pp lhs (EdgeExp.to_string rhs)
      ) in

      let label = F.asprintf "%s\n%s\n%s\n%s" label (String.concat ~sep:"\n" conditions) 
        (String.concat ~sep:"\n" assignments) calls_str 
      in
      [`Label label; `Color 4711]
    )
    | GuardedDCP -> (
      let guards = List.map (EdgeExp.Set.elements edge_data.guards) ~f:(fun guard -> EdgeExp.to_string guard) in
      let constraints = List.map (DC.Map.bindings edge_data.constraints) ~f:(fun (l, (n, c)) -> (DC.to_string (l, n, c) true)) in
      let label = F.asprintf "%s\n%s\n%s\n%s" label 
      (String.concat ~sep:" > 0\n" guards) 
      (String.concat ~sep:"\n" constraints) calls_str in
      [`Label label; `Color 4711]
    )
    | DCP -> (
      let constraints = List.map (DC.Map.bindings edge_data.constraints) ~f:(fun (l, (n, c)) -> (DC.to_string (l, n, c) false)) in
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
}

let empty_cache = { 
  updates = EdgeExp.Map.empty; 
  variable_bounds = EdgeExp.Map.empty;
  reset_chains = EdgeExp.Map.empty;
}

let output_graph filepath graph output_fun =
  let out_c = Utils.out_channel_create_with_dir filepath in
  (* let fmt = F.formatter_of_out_channel out_c in *)
  (* ({ fname=filepath; out_c; fmt} : Utils.outfile) *)
  (* let out_file = create_graph_file filepath in *)
  output_fun out_c graph;
  Out_channel.close out_c