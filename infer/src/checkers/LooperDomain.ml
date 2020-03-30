open! IStd
module F = Format
module L = Logging


module PvarMap = struct
  include Caml.Map.Make(Pvar)

  let pp fmt map =
    iter (fun pvar _ ->
      F.fprintf fmt " %s " (Pvar.to_string pvar)
    ) map

  let to_string map =
    let tmp = fold (fun pvar _ acc ->
      acc ^ Pvar.to_string pvar ^ " "
    ) map ""
    in
    "[" ^ (String.rstrip tmp) ^ "]"
end


module EdgeExp = struct
  type t =
  | BinOp of Binop.t * t * t
  | UnOp of Unop.t * t * Typ.t option
  | Access of AccessPath.t
  | Var of Pvar.t
  | Const of Const.t
  | Call of Typ.t * Procname.t * call_arg list * summary 
  | Max of t list
  | Min of t list
  | Inf
  [@@deriving compare]

  and call_arg = (t * Typ.t) [@@deriving compare]

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

  let equal = [%compare.equal: t]

  let one = Const (Const.Cint IntLit.one)

  let zero = Const (Const.Cint IntLit.zero)

  let is_zero = function Const const -> Const.iszero_int_float const | _ -> false

  let is_one = function Const (Const.Cint const) -> IntLit.isone const | _ -> false

  let rec is_int exp type_map = match exp with
    | BinOp (_, lexp, rexp) -> is_int lexp type_map && is_int rexp type_map
    | UnOp (_, exp, typ) -> (match typ with
      | Some typ -> Typ.is_int typ
      | None -> is_int exp type_map
    )
    | Var pvar -> (match PvarMap.find_opt pvar type_map with
      | Some pvar_typ -> Typ.is_int pvar_typ
      | None -> false (* [TODO] How the hell can I get the type of a global?! *)
    )
    | Const Const.Cint _ -> true
    | Call (ret_typ, _, _, _) -> Typ.is_int ret_typ
    | _ -> false


  let rec of_exp exp ident_map = match exp with
    | Exp.BinOp (op, lexp, rexp) -> (
      let lexp = of_exp lexp ident_map in
      let rexp = of_exp rexp ident_map in
      BinOp (op, lexp, rexp)
    )
    | Exp.UnOp (op, sub_exp, typ) -> UnOp (op, of_exp sub_exp ident_map, typ)
    | Exp.Var ident -> Ident.Map.find ident ident_map
    | Exp.Cast (_, exp) -> of_exp exp ident_map
    | Exp.Lvar pvar -> Var pvar
    | Exp.Const const -> Const const
    | _ -> assert(false)


  let get_vars exp =
    let rec aux exp set = match exp with
    | Var var -> Pvar.Set.add var set
    | BinOp (_, lexp, rexp) -> aux rexp (aux lexp set)
    | UnOp (_, exp, _) -> aux exp set
    | Max args -> List.fold args ~init:set ~f:(fun acc arg -> aux arg acc)
    | Min args -> List.fold args ~init:set ~f:(fun acc arg -> aux arg acc)
    | _ -> set
    in
    aux exp Pvar.Set.empty

  let get_exp_vars exp =
    let vars = get_vars exp in
    Pvar.Set.fold (fun pvar acc -> Set.add (Var pvar) acc) vars Set.empty

  let iter_vars bound ~f:f = Pvar.Set.iter f (get_vars bound)


  let map_vars bound ~f:f acc =
    let rec aux bound acc = match bound with
    | Var var -> f var acc
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
    let formal_indices = FormalMap.get_formals_indexes formal_map in
    let rec aux bound = match bound with
    | Var bound_pvar -> (
      let formal_idx = List.find formal_indices ~f:(fun ((formal_var, _), _) -> 
        Var.equal formal_var (Var.of_pvar bound_pvar)
      )
      in
      match formal_idx with
      | Some (_, idx) -> (
        let subst_exp, _ = List.nth_exn args idx in
        subst_exp
      )
      | None -> bound
    )
    | BinOp (op, lexp, rexp) -> BinOp (op, aux lexp, aux rexp)
    | UnOp (op, exp, typ) -> UnOp (op, aux exp, typ)
    | Max max_args -> Max (List.map max_args ~f:(fun arg -> aux arg))
    | Min min_args -> Min (List.map min_args ~f:(fun arg -> aux arg))
    | _ -> bound
    in
    aux bound


  let normalize_condition exp = 
    let negate_lop lop = match lop with
    | Binop.Lt -> Binop.Ge
    | Binop.Gt -> Binop.Le
    | Binop.Le -> Binop.Gt
    | Binop.Ge -> Binop.Lt
    | Binop.Eq -> Binop.Ne
    | Binop.Ne -> Binop.Eq
    | _ -> lop
    in

    let aux (op, lexp, rexp) = match op with
    | Binop.Lt -> BinOp (Binop.Gt, rexp, lexp)
    | Binop.Le -> BinOp (Binop.Ge, rexp, lexp)
    | _ -> BinOp (op, lexp, rexp)
    in
    match exp with
    | BinOp (op, lexp, rexp) -> aux (op, lexp, rexp)
    | UnOp (Unop.LNot, exp, _) -> (
      (* Currently handles only "!exp" *)
      match exp with
      | BinOp (op, lexp, rexp) -> aux (negate_lop op, lexp, rexp)
      | Const _ -> BinOp (Binop.Eq, exp, zero)
      | _ -> L.(die InternalError)"Unsupported condition type!"
    )
    | Const _ -> BinOp (Binop.Ne, exp, zero)
    | _ -> L.(die InternalError)"Unsupported condition type!"


  let add e1 e2 = match is_zero e1, is_zero e2 with
  | false, false -> BinOp (Binop.PlusA None, e1, e2)
  | true, false -> e2
  | false, true -> e1
  | _ -> zero


  let sub e1 e2 = match is_zero e1, is_zero e2 with
  | false, false -> BinOp (Binop.MinusA None, e1, e2)
  | true, false -> e2
  | false, true -> e1
  | _ -> zero


  let mult e1 e2 = if is_zero e1 || is_zero e2 then zero
  else (
    match is_one e1, is_one e2 with
    | true, true -> one
    | true, false -> e2
    | false, true -> e1
    | _ -> BinOp (Binop.Mult None, e1, e2)
  )


  let rec to_string ?(braces = false) = function
  | BinOp (op, lhs, rhs) -> (
    F.sprintf "(%s %s %s)" (to_string ~braces:true lhs) (Binop.str Pp.text op) (to_string ~braces:true rhs)
    (* if braces then F.sprintf "(%s %s %s)" (to_string lhs) (Binop.str Pp.text op) (to_string rhs)
    else (
      F.sprintf "%s %s %s" (to_string ~braces:true lhs) (Binop.str Pp.text op) (to_string ~braces:true rhs)
    ) *)
  )
  | UnOp (op, exp, _) -> F.sprintf "%s%s" (Unop.to_string op) (to_string exp)
  | Access path -> F.asprintf "%a" AccessPath.pp path
  | Var pvar -> Pvar.to_string pvar
  | Const const -> Exp.to_string (Exp.Const const)
  | Call (_, callee, args, summary) -> (
    let proc_name = Procname.to_simplified_string callee in
    let proc_name = String.slice proc_name 0 (String.length proc_name - 1) in
    let str = (List.fold args ~init:(proc_name) ~f:(fun acc (arg, _) -> acc ^ (to_string arg))) ^ ")" in
    match summary.return_bound with
    | Some return_bound -> str ^ " : " ^ to_string return_bound
    | None -> str
  )
  | Max args -> if Int.equal (List.length args) 1 then (
    let arg = List.hd_exn args in
    let str = to_string arg in
    match arg with 
    | Var _ -> F.sprintf "[%s]" str
    | _ -> F.sprintf "max(%s, 0)" str
  ) else (
    if List.is_empty args then (
      assert(false)
    ) else (
      let str = List.fold args ~init:"max(" ~f:(fun str arg -> str ^ to_string arg ^ ", ") in
      (String.slice str 0 ((String.length str) - 2)) ^ ")"
    )
  )
  | Min args -> if Int.equal (List.length args) 1 then (
    to_string (List.hd_exn args)
  ) else (
    let str = List.fold args ~init:"min(" ~f:(fun str arg -> str ^ to_string arg ^ ", ") in
    (String.slice str 0 ((String.length str) - 2)) ^ ")"
  )
  | Inf -> "Infinity"


  let pp fmt exp = F.fprintf fmt "%s" (to_string exp)
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
    let dc = if guarded then (
      F.asprintf "%s' <= %s" (EdgeExp.to_string lhs ~braces:true) (EdgeExp.to_string rhs_norm ~braces:true)
    ) else (
      F.asprintf "[%s]' <= [%s]" (EdgeExp.to_string lhs) (EdgeExp.to_string rhs_norm)
    ) 
    in
    if IntLit.iszero rhs_const then (
      dc
    ) else if IntLit.isnegative rhs_const then (
      dc ^ " - " ^ IntLit.to_string (IntLit.neg rhs_const)
    ) else (
      dc ^ " + " ^ IntLit.to_string rhs_const
    )
    
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
  end
end

let is_loop_prune : Sil.if_kind -> bool = function
  | Ik_dowhile | Ik_for | Ik_while -> true
  | _ -> false

let pp_element fmt (kind, branch, loc) = 
  let kind = Sil.if_kind_to_string kind in
  F.fprintf fmt "%s[%s](%B)" kind (Location.to_string loc) branch

let rec exp_to_z3_expr smt_ctx exp = 
  let int_sort = Z3.Arithmetic.Integer.mk_sort smt_ctx in
  match exp with
  | EdgeExp.Const (Const.Cint const) -> (
    let const_value = IntLit.to_int_exn const in
    Z3.Arithmetic.Integer.mk_numeral_i smt_ctx const_value
  )
  | EdgeExp.Var pvar -> Z3.Expr.mk_const_s smt_ctx (Pvar.to_string pvar) int_sort
  | EdgeExp.BinOp (op, lexp, rexp) -> (
    let lexp = exp_to_z3_expr smt_ctx lexp in
    let rexp = exp_to_z3_expr smt_ctx rexp in
    match op with
    | Binop.MinusA _ -> Z3.Arithmetic.mk_sub smt_ctx [lexp; rexp]
    | Binop.PlusA _ -> Z3.Arithmetic.mk_add smt_ctx [lexp; rexp]
    | Binop.Mult _ -> Z3.Arithmetic.mk_mul smt_ctx [lexp; rexp]
    | _ -> L.(die InternalError)"[Z3 expr] Expression contains invalid binary operator!"
  )
  | _ -> L.(die InternalError)"[Z3 expr] Expression contains invalid element!"


type graph_type = | LTS | GuardedDCP | DCP

let active_graph_type = ref LTS

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


(* Difference Constraint Program *)
module DCP = struct
  module Node = struct
    type t = 
      | Prune of (Sil.if_kind * Location.t)
      | Start of Location.t
      | Join of Location.t
      | Exit
    [@@deriving compare]

    let equal = [%compare.equal: t]
    let hash = Hashtbl.hash

    let is_join : t -> bool = function Join _ -> true | _ -> false

    let rec to_string loc = match loc with
      | Prune (kind, loc) -> F.sprintf "%s [%s]" (Sil.if_kind_to_string kind) (Location.to_string loc)
      | Start loc -> F.sprintf "Begin [%s]" (Location.to_string loc)
      | Join loc -> F.sprintf "Join [%s]" (Location.to_string loc)
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
      assignments: EdgeExp.t PvarMap.t;
      modified: Pvar.Set.t;
      branch_info: (Sil.if_kind * bool * Location.t) option;
      exit_edge: bool;

      mutable calls: CallSiteSet.t;
      mutable constraints: DC.rhs DC.Map.t;
      mutable guards: EdgeExp.Set.t;
      mutable bound: EdgeExp.t;
      mutable execution_cost: EdgeExp.t;
      mutable bound_norm: EdgeExp.t option;
      mutable computing_bound: bool;
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

    let modified_pvars edge = PvarMap.fold (fun pvar exp pvar_set -> 
      if EdgeExp.equal (EdgeExp.Var pvar) exp then pvar_set
      else Pvar.Set.add pvar pvar_set
    ) edge.assignments Pvar.Set.empty

    let make assignments branch_info = {
      backedge = false;
      conditions = EdgeExp.Set.empty;
      assignments = assignments;
      modified = Pvar.Set.empty;
      branch_info = branch_info;

      calls = CallSiteSet.empty;
      constraints = DC.Map.empty;
      guards = EdgeExp.Set.empty;
      bound = EdgeExp.Inf;
      execution_cost = EdgeExp.one;
      bound_norm = None;
      computing_bound = false;
      exit_edge = false;
    }

    let empty = make PvarMap.empty None

    (* Required by Graph module interface *)
    let default = empty

    let set_backedge edge = { edge with backedge = true }

    let add_condition edge cond = if EdgeExp.is_zero cond then edge else
      { edge with conditions = EdgeExp.Set.add cond edge.conditions }

    let add_assignment edge lhs rhs =
      { edge with 
        assignments = PvarMap.add lhs rhs edge.assignments;
        modified = Pvar.Set.add lhs edge.modified;
      }  

    let add_invariants edge locals =
      let unmodified = Pvar.Set.diff locals edge.modified in
      let with_invariants = Pvar.Set.fold (fun lhs acc ->
        if PvarMap.mem lhs acc then (
          F.printf "[Warning] Assignment map already contains key";
          acc
        ) else (
          PvarMap.add lhs (EdgeExp.Var lhs) acc
        )
      ) unmodified edge.assignments
      in
      { edge with assignments = with_invariants }

    let get_assignment_rhs edge lhs =
      match PvarMap.find_opt lhs edge.assignments with
      | Some rhs -> rhs
      | None -> EdgeExp.Var lhs

    let derive_guards edge norms solver smt_ctx =
      let cond_expressions = EdgeExp.Set.fold (fun cond acc -> 
        match cond with
        | EdgeExp.BinOp (_, EdgeExp.Const _, EdgeExp.Const _) -> acc
        | EdgeExp.BinOp (op, lexp, rexp) -> (
          let lexp_const = exp_to_z3_expr smt_ctx lexp in
          let rexp_const = exp_to_z3_expr smt_ctx rexp in
          match op with
          | Binop.Lt -> List.append [Z3.Arithmetic.mk_lt smt_ctx lexp_const rexp_const] acc
          | Binop.Le -> List.append [Z3.Arithmetic.mk_le smt_ctx lexp_const rexp_const] acc
          | Binop.Gt -> List.append [Z3.Arithmetic.mk_gt smt_ctx lexp_const rexp_const] acc
          | Binop.Ge -> List.append [Z3.Arithmetic.mk_ge smt_ctx lexp_const rexp_const] acc
          | Binop.Eq -> List.append [Z3.Boolean.mk_eq smt_ctx lexp_const rexp_const] acc
          | Binop.Ne -> (
            let eq = Z3.Boolean.mk_eq smt_ctx lexp_const rexp_const in
            List.append [Z3.Boolean.mk_not smt_ctx eq] acc
          )
          | _ -> L.(die InternalError)"[Guards] Condition binop [%a] is not supported!" EdgeExp.pp cond
        )
        | _ -> L.(die InternalError)"[Guards] Condition type is not supported by guard!"
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
          | EdgeExp.BinOp _ | EdgeExp.Var _ -> (
            let rhs = exp_to_z3_expr smt_ctx norm in
            solve_formula rhs
          )
          | EdgeExp.Const Const.Cint _ -> acc
          | _ -> (
            L.(die InternalError)"[Guards] Norm expression %a is not supported!" EdgeExp.pp norm
          )

        ) norms EdgeExp.Set.empty
        in
        edge.guards <- guards;
      )
    
    (* Derive difference constraints "x <= y + c" based on edge assignments *)
    let derive_constraint edge norm formals =
      let dc_map = edge.constraints in
      let norm_set = EdgeExp.Set.empty in
      let get_assignment pvar = match PvarMap.find_opt pvar edge.assignments with
      | Some rhs -> Some rhs
      | None -> if Pvar.Set.mem pvar formals then Some (EdgeExp.Var pvar) else None
      in
      let dc_map, norm_set = match norm with
      | EdgeExp.Var x_pvar -> (
        (* Norm [x] *)
        if Pvar.Set.mem x_pvar formals then (
          (* Ignore norms that are formal parameters *)
          dc_map, norm_set
        ) else match PvarMap.find_opt x_pvar edge.assignments with
          | Some x_rhs -> (
            if EdgeExp.equal norm x_rhs then (
              (* [x = x], unchanged *)
              DC.Map.add_dc norm (DC.make_rhs norm) dc_map, norm_set
            ) else match x_rhs with
              | EdgeExp.BinOp (op, EdgeExp.Var rhs_pvar, EdgeExp.Const Const.Cint increment) -> (
                let const = match op with
                | Binop.PlusA _ -> increment
                | Binop.MinusA _ -> IntLit.neg increment
                | _ -> L.(die InternalError)"[TODO] currently unsupported binop operator!"
                in
                if Pvar.equal x_pvar rhs_pvar then (
                  (* [x = x OP const] *)
                  let dc_rhs = DC.make_rhs ~const norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                ) else (
                  (* [x = z OP const] *)
                  let rhs_pvar_exp = EdgeExp.Var rhs_pvar in
                  let dc_rhs = DC.make_rhs ~const rhs_pvar_exp in
                  DC.Map.add_dc norm dc_rhs dc_map, EdgeExp.Set.add rhs_pvar_exp norm_set
                )
              )
              | EdgeExp.Var _ | EdgeExp.Const Const.Cint _-> (
                DC.Map.add_dc norm (DC.make_rhs x_rhs) dc_map, EdgeExp.Set.add x_rhs norm_set
              )
              | _ -> L.(die InternalError)"[TODO] currently unsupported assignment expression!"
          )
          | None -> dc_map, norm_set
      )
      | EdgeExp.BinOp (Binop.MinusA _, x, y) -> (
        match x, y with
        | EdgeExp.Var x_pvar, EdgeExp.Var y_pvar -> (
          (* Most common form of norm, obtained from condition of form [x > y] -> norm [x - y] *)
          match get_assignment x_pvar, get_assignment y_pvar with
          | Some x_rhs, Some y_rhs -> (
            let x_not_changed = EdgeExp.equal x x_rhs in
            let y_not_changed = EdgeExp.equal y y_rhs in
            if x_not_changed && y_not_changed then (
              (* assignments [x = x] and [y = y] *)
              DC.Map.add_dc norm (DC.make_rhs norm) dc_map, norm_set
            ) 
            else if x_not_changed then (
              (* assignments [x = x] and [y = expr] *)
              match y_rhs with
              | EdgeExp.BinOp (op, EdgeExp.Var rhs_pvar, EdgeExp.Const Const.Cint increment) -> (
                assert(not (Pvar.equal rhs_pvar x_pvar));
                assert(Pvar.equal rhs_pvar y_pvar);
                match op with
                | Binop.PlusA _ -> (
                  (* norm [x - y], assignment [y = y + const] -> [(x - y) - const] *)
                  let dc_rhs = DC.make_rhs ~const:(IntLit.neg increment) norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | Binop.MinusA _ -> (
                  (* norm [x - y], assignment [y = y - const] -> [(x - y) + const] *)
                  let dc_rhs = DC.make_rhs ~const:increment norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | _ -> (
                  L.(die InternalError)"[TODO] currently unsupported binop operator!"
                )
              )
              | EdgeExp.Var rhs_pvar -> (
                if Pvar.equal rhs_pvar x_pvar then (
                  (* norm [x - y], assignment [y = x], zero interval *)
                  DC.Map.add_dc norm (DC.make_rhs EdgeExp.zero) dc_map, EdgeExp.Set.add EdgeExp.zero norm_set
                ) else (
                  (* norm [x - y], assignment [y = z] -> [x - z] *)
                  let new_norm = EdgeExp.BinOp (Binop.MinusA None, x, y_rhs) in
                  DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
                )
              )
              | EdgeExp.Const (Const.Cint const) when IntLit.iszero const -> (
                (* norm [x - y], assignment [y = 0] -> [x] *)
                DC.Map.add_dc norm (DC.make_rhs x) dc_map, EdgeExp.Set.add x norm_set
              )
              | _ -> L.(die InternalError)"[TODO] currently unsupported assignment expression!"
            ) 
            else if y_not_changed then (
              (* assignments [y = y] and [x = expr] *)
              match x_rhs with
              | EdgeExp.BinOp (op, EdgeExp.Var rhs_pvar, EdgeExp.Const Const.Cint increment) -> (
                assert(not (Pvar.equal rhs_pvar y_pvar));
                assert(Pvar.equal rhs_pvar x_pvar);
                match op with
                | Binop.PlusA _ -> (
                  (* norm [x - y], assignment [x = x + const] -> [(x - y) + const] *)
                  let dc_rhs = DC.make_rhs ~const:increment norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | Binop.MinusA _ -> (
                  (* norm [x - y], assignment [x = x - const] -> [(x - y) - const] *)
                  let dc_rhs = DC.make_rhs ~const:(IntLit.neg increment) norm in
                  DC.Map.add_dc norm dc_rhs dc_map, norm_set
                )
                | _ -> (
                  L.(die InternalError)"[TODO] currently unsupported binop operator!"
                )
              )
              | EdgeExp.Var rhs_pvar -> (
                if Pvar.equal rhs_pvar x_pvar then (
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
                let new_norm = EdgeExp.UnOp (Unop.Neg, y, None) in
                DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
              )
              | _ -> L.(die InternalError)"[TODO] currently unsupported assignment expression!"
            ) 
            else (
              if EdgeExp.equal x_rhs y_rhs then (
                (* norm [x - y], assignments [x = expr] and [y = expr] -> 0 *)  
                DC.Map.add_dc norm (DC.make_rhs EdgeExp.zero) dc_map, EdgeExp.Set.add EdgeExp.zero norm_set
              )
              else (
                (* TODO: [x = e1] && [y = e2] -> [e1 - e2] *)
                match x_rhs, y_rhs with
                | EdgeExp.Const Const.Cint x_const, EdgeExp.Var y_pvar -> (
                  let new_norm = EdgeExp.UnOp (Unop.Neg, y_rhs, None) in
                  if IntLit.iszero x_const then (
                    DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
                  ) else (
                    let dc_rhs = DC.make_rhs ~const:x_const new_norm in
                    DC.Map.add_dc norm dc_rhs dc_map, EdgeExp.Set.add new_norm norm_set
                  )
                )
                | EdgeExp.Var x_pvar, EdgeExp.Const Const.Cint y_const -> (
                  if IntLit.iszero y_const then (
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
        | EdgeExp.BinOp (Binop.PlusA _, EdgeExp.Var x_pvar, EdgeExp.Const Const.Cint const), EdgeExp.Var y_pvar -> (
          (* TODO: rewrite entire derivation code for [x - y] exp as recursive
           * function which will determine if the overall value of a norm
           * increases/decreases. Current approach is hideous. *)
          match get_assignment x_pvar, get_assignment y_pvar with
          | Some x_rhs, Some y_rhs -> (
            let x_changed = not (EdgeExp.equal (EdgeExp.Var x_pvar) x_rhs) in
            let y_changed = not (EdgeExp.equal y y_rhs) in
            if not x_changed && y_changed then (
              match y_rhs with
              | EdgeExp.BinOp (op, EdgeExp.Var rhs_pvar, EdgeExp.Const Const.Cint const) -> (
                assert(Pvar.equal y_pvar rhs_pvar);
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
              | EdgeExp.Var rhs_pvar when Pvar.equal x_pvar rhs_pvar -> (
                let new_norm = EdgeExp.Const (Const.Cint const) in
                DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, EdgeExp.Set.add new_norm norm_set
              )
              | _ -> L.(die InternalError)"[TODO] currently unsupported assignment '%a' !" EdgeExp.pp y_rhs
            ) else (
              DC.Map.add_dc norm (DC.make_rhs norm) dc_map, norm_set
            )
          )
          | _ -> dc_map, norm_set
        )
        | EdgeExp.Const Const.Cint x_const, EdgeExp.Var y_pvar -> (
          (* [x_const - y_pvar] *)
          match get_assignment y_pvar with
          | Some rhs -> (
            if not (EdgeExp.equal y rhs) then (
              match rhs with
              | EdgeExp.BinOp (op, EdgeExp.Var rhs_pvar, EdgeExp.Const Const.Cint const) -> (
                assert(Pvar.equal y_pvar rhs_pvar);
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
        )
        | _ -> L.(die InternalError)"[TODO] currently unsupported type of norm '%a' !" EdgeExp.pp norm
      )
      | EdgeExp.Const Const.Cint _ -> dc_map, norm_set
      | _ -> L.(die InternalError)"[TODO] currently unsupported type of norm '%a' !" EdgeExp.pp norm
      in
      edge.constraints <- dc_map;
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
    match !active_graph_type with
    | LTS -> (
      let label = if edge_data.backedge then label ^ "[backedge]\n" else label in
      let label = EdgeExp.Set.fold (fun condition acc ->
        acc ^ EdgeExp.to_string condition ^ "\n"
      ) edge_data.conditions label
      in
      let label = PvarMap.fold (fun lhs rhs acc -> 
        let str = F.sprintf "%s = %s\n" (Pvar.to_string lhs) (EdgeExp.to_string rhs) in
        acc ^ str
      ) edge_data.assignments label
      in
      let label = CallSiteSet.fold (fun (call, loc) acc -> 
        let str = F.sprintf "%s : %s\n" (EdgeExp.to_string call) (Location.to_string loc) in
        acc ^ str
      ) edge_data.calls label
      in
      [`Label label; `Color 4711]
    )
    | GuardedDCP -> (
      let label = EdgeExp.Set.fold (fun guard acc -> 
        acc ^ EdgeExp.to_string guard ^ " > 0\n"
      ) edge_data.guards label
      in
      let label = DC.Map.fold (fun lhs (norm, const) acc -> 
        acc ^ (DC.to_string (lhs, norm, const) true) ^ "\n"
      ) edge_data.constraints label
      in
      [`Label label; `Color 4711]
    )
    | DCP -> (
      let label = DC.Map.fold (fun lhs (norm, const) acc -> 
        acc ^ (DC.to_string (lhs, norm, const) false) ^ "\n"
      ) edge_data.constraints label
      in
      [`Label label; `Color 4711]
    )
  )
end

module DCPDot = Graph.Graphviz.Dot(DCP)


(* Variable flow graph *)
module VFG = struct
  module Node = struct
    type t = EdgeExp.t * DCP.Node.t [@@deriving compare]
    let hash = Hashtbl.hash
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
    let hash = Hashtbl.hash
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

  let vertex_name : V.t -> string = fun node -> (
    string_of_int (Hashtbl.hash node)
  )
    
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
              | Some reset -> norm_reset 
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

let norm_is_variable norm formals =
  let rec traverse_exp = function
  | EdgeExp.Var pvar when not (Pvar.Set.mem pvar formals) -> true
  | EdgeExp.Const _ -> false
  | EdgeExp.BinOp (_, lexp, rexp) -> (traverse_exp lexp) || (traverse_exp rexp)
  | EdgeExp.UnOp (_, exp, _) -> (traverse_exp exp)
  | _ -> false
  in
  traverse_exp norm