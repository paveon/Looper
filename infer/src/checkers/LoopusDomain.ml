open! IStd
module F = Format
module L = Logging


module LocSet = Caml.Set.Make(Location)

module PvarSet = struct
  include Caml.Set.Make(Pvar)

  let pp fmt set =
    iter (fun pvar ->
      F.fprintf fmt " %s " (Pvar.to_string pvar)
    ) set

  let to_string set =
    let tmp = fold (fun pvar acc ->
      acc ^ Pvar.to_string pvar ^ " "
    ) set ""
    in
    "[" ^ (String.rstrip tmp) ^ "]"
end


module PvarMap = struct
  include Caml.Map.Make(Pvar)

  let pp fmt set =
    iter (fun pvar _ ->
      F.fprintf fmt " %s " (Pvar.to_string pvar)
    ) set

  let to_string set =
    let tmp = fold (fun pvar _ acc ->
      acc ^ Pvar.to_string pvar ^ " "
    ) set ""
    in
    "[" ^ (String.rstrip tmp) ^ "]"
end


let rec exp_to_str ?(braces = false) exp = match exp with
  | Exp.BinOp (op, lexp, rexp) -> (
    let lexp = exp_to_str ~braces lexp in
    let rexp = exp_to_str ~braces rexp in
    let op = Binop.str Pp.text op in
    if braces then (
      F.sprintf "(%s %s %s)" lexp op rexp
    ) else (
      F.sprintf "%s %s %s" lexp op rexp
    )
    
  )
  | Exp.Lvar _ -> String.slice (Exp.to_string exp) 1 0
  | _ -> Exp.to_string exp


(* Difference Constraint of form "x <= y + c"
 * Example: "(len - i) <= (len - i) + 1" *)
module DC = struct
  type t = (Exp.t * Exp.t * IntLit.t)
  [@@deriving compare]

  type dc = t
  type rhs = (Exp.t * IntLit.t)
  [@@deriving compare]

  let make ?(const = IntLit.zero) lhs rhs_norm = (lhs, rhs_norm, const)

  let make_rhs ?(const = IntLit.zero) (rhs_norm: Exp.t) = (rhs_norm, const)

  let is_constant : t -> bool = fun (lhs, rhs, const) -> Exp.equal lhs rhs && IntLit.iszero const

  let same_norms : t -> bool = fun (lhs, rhs, _) -> Exp.equal lhs rhs

  let is_decreasing : t -> bool = fun (_, _, const) -> IntLit.isnegative const

  let is_increasing : t -> bool = fun (_, _, const) ->
    not (IntLit.isnegative const) && not (IntLit.iszero const)

  let to_string : t -> bool -> string = fun (lhs, rhs_norm, rhs_const) guarded ->
    let dc = if guarded then (
      F.asprintf "%s' <= %s" (exp_to_str lhs ~braces:true) (exp_to_str rhs_norm ~braces:true)
    ) else (
      F.asprintf "[%s]' <= [%s]" (exp_to_str lhs) (exp_to_str rhs_norm)
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
    include Caml.Map.Make (struct 
      type nonrec t = Exp.t
      let compare = Exp.compare
    end)

    let get_dc : Exp.t -> rhs t -> dc option = fun key map ->
      match find_opt key map with
      | Some (rhs_norm, const) -> Some (key, rhs_norm, const)
      | None -> None

    let add_dc : Exp.t -> rhs -> rhs t -> rhs t = fun dc_lhs dc_rhs map -> (
      let rhs_norm, rhs_const = dc_rhs in
      if Exp.equal dc_lhs rhs_norm && IntLit.iszero rhs_const then (
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
    )
  end
end


type prune_info = (Sil.if_kind * bool * Location.t)
[@@deriving compare]

let prune_info_equal = [%compare.equal: prune_info]

let equal_paths path_a path_b = List.equal path_a path_b ~equal:prune_info_equal


let pp_prune_info fmt (kind, branch, loc) = 
  let kind = Sil.if_kind_to_string kind in
  F.fprintf fmt "%s[%s](%B)" kind (Location.to_string loc) branch

let rec exp_to_z3_expr smt_ctx exp = 
  let int_sort = Z3.Arithmetic.Integer.mk_sort smt_ctx in
  match exp with
  | Exp.Const (Const.Cint const) -> (
    let const_value = IntLit.to_int_exn const in
    Z3.Arithmetic.Integer.mk_numeral_i smt_ctx const_value
  )
  | Exp.Lvar pvar -> Z3.Expr.mk_const_s smt_ctx (Pvar.to_string pvar) int_sort
  | Exp.BinOp (op, lexp, rexp) -> (
    let lexp = exp_to_z3_expr smt_ctx lexp in
    let rexp = exp_to_z3_expr smt_ctx rexp in
    match op with
    | Binop.MinusA _ -> Z3.Arithmetic.mk_sub smt_ctx [lexp; rexp]
    | Binop.PlusA _ -> Z3.Arithmetic.mk_add smt_ctx [lexp; rexp]
    | Binop.Mult _ -> Z3.Arithmetic.mk_mul smt_ctx [lexp; rexp]
    | _ -> L.(die InternalError)"[Z3 expr] Expression contains invalid binary operator!"
  )
  | _ -> L.(die InternalError)"[Z3 expr] Expression contains invalid element!"


module Bound = struct
  type t =
  | BinOp of Binop.t * t * t
  | Value of Exp.t
  | Max of t list
  | Min of t list
  [@@deriving compare]

  let rec to_string bound = match bound with
  | BinOp (op, lhs, rhs) -> (
    match op with
    | Binop.Mult _ -> (
      let aux str exp = match exp with
      | Max _ | Value _ -> str
      | _ -> F.sprintf "(%s)" str
      in
      let lhs_str = aux (to_string lhs) lhs in
      let rhs_str = aux (to_string rhs) rhs in
      F.sprintf "%s %s %s" lhs_str (Binop.(str Pp.text) op) rhs_str
    )
    | _ -> F.sprintf "%s %s %s" (to_string lhs) (Binop.(str Pp.text) op) (to_string rhs)
  )
  | Value exp -> Exp.to_string exp
  | Max args -> if Int.equal (List.length args) 1 then (
    let arg = List.hd_exn args in
    let str = to_string arg in
    match arg with 
    | Value arg -> (match arg with
      | Exp.Lvar _ -> F.sprintf "[%s]" str
      | _ -> F.sprintf "max(%s, 0)" str
    )
    | _ -> F.sprintf "max(%s, 0)" str
  ) else (
    if List.is_empty args then (
      "max()"
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

  let pp fmt bound = F.fprintf fmt "%s" (to_string bound)

  let is_zero bound = match bound with
  | Value exp -> Exp.is_zero exp
  | _ -> false

  let is_one bound = match bound with
  | Value (Exp.Const (Const.Cint const)) -> IntLit.isone const
  | _ -> false

  (* let to_z3_expr bound smt_ctx = 
    let int_sort = Z3.Arithmetic.Integer.mk_sort smt_ctx in
    let zero_const = Z3.Arithmetic.Integer.mk_numeral_i smt_ctx 0 in
    let rec aux bound = match bound with
    | BinOp (op, lexp, rexp) -> (
      let lexp = aux lexp in
      let rexp = aux rexp in
      match op with
      | Binop.MinusA -> Z3.Arithmetic.mk_sub smt_ctx [lexp; rexp]
      | Binop.PlusA -> Z3.Arithmetic.mk_add smt_ctx [lexp; rexp]
      | Binop.Mult -> Z3.Arithmetic.mk_mul smt_ctx [lexp; rexp]
      | _ -> L.(die InternalError)"[Z3 expr] Expression contains invalid binary operator!"
    )
    | Value exp -> exp_to_z3_expr smt_ctx exp
    | Max args -> (
      let types, z3_args = List.fold args ~init:([], []) ~f:(fun (types, z3_args) arg -> 
        types @ [int_sort], z3_args @ [aux arg]
      ) 
      in
      let max_func = Z3.FuncDecl.mk_func_decl_s smt_ctx "max" types int_sort in
      if List.length args < 2 then (
        Z3.Expr.mk_app smt_ctx max_func (z3_args @ [zero_const])
      ) else (
        Z3.Expr.mk_app smt_ctx max_func z3_args
      )
    )
    in
    aux bound *)
end


(* Difference Constraint Program *)
module DCP = struct
  module Node = struct
    type t = 
      | Prune of (Sil.if_kind * Location.t)
      | Start of Location.t
      | Join of (t * t)
      | Exit
      | Dummy
    [@@deriving compare]

    let equal = [%compare.equal: t]
    let hash = Hashtbl.hash

    let is_join : t -> bool = function Join _ -> true | _ -> false

    let rec to_string loc = match loc with
      | Prune (kind, loc) -> F.sprintf "%s [%s]" (Sil.if_kind_to_string kind) (Location.to_string loc)
      | Start loc -> F.sprintf "Begin [%s]" (Location.to_string loc)
      | Join (lhs, rhs) -> F.sprintf "Join(%s, %s)" (to_string lhs) (to_string rhs)
      | Exit -> F.sprintf "Exit"
      | Dummy -> F.sprintf "Dummy"

    let pp fmt loc = F.fprintf fmt "%s" (to_string loc)

    let equal = [%compare.equal: t]

    module Map = Caml.Map.Make(struct
      type nonrec t = t
      let compare = compare
    end)
  end

  module EdgeData = struct
    type t = {
      backedge: bool;
      conditions: Exp.Set.t;
      assignments: Exp.t PvarMap.t;
      mutable constraints: DC.rhs DC.Map.t;
      mutable guards: Exp.Set.t;
      mutable bound_cache: Bound.t option;
      mutable bound_norm: Exp.t option;

      (* Last element of common path prefix *)
      path_prefix_end: prune_info option; 
    }
    [@@deriving compare]

    let equal = [%compare.equal: t]

    let active_guards edge = Exp.Set.fold (fun guard acc ->
      match DC.Map.get_dc guard edge.constraints with
      | Some dc ->
        if DC.is_decreasing dc && DC.same_norms dc then acc
        else Exp.Set.add guard acc
      | _ -> Exp.Set.add guard acc
    ) edge.guards Exp.Set.empty

    let modified_pvars edge = PvarMap.fold (fun pvar exp pvar_set -> 
        if Exp.equal (Exp.Lvar pvar) exp then pvar_set
        else PvarSet.add pvar pvar_set
      ) edge.assignments PvarSet.empty

    module Set = Caml.Set.Make(struct
      type nonrec t = t
      let compare = compare
    end)

    let make : Exp.t PvarMap.t -> prune_info option -> t = fun assignments prefix_end -> {
      backedge = false;
      conditions = Exp.Set.empty;
      assignments = assignments;
      constraints = DC.Map.empty;
      guards = Exp.Set.empty;
      bound_cache = None;
      bound_norm = None;
      path_prefix_end = prefix_end; 
    }

    let empty = make PvarMap.empty None

    (* Required by Graph module interface *)
    let default = empty

    let set_backedge : t -> t = fun edge -> { edge with backedge = true }

    let add_condition : t -> Exp.t -> t = fun edge cond ->
      { edge with conditions = Exp.Set.add cond edge.conditions }

    let add_assignment : t -> Pvar.t -> Exp.t -> t = fun edge lhs rhs ->
      { edge with assignments = PvarMap.add lhs rhs edge.assignments }

    let add_invariants : t -> PvarSet.t -> t = fun edge unmodified ->
      let with_invariants = PvarSet.fold (fun lhs acc ->
        if PvarMap.mem lhs acc then (
          F.printf "[Warning] Assignment map already contains key";
          acc
        ) else (
          PvarMap.add lhs (Exp.Lvar lhs) acc
        )
      ) unmodified edge.assignments
      in
      { edge with assignments = with_invariants }

    let set_path_end : t -> prune_info option -> t = fun edge path_end ->
      { edge with path_prefix_end = path_end }

    let get_assignment_rhs : t -> Pvar.t -> Exp.t = fun edge lhs ->
      match PvarMap.find_opt lhs edge.assignments with
      | Some rhs -> rhs
      | None -> Exp.Lvar lhs

    let derive_guards : t -> Exp.Set.t -> Z3.Solver.solver -> Z3.context -> unit = 
    fun edge norms solver smt_ctx -> (
      let int_sort = Z3.Arithmetic.Integer.mk_sort smt_ctx in
      let cond_expressions = Exp.Set.fold (fun cond acc -> 
        match cond with
        | Exp.BinOp (_, Exp.Const _, Exp.Const _) -> (
          acc
        )
        | Exp.BinOp (op, lexp, rexp) -> (
          let cond_exp_to_z3 exp = match exp with
          | Exp.Lvar pvar -> Z3.Expr.mk_const_s smt_ctx (Pvar.to_string pvar) int_sort
          | Exp.Const (Const.Cint const) -> (
            Z3.Arithmetic.Integer.mk_numeral_i smt_ctx (IntLit.to_int_exn const)          
          )
          | _ -> L.(die InternalError)"[Guards] Condition BINOP subexpression is not supported!"
          in

          let lexp_const = cond_exp_to_z3 lexp in
          let rexp_const = cond_exp_to_z3 rexp in
          match op with
          | Binop.Lt -> List.append [Z3.Arithmetic.mk_lt smt_ctx lexp_const rexp_const] acc
          | Binop.Le -> List.append [Z3.Arithmetic.mk_le smt_ctx lexp_const rexp_const] acc
          | Binop.Gt -> List.append [Z3.Arithmetic.mk_gt smt_ctx lexp_const rexp_const] acc
          | Binop.Ge -> List.append [Z3.Arithmetic.mk_ge smt_ctx lexp_const rexp_const] acc
          | _ -> L.(die InternalError)"[Guards] Condition binop [%a] is not supported!" Exp.pp cond
        )
        | _ -> L.(die InternalError)"[Guards] Condition type is not supported by guard!"
      ) edge.conditions [] 
      in
      if List.is_empty cond_expressions then (
        ()
      ) else (
        let lhs = Z3.Boolean.mk_and smt_ctx cond_expressions in
        let zero_const = Z3.Arithmetic.Integer.mk_numeral_i smt_ctx 0 in
        let guards = Exp.Set.fold (fun norm acc ->         
          let solve_formula rhs =
            let rhs = Z3.Arithmetic.mk_gt smt_ctx rhs zero_const in
            let formula = Z3.Boolean.mk_not smt_ctx (Z3.Boolean.mk_implies smt_ctx lhs rhs) in
            let goal = (Z3.Goal.mk_goal smt_ctx true false false) in
            Z3.Goal.add goal [formula];
            Z3.Solver.reset solver;
            Z3.Solver.add solver (Z3.Goal.get_formulas goal);
            (* F.printf "%s\n" ("Goal: " ^ (Z3.Goal.to_string goal)); *)
            let solve_status = Z3.Solver.check solver [] in
            if phys_equal solve_status Z3.Solver.UNSATISFIABLE then (
              (* F.printf "[STATUS] Not satisfiable\n"; *)
              (* Implication [conditions] => [norm > 0] always holds *)
              Exp.Set.add norm acc
            )
            else (
              (* F.printf "[STATUS] Satisfiable\n"; *)
              acc
            )
          in
          match norm with
          | Exp.BinOp _ | Exp.Lvar _ -> (
            let rhs = exp_to_z3_expr smt_ctx norm in
            solve_formula rhs
          )
          | Exp.Const Const.Cint _ -> acc
          | _ -> (
            L.(die InternalError)"[Guards] Norm expression %a is not supported!" Exp.pp norm
          )

        ) norms Exp.Set.empty
        in
        edge.guards <- guards;
      );
    )
    
    (* Derive difference constraints "x <= y + c" based on edge assignments *)
    let derive_constraints : t -> Exp.t -> Typ.t PvarMap.t -> Exp.Set.t = fun edge norm formals -> (
      let dc_map = edge.constraints in
      let norm_set = Exp.Set.empty in
      let dc_map, norm_set = match norm with
      | Exp.Lvar x_pvar -> (
        (* Norm [x] *)
        if PvarMap.mem x_pvar formals then (
          (* Ignore norms that are formal parameters *)
          dc_map, norm_set
        ) else (
          let x_assignment = match PvarMap.find_opt x_pvar edge.assignments with
          | Some x_rhs -> Some x_rhs
          | None -> if PvarMap.mem x_pvar formals then Some (Exp.Lvar x_pvar) else None
          in
          match x_assignment with
          | Some x_rhs -> (
            if Exp.equal norm x_rhs then (
              (* [x = x], unchanged *)
              DC.Map.add_dc norm (DC.make_rhs norm) dc_map, norm_set
            ) else (
              match x_rhs with
              | Exp.BinOp (op, Exp.Lvar rhs_pvar, Exp.Const Const.Cint increment) -> (
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
                  let rhs_pvar_exp = Exp.Lvar rhs_pvar in
                  let dc_rhs = DC.make_rhs ~const rhs_pvar_exp in
                  DC.Map.add_dc norm dc_rhs dc_map, Exp.Set.add rhs_pvar_exp norm_set
                )
                
              )
              | Exp.Lvar _ | Exp.Const Const.Cint _-> (
                DC.Map.add_dc norm (DC.make_rhs x_rhs) dc_map, Exp.Set.add x_rhs norm_set
              )
              | _ -> L.(die InternalError)"[TODO] currently unsupported assignment expression!"
            )
          )
          | None -> dc_map, norm_set
        )
      )
      | Exp.BinOp (Binop.MinusA _, Exp.Lvar x_pvar, Exp.Lvar y_pvar) -> (
        (* Most common form of norm, obtained from condition of form [x > y] -> norm [x - y] *)
        let lexp_assignment_rhs = match PvarMap.find_opt x_pvar edge.assignments with
        | Some x_rhs -> Some x_rhs
        | None -> if PvarMap.mem x_pvar formals then Some (Exp.Lvar x_pvar) else None
        in
        let rexp_assignment_rhs = match PvarMap.find_opt y_pvar edge.assignments with
        | Some y_rhs -> Some y_rhs
        | None -> if PvarMap.mem y_pvar formals then Some (Exp.Lvar y_pvar) else None
        in

        match lexp_assignment_rhs, rexp_assignment_rhs with
        | Some x_rhs, Some y_rhs -> (
          let norm_lexp = Exp.Lvar x_pvar in
          let norm_rexp = Exp.Lvar y_pvar in

          let x_not_changed = Exp.equal norm_lexp x_rhs in
          let y_not_changed = Exp.equal norm_rexp y_rhs in
          if x_not_changed && y_not_changed then (
            (* assignments [x = x] and [y = y] *)
            DC.Map.add_dc norm (DC.make_rhs norm) dc_map, norm_set
          ) 
          else if x_not_changed then (
            (* assignments [x = x] and [y = expr] *)
            match y_rhs with
            | Exp.BinOp (op, Exp.Lvar rhs_pvar, Exp.Const Const.Cint increment) -> (
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
            | Exp.Lvar rhs_pvar -> (
              if Pvar.equal rhs_pvar x_pvar then (
                (* norm [x - y], assignment [y = x], zero interval *)
                DC.Map.add_dc norm (DC.make_rhs Exp.zero) dc_map, Exp.Set.add Exp.zero norm_set
              ) else (
                (* norm [x - y], assignment [y = z] -> [x - z] *)
                let new_norm = Exp.BinOp (Binop.MinusA None, norm_lexp, y_rhs) in
                DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, Exp.Set.add new_norm norm_set
              )
            )
            | Exp.Const (Const.Cint const) when IntLit.iszero const -> (
              (* norm [x - y], assignment [y = 0] -> [x] *)
              DC.Map.add_dc norm (DC.make_rhs norm_lexp) dc_map, Exp.Set.add norm_lexp norm_set
            )
            | _ -> L.(die InternalError)"[TODO] currently unsupported assignment expression!"
          ) 
          else if y_not_changed then (
            (* assignments [y = y] and [x = expr] *)
            match x_rhs with
            | Exp.BinOp (op, Exp.Lvar rhs_pvar, Exp.Const Const.Cint increment) -> (
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
            | Exp.Lvar rhs_pvar -> (
              if Pvar.equal rhs_pvar x_pvar then (
                (* norm [x - y], assignment [x = y], zero interval *)
                DC.Map.add_dc norm (DC.make_rhs Exp.zero) dc_map, Exp.Set.add Exp.zero norm_set
              ) else (
                (* norm [x - y], assignment [x = z] -> [z - y] *)
                let new_norm = Exp.BinOp (Binop.MinusA None, x_rhs, norm_rexp) in
                DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, Exp.Set.add new_norm norm_set
              )
            )
            | Exp.Const (Const.Cint const) when IntLit.iszero const -> (
              (* norm [x - y], assignment [x = 0] -> [-y] *)
              let new_norm = Exp.UnOp (Unop.Neg, norm_rexp, None) in
              DC.Map.add_dc norm (DC.make_rhs new_norm) dc_map, Exp.Set.add new_norm norm_set
            )
            | _ -> L.(die InternalError)"[TODO] currently unsupported assignment expression!"
          ) 
          else (
            if Exp.equal x_rhs y_rhs then (
              (* norm [x - y], assignments [x = expr] and [y = expr] -> 0 *)  
              DC.Map.add_dc norm (DC.make_rhs Exp.zero) dc_map, Exp.Set.add Exp.zero norm_set
            )
            else (
              (* TODO: [x = e1] && [y = e2] -> [e1 - e2] *)
              L.(die InternalError)"[TODO] currently unsupported assignment expression!"
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
      | Exp.Const Const.Cint _ -> dc_map, norm_set
      | _ -> L.(die InternalError)"[TODO] currently unsupported type of norm '%a' !" Exp.pp norm
      in
      edge.constraints <- dc_map; 
      norm_set
    )
  end

  include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(EdgeData)
  module NodeSet = Caml.Set.Make(V)
  module EdgeSet = Caml.Set.Make(E)
end

module DefaultDot = struct
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let default_vertex_attributes _ = []
  let graph_attributes _ = []
end

module DotConfig = struct
  include DCP
  include DefaultDot
  let edge_label : EdgeData.t -> string = fun edge_data ->
    match edge_data.path_prefix_end with
    | Some prune_info -> F.asprintf "%a\n" pp_prune_info prune_info
    | None -> ""

  let vertex_attributes : Node.t -> 'a list = fun node -> (
    [ `Shape `Box; `Label (Node.to_string node) ]
  )
  let vertex_name : Node.t -> string = fun vertex -> string_of_int (Node.hash vertex)
end

module LTSConfig = struct
  include DotConfig
  let edge_attributes : DCP.E.t -> 'a list = fun (_, edge_data, _) -> (
    let label = (edge_label edge_data) in
    let label = if edge_data.backedge then label ^ "[backedge]\n" else label in
    let label = Exp.Set.fold (fun condition acc ->
      acc ^ exp_to_str condition ^ "\n"
    ) edge_data.conditions label
    in
    let label = PvarMap.fold (fun lhs rhs acc -> 
      let str = F.sprintf "%s = %s\n" (Pvar.to_string lhs) (exp_to_str rhs) in
      acc ^ str
    ) edge_data.assignments label
    in
    [`Label label; `Color 4711]
  )
end

module GuardedDCPConfig = struct
  include DotConfig
  let edge_attributes : DCP.E.t -> 'a list = fun (_, edge_data, _) -> (
    let label = edge_label edge_data in
    let label = Exp.Set.fold (fun guard acc -> 
      acc ^ exp_to_str guard ^ " > 0\n"
    ) edge_data.guards label
    in
    let label = DC.Map.fold (fun lhs (norm, const) acc -> 
      acc ^ (DC.to_string (lhs, norm, const) true) ^ "\n"
    ) edge_data.constraints label
    in
    [`Label label; `Color 4711]
  )
end

module DCPConfig = struct
  include DotConfig
  let edge_attributes : DCP.E.t -> 'a list = fun (_, edge_data, _) -> (
    let label = edge_label edge_data in
    let label = DC.Map.fold (fun lhs (norm, const) acc -> 
      acc ^ (DC.to_string (lhs, norm, const) false) ^ "\n"
    ) edge_data.constraints label
    in
    [`Label label; `Color 4711]
  )
end

module LTSDot = Graph.Graphviz.Dot(LTSConfig)
module GuardedDCPDot = Graph.Graphviz.Dot(GuardedDCPConfig)
module DCPDot = Graph.Graphviz.Dot(DCPConfig)


(* Variable flow graph *)
module VFG = struct
  module Node = struct
    type t = {
      norm: Exp.t;
      dcp_node: DCP.Node.t;
    } [@@deriving compare]
    let hash = Hashtbl.hash
    let equal = [%compare.equal: t]
    let make : Exp.t -> DCP.Node.t -> t = fun norm dcp_node -> { norm; dcp_node }
  end
  
  module Edge = struct
    type t = {
      dcp_edge : DCP.E.t option;
    } [@@deriving compare]
    let hash = Hashtbl.hash
    let equal = [%compare.equal : t]
    let default = { dcp_edge = None }
    end
  include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(Edge)
  include DefaultDot

  let edge_attributes : E.t -> 'a list = fun (_, edge, _) -> [`Label ""; `Color 4711]
  let vertex_attributes : V.t -> 'a list = fun node -> (
    let label = F.asprintf "%a, %a" Exp.pp node.norm DCP.Node.pp node.dcp_node in
    [ `Shape `Box; `Label label ]
  )
  let vertex_name : V.t -> string = fun vertex -> string_of_int (Node.hash vertex)
end

module VFG_Dot = Graph.Graphviz.Dot(VFG)


(* Reset graph *)
module RG = struct 
  module Node = struct
    type t = {
      norm : Exp.t
    } [@@deriving compare]
    let hash = Hashtbl.hash
    let equal = [%compare.equal: t]
    let make : Exp.t -> t = fun norm -> { norm }

    module Set = Caml.Set.Make(struct
      type nonrec t = t
      let compare = compare
    end)
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
    [ `Shape `Box; `Label (Exp.to_string node.norm) ]
  )

  let vertex_name : V.t -> string = fun vertex -> (
    string_of_int (Hashtbl.hash vertex.norm)
  )
    
  let default_vertex_attributes _ = []
  let graph_attributes _ = []

  module Chain = struct
    type t = {
      data : E.t list;
      mutable norms : (Exp.Set.t * Exp.Set.t) option;
    }
    [@@deriving compare]

    let empty = {
      data = [];
      norms = None;
    }

    let origin : t -> Exp.t = fun chain ->
      (E.src (List.hd_exn chain.data)).norm

    let value : t -> IntLit.t = fun chain ->
      List.fold chain.data ~init:IntLit.zero ~f:(fun acc (_, (data : Edge.t), _) -> 
        IntLit.add acc data.const
      )

    let transitions : t -> DCP.EdgeSet.t = fun chain ->
      List.fold chain.data ~init:DCP.EdgeSet.empty ~f:(fun acc (_, (edge_data), _) ->
        DCP.EdgeSet.add (Edge.dcp_edge edge_data) acc
      )

    let norms : t -> graph -> Exp.Set.t * Exp.Set.t = fun chain reset_graph ->
      match chain.norms with
      | Some cache -> cache
      | None -> (
        let _, _, path_end = List.last_exn chain.data in
        let rec find_paths origin visited counter =
          if Node.equal origin path_end then counter + 1 else (
            let next = succ_e reset_graph origin in
            if List.is_empty next then counter else (
              let visited = Node.Set.add origin visited in
              List.fold next ~init:counter ~f:(fun counter (_, _, dst) ->
                if Node.Set.mem dst visited then counter else find_paths dst visited counter
              )
            )
          )
        in
        let norms = List.fold chain.data ~init:(Exp.Set.empty, Exp.Set.empty) 
        ~f:(fun (norms_1, norms_2) (_, _, (dst : Node.t)) ->
          let path_count = find_paths dst Node.Set.empty 0 in
          if path_count < 2 then Exp.Set.add dst.norm norms_1, norms_2
          else norms_1, Exp.Set.add dst.norm norms_2
        )
        in
        chain.norms <- Some norms;
        norms
      )

    let pp fmt chain = List.iter chain.data ~f:(fun ((src : Node.t), _, _) ->
        F.fprintf fmt "%a --> " Exp.pp src.norm
      );
      let _, _, (dst : Node.t) = List.last_exn chain.data in
      F.fprintf fmt "%a" Exp.pp dst.norm

    module Set = Caml.Set.Make(struct
      type nonrec t = t
      let compare = compare
    end)
  end


  (* Finds all reset chains leading to the norm through reset graph *)
  let get_reset_chains origin reset_graph dcp =
    let rec traverse_reset_graph node (chain : Chain.t) =
      let preds = pred_e reset_graph node in
      if List.is_empty preds then (
        Chain.Set.singleton { chain with data = List.rev chain.data; }
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
      let _, edge_data, _ = List.last_exn chain.data in
      let path_origin = match edge_data.dcp_edge with
      | Some (_, _, dcp_dst) -> dcp_dst
      | None -> assert(false)
      in
      (* F.printf "[UNOPTIMIZED CHAIN] %a\n" Chain.pp chain; *)
      let optimize_chain : edge list -> edge -> edge list = 
      fun optimal_chain (src, edge_data, dst) ->
        match edge_data.dcp_edge with
        | Some (path_end, _, _) -> (
          (* F.printf "[PATH END] %a\n" DCP.Node.pp path_end; *)
          (* Find all paths from origin to end and check if they reset the end norm *)
          let current_norm = src.norm in
          let rec checkPaths origin visited_nodes norm_reset acc =
            let open Base.Continue_or_stop in
            if DCP.Node.equal origin path_end then (
              (* Found path, return info if norm was reset along the path *)
              (* F.printf "[PATH FOUND] Reset: %B\n" norm_reset; *)
              Some norm_reset
            ) else (
              let next = DCP.succ_e dcp origin in
              if List.is_empty next then (
                (* Not a path *)
                None
              ) else (
                let visited_nodes = DCP.NodeSet.add origin visited_nodes in
                List.fold_until next ~init:acc ~f:(fun acc (dcp_edge : DCP.E.t) ->
                  let _, dcp_data, dcp_dst = dcp_edge in
                  if DCP.NodeSet.mem dcp_dst visited_nodes then (
                    Continue acc
                  ) else (
                    let norm_reset = if norm_reset then norm_reset else (
                      let dc = DC.Map.get_dc current_norm dcp_data.constraints in
                      match dc with
                      | Some dc -> not (DC.same_norms dc)
                      | None -> norm_reset
                    )
                    in
                    let norm_reset = checkPaths dcp_dst visited_nodes norm_reset acc in
                    match norm_reset with
                    | Some norm_reset -> if norm_reset then (
                      Continue (Some true)
                    ) else Stop (Some false)
                    | None -> Continue acc
                  )
                ) ~finish:(fun acc -> acc)
              )
            )
          in
          let next = (DCP.succ_e dcp path_origin) in
          let all_paths_reset = List.fold_until next ~init:None ~f:(fun acc (dcp_edge : DCP.E.t) ->
            let src, data, dst = dcp_edge in
            if DCP.Node.equal src dst then (
              (* Ignore direct backedge, hotfix for now, have to confirm this *)
              Continue acc
            ) else (
              let dc = DC.Map.get_dc current_norm data.constraints in
              let norm_reset = match dc with
              | Some dc -> not (DC.same_norms dc)
              | None -> false
              in
              let norm_reset = checkPaths dst DCP.NodeSet.empty norm_reset None in
              match norm_reset with
              | Some norm_reset -> if norm_reset then (
                Continue (Some true)
              ) else Stop None
              | None -> Continue acc
            )
          ) ~finish:(fun acc -> acc)
          in
          match all_paths_reset with
          | Some _ -> (
            optimal_chain @ [(src, edge_data, dst)]
          )
          | _ -> (
            F.printf "[NORM NOT RESET] %a\n" Exp.pp current_norm;
            [(src, edge_data, dst)]
          )
        )
        | None -> assert(false)
      in
      let chain_data = List.fold (List.tl_exn chain.data) ~init:[List.hd_exn chain.data] ~f:optimize_chain in
      let chain = { chain with data = chain_data} in
      (* F.printf "[OPTIMIZED CHAIN]   %a\n" Chain.pp chain; *)
      chain
    ) reset_chains
end

module RG_Dot = Graph.Graphviz.Dot(RG)


module AggregateJoin = struct
  type t = {
    rhs: DCP.Node.t;
    lhs: DCP.Node.t;
    edges: DCP.EdgeSet.t;
  } [@@deriving compare]

  let initial : t = {
    lhs = DCP.Node.Dummy;
    rhs = DCP.Node.Dummy;
    edges = DCP.EdgeSet.empty;
  }

  let edge_count : t -> int = fun node -> DCP.EdgeSet.cardinal node.edges

  let add_edge : t -> DCP.E.t -> t = fun info edge -> 
    { info with edges = DCP.EdgeSet.add edge info.edges } 

  let make : DCP.Node.t -> DCP.Node.t -> t = fun rhs lhs ->
    { lhs = lhs; rhs = rhs; edges = DCP.EdgeSet.empty; }
end


type t = {
  last_node: DCP.Node.t;
  branchingPath: prune_info list;

  potential_norms: Exp.Set.t;
  initial_norms: Exp.Set.t;
  locals: PvarSet.t;
  ident_map: Pvar.t Ident.Map.t;
  modified_pvars: PvarSet.t;
  edge_data: DCP.EdgeData.t;
  graph_nodes: DCP.NodeSet.t;
  graph_edges: DCP.EdgeSet.t;
  aggregate_join: AggregateJoin.t;
}

let initial : DCP.Node.t -> t = fun entry_point -> (
  {
    last_node = entry_point;
    branchingPath = [];

    potential_norms = Exp.Set.empty;
    initial_norms = Exp.Set.empty;
    locals = PvarSet.empty;
    ident_map = Ident.Map.empty;
    modified_pvars = PvarSet.empty;
    edge_data = DCP.EdgeData.empty;
    graph_nodes = DCP.NodeSet.add entry_point DCP.NodeSet.empty;
    graph_edges = DCP.EdgeSet.empty;
    aggregate_join = AggregateJoin.initial;
  }
)

let norm_is_variable : Exp.t -> Typ.t PvarMap.t -> bool = fun norm formals ->
  let rec traverse_exp = function
  | Exp.Lvar pvar when not (PvarMap.mem pvar formals) -> true
  | Exp.Const _ -> false
  | Exp.BinOp (_, lexp, rexp) -> (traverse_exp lexp) || (traverse_exp rexp)
  | Exp.UnOp (_, exp, _) -> (traverse_exp exp)
  | _ -> false
  in
  traverse_exp norm

let get_unmodified_pvars : t -> PvarSet.t = fun astate ->
  PvarSet.diff astate.locals astate.modified_pvars

let is_loop_prune : Sil.if_kind -> bool = function
  | Ik_dowhile | Ik_for | Ik_while -> true
  | _ -> false

let pp_path fmt path =
  List.iter path ~f:(fun prune_info ->
    F.fprintf fmt "-> %a " pp_prune_info prune_info
  )

let path_to_string path =
  List.fold path ~init:"" ~f:(fun acc (kind, branch, _) ->
    let kind = Sil.if_kind_to_string kind in
    let part = F.sprintf "-> %s(%B) " kind branch in
    acc ^ part
  )

let get_edge_label path = match List.last path with
  | Some (_, branch, _) -> string_of_bool branch
  | None -> "none"


let ( <= ) ~lhs ~rhs =
  (* F.printf "[Partial order <= ]\n"; *)
  (* F.printf "  [LHS]\n"; *)
  DCP.EdgeSet.equal lhs.graph_edges rhs.graph_edges || 
  DCP.EdgeSet.cardinal lhs.graph_edges < DCP.EdgeSet.cardinal rhs.graph_edges


let join : t -> t -> t = fun lhs rhs ->
  F.printf "\n[JOIN] %a | %a\n" DCP.Node.pp lhs.last_node DCP.Node.pp rhs.last_node;

  (* Creates common path prefix of provided paths *)
  let rec common_path_prefix = fun prefix pathA pathB ->
    match (pathA, pathB) with
    | headA :: tailA, headB :: tailB when Int.equal (compare_prune_info headA headB) 0 -> 
      common_path_prefix (headA :: prefix) tailA tailB
    | _, _ -> prefix
  in

  let lhs_path = lhs.branchingPath in
  let rhs_path = rhs.branchingPath in
  let path_prefix_rev = common_path_prefix [] lhs_path rhs_path in
  let path_prefix = List.rev path_prefix_rev in
  F.printf "  [NEW] Path prefix: %a\n" pp_path path_prefix;

  let join_node = DCP.Node.Join (lhs.last_node, rhs.last_node) in

  let ident_map = Ident.Map.union (fun _ a b ->
    if not (Pvar.equal a b) then 
      L.(die InternalError)"One SIL identificator maps to multiple Pvars!" 
    else Some a
  ) lhs.ident_map rhs.ident_map 
  in
  
  let astate = { lhs with
    branchingPath = path_prefix;
    ident_map = ident_map;
    edge_data = DCP.EdgeData.empty;
    initial_norms = Exp.Set.union lhs.initial_norms rhs.initial_norms;
    locals = PvarSet.inter lhs.locals rhs.locals;
    modified_pvars = PvarSet.empty;
    graph_nodes = DCP.NodeSet.union lhs.graph_nodes rhs.graph_nodes;
    graph_edges = DCP.EdgeSet.union lhs.graph_edges rhs.graph_edges;
  }
  in
  let lhs_empty = DCP.EdgeData.equal lhs.edge_data DCP.EdgeData.empty in
  let rhs_empty = DCP.EdgeData.equal rhs.edge_data DCP.EdgeData.empty in

  let is_consecutive_join = (DCP.Node.is_join lhs.last_node && not (equal_paths path_prefix lhs_path))
   || (DCP.Node.is_join rhs.last_node && not (equal_paths path_prefix rhs_path)) in

  let astate = if is_consecutive_join then (
    F.printf "-----------------------FAIL\n";
    (* Consecutive join, merge join nodes and possibly add new edge to aggregated join node *)
    let other_state, join_state = if DCP.Node.is_join lhs.last_node then rhs, lhs else lhs, rhs in
    let aggregate_join, last_node = match other_state.last_node with
    | DCP.Node.Start _ -> (
      (* Don't add new edge if it's from the beginning location *)
      join_state.aggregate_join, join_state.last_node
    )
    | _ -> (
      if equal_paths path_prefix other_state.branchingPath then (
        (* Heuristic: ignore edge from previous location if this is a "backedge" join which 
         * joins state from inside of the loop with outside state denoted by prune location before loop prune *)
        F.printf "-----------------------BACKEDGE\n";
        join_state.aggregate_join, join_state.last_node
      ) else (
        (* Add edge from non-join node to current set of edges pointing to aggregated join node *)
        F.printf "-----------------------ADD EDGE\n";
        let unmodified = get_unmodified_pvars other_state in
        let edge_data = DCP.EdgeData.add_invariants other_state.edge_data unmodified in
        let edge_data = DCP.EdgeData.set_path_end edge_data (List.last other_state.branchingPath) in
        let lts_edge = DCP.E.create other_state.last_node edge_data join_state.last_node in
        let aggregate_join = AggregateJoin.add_edge join_state.aggregate_join lts_edge in
        aggregate_join, DCP.Node.Join (join_state.last_node, other_state.last_node)
      )
    )
    in
    { astate with 
      edge_data = join_state.edge_data;
      last_node = join_state.last_node;
      aggregate_join = aggregate_join;
      (* last_node = last_node;  *)
    }
  ) else (
    (* First join in a row, create new join node and join info *)
    match lhs.last_node, rhs.last_node with
    | DCP.Node.Prune (kind, _), DCP.Node.Start _ when not (is_loop_prune kind) -> (
      { astate with last_node = lhs.last_node }
    )
    | DCP.Node.Start _, DCP.Node.Prune (kind, _) when not (is_loop_prune kind) -> (
      { astate with last_node = rhs.last_node }
    )
    | _, _ -> (
      let aggregate_join = AggregateJoin.make lhs.last_node rhs.last_node in
      let add_edge aggregate state = 
        if equal_paths path_prefix state.branchingPath then (
          aggregate
        ) else (
          let unmodified = PvarSet.diff astate.locals state.modified_pvars in
          let edge_data = DCP.EdgeData.add_invariants state.edge_data unmodified in
          let edge_data = DCP.EdgeData.set_path_end edge_data (List.last state.branchingPath) in
          let lts_edge = DCP.E.create state.last_node edge_data join_node in
          AggregateJoin.add_edge aggregate lts_edge
        )
      in
      let aggregate_join = add_edge aggregate_join lhs in
      let aggregate_join = add_edge aggregate_join rhs in
      { astate with 
        last_node = join_node; 
        aggregate_join = aggregate_join;
        graph_nodes = DCP.NodeSet.add join_node astate.graph_nodes;
      }
    )
  )
  in
  astate

let widen ~prev ~next ~num_iters:_ = 
  { next with graph_edges = DCP.EdgeSet.union prev.graph_edges next.graph_edges }

let pp fmt astate =
  DCP.EdgeSet.iter (fun (src, edge_data, dst) -> 
    F.fprintf fmt "(%a) -->  (%a) [%a]\n" 
    DCP.Node.pp src
    DCP.Node.pp dst 
    PvarSet.pp (DCP.EdgeData.modified_pvars edge_data)
  ) astate.graph_edges

let pp_summary : F.formatter -> t -> unit =
  fun fmt _astate ->
    F.fprintf fmt "loopus summary placeholder\n";
