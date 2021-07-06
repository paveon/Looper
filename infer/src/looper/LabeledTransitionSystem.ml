(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
open LooperUtils
module L = Logging
module DC = DifferenceConstraint


let debug_log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.fprintf (List.hd_exn !debug_fmt) fmt


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

  let is_loophead node = match node with
    | Prune (kind, _, _) -> (
      match kind with
      | Ik_dowhile | Ik_for | Ik_while -> true
      | _ -> false
      )
    | _ -> false

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
    branch_info: (Sil.if_kind * bool * Location.t) option;
    calls: EdgeExp.Set.t;
  }
  [@@deriving compare]

  let equal = [%compare.equal: t]

  (* Required by Graph module interface *)
  let default = {
    backedge = false;
    conditions = EdgeExp.Set.empty;
    assignments = AccessPathMap.empty;
    branch_info = None;
    calls = EdgeExp.Set.empty;
  }

  let set_backedge edge = { edge with backedge = true }

  let add_condition edge cond = if EdgeExp.is_zero cond then edge
    else { edge with conditions = EdgeExp.Set.add cond edge.conditions }

  let add_assignment edge lhs rhs = { edge with 
      assignments = AccessPathMap.add lhs rhs edge.assignments;
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


  let derive_guards edge norms tenv prover_data =
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
    if Why3.Term.Sterm.is_empty cond_expressions then EdgeExp.Set.empty
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

      guards
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


    let substituted_accesses, derived_rhs_opt = derive_rhs norm in
    match derived_rhs_opt with
    | Some derived_rhs -> (
      if EdgeExp.equal derived_rhs norm then AccessSet.empty, Some (DC.make_rhs norm), None
      else (
        let rhs_norm, rhs_const_opt = EdgeExp.separate derived_rhs in
        let merged = EdgeExp.merge rhs_norm rhs_const_opt in

        if EdgeExp.equal merged norm then AccessSet.empty, Some (DC.make_rhs norm), None
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

            AccessSet.empty, Some dc_rhs, None
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
            substituted_accesses, Some dc_rhs, Some rhs_norm
          )
        )
      )
    )
    | None -> AccessSet.empty, None, None
end


include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(EdgeData)
module NodeSet = Caml.Set.Make(V)
module EdgeSet = Caml.Set.Make(E)
module EdgeMap = Caml.Map.Make(E)

include DefaultDot


let pp_element fmt (kind, branch, loc) = 
  let kind = Sil.if_kind_to_string kind in
  F.fprintf fmt "%s[%s](%B)" kind (Location.to_string loc) branch

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
  let conditions = List.map (EdgeExp.Set.elements edge_data.conditions) ~f:(fun cond -> EdgeExp.to_string cond) in
  let assignments = List.map (AccessPathMap.bindings edge_data.assignments) ~f:(fun (lhs, rhs) ->
    F.asprintf "%a = %s" AccessPath.pp lhs (EdgeExp.to_string rhs)
  )
  in
  let label = F.asprintf "%s\n%s\n%s\n%s" label (String.concat ~sep:"\n" conditions) 
    (String.concat ~sep:"\n" assignments) calls_str 
  in
  [`Label label; `Color 4711]
)