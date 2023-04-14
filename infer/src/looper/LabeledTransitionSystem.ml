(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
open LooperUtils
module L = Logging
module DC = DifferenceConstraint

let debug_log : ('a, Format.formatter, unit) format -> 'a =
 fun fmt -> F.fprintf (List.hd_exn !debug_fmt) fmt


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

  let is_loophead node =
    match node with
    | Prune (kind, _, _) -> (
      match kind with Ik_dowhile | Ik_for | Ik_while -> true | _ -> false )
    | _ ->
        false


  let get_location node =
    match node with
    | Prune (_, loc, _) | Start (_, loc) | Join (loc, _) ->
        loc
    | Exit ->
        Location.dummy


  let to_string loc =
    match loc with
    | Prune (kind, loc, node_id) ->
        F.asprintf "[%s] %a (%a)" (Location.to_string loc) Sil.pp_if_kind kind Procdesc.Node.pp_id
          node_id
    | Start (proc_name, loc) ->
        F.asprintf "[%s] Begin: %a" (Location.to_string loc) Procname.pp proc_name
    | Join (loc, node_id) ->
        F.asprintf "[%s] Join (%a)" (Location.to_string loc) Procdesc.Node.pp_id node_id
    | Exit ->
        F.sprintf "Exit"


  let pp fmt loc = F.fprintf fmt "%s" (to_string loc)

  module Map = Caml.Map.Make (struct
    type nonrec t = t

    let compare = compare
  end)
end

module EdgeData = struct
  type t =
    { backedge: bool
    ; conditions: EdgeExp.Set.t
    ; assignments: (HilExp.access_expression * EdgeExp.ValuePair.t) list
    ; branch_info: (Sil.if_kind * bool * Location.t) option
    ; calls: EdgeExp.CallPair.Set.t }
  [@@deriving compare]

  let equal = [%compare.equal: t]

  (* Required by Graph module interface *)
  let default =
    { backedge= false
    ; conditions= EdgeExp.Set.empty
    ; assignments= []
    ; branch_info= None
    ; calls= EdgeExp.CallPair.Set.empty }


  let set_backedge edge = {edge with backedge= true}

  let add_condition edge cond =
    if EdgeExp.is_zero cond then edge
    else {edge with conditions= EdgeExp.Set.add cond edge.conditions}


  let add_assignment edge lhs rhs =
    ( match rhs with
    | EdgeExp.ValuePair.P (lb, ub) ->
        if EdgeExp.equal lb ub then
          L.die InternalError "Unnecessary EdgeExp.ValuePair.P: " EdgeExp.ValuePair.pp rhs
    | _ ->
        () ) ;
    {edge with assignments= edge.assignments @ [(lhs, rhs)]}


  let add_invariants edge locals =
    let with_invariants =
      AccessPath.BaseMap.fold
        (fun local_base accesses acc ->
          let has_assignment assignments lhs_access =
            List.exists assignments ~f:(fun (access, _) ->
                HilExp.AccessExpression.equal lhs_access access )
          in
          let add_assignment access assignments =
            if has_assignment assignments access then assignments
            else assignments @ [(access, EdgeExp.ValuePair.V (EdgeExp.T.Access access))]
          in
          let local_base_access = HilExp.AccessExpression.base local_base in
          let assignments = add_assignment local_base_access acc in
          AccessExpressionSet.fold add_assignment accesses assignments )
        locals edge.assignments
    in
    {edge with assignments= with_invariants}


  let get_assignment_rhs edge lhs_access =
    let access_opt =
      List.find edge.assignments ~f:(fun (access, _) ->
          HilExp.AccessExpression.equal lhs_access access )
    in
    match access_opt with
    | Some access ->
        snd access
    | None ->
        EdgeExp.ValuePair.V (EdgeExp.T.Access lhs_access)


  let derive_guards edge norms tenv prover_data =
    let cond_expressions =
      EdgeExp.Set.fold
        (fun cond acc ->
          match cond with
          | EdgeExp.T.BinOp (_, EdgeExp.T.Const _, EdgeExp.T.Const _) ->
              acc
          | EdgeExp.T.BinOp _ ->
              let cond_why3, type_conditions = EdgeExp.to_why3_expr cond tenv prover_data in
              Why3.Term.Sterm.add cond_why3 (Why3.Term.Sterm.union type_conditions acc)
          | _ ->
              L.(die InternalError)
                "[Guards] Condition of form '%a' is not supported" EdgeExp.pp cond )
        edge.conditions Why3.Term.Sterm.empty
    in
    if Why3.Term.Sterm.is_empty cond_expressions then EdgeExp.Set.empty
    else
      let lhs = Why3.Term.Sterm.elements cond_expressions |> Why3.Term.t_and_l in
      let zero_const = Why3.Term.t_real_const (Why3.BigInt.of_int 0) in
      let gt_symbol = Why3.Theory.ns_find_ls prover_data.theory.th_export ["infix >"] in
      let goal_symbol = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh "is_guard") in
      let lhs_vars = Why3.Term.Mvs.keys (Why3.Term.t_vars lhs) in
      let guards =
        EdgeExp.Set.fold
          (fun norm acc ->
            let solve_formula rhs =
              let rhs = Why3.Term.t_app_infer gt_symbol [rhs; zero_const] in
              let formula = Why3.Term.t_implies lhs rhs in
              let rhs_vars = Why3.Term.Mvs.keys (Why3.Term.t_vars rhs) in
              let free_vars = lhs_vars @ rhs_vars in
              let quantified_fmla = Why3.Term.t_forall_close free_vars [] formula in
              let task = Why3.Task.use_export None prover_data.theory in
              let task = Why3.Task.add_prop_decl task Why3.Decl.Pgoal goal_symbol quantified_fmla in
              let prover_call =
                Why3.Driver.prove_task prover_data.driver task ~config:prover_data.main
                  ~command:prover_data.prover_conf.command
                  ~limit:{Why3.Call_provers.empty_limit with limit_time= 5.}
              in
              let result = Why3.Call_provers.wait_on_call prover_call in
              match result.pr_answer with
              | Why3.Call_provers.Valid ->
                  (* Implication [conditions] => [norm > 0] always holds *)
                  EdgeExp.Set.add norm acc
              | Why3.Call_provers.Invalid | Why3.Call_provers.Unknown _ ->
                  acc
              | _ ->
                  debug_log "Failed task: %a\n" Why3.Pretty.print_task task ;
                  debug_log "Fail: %s\n" result.pr_output ;
                  assert false
            in
            if EdgeExp.is_const norm then acc
            else
              let rhs_expr = EdgeExp.to_why3_expr norm tenv prover_data |> fst in
              solve_formula rhs_expr )
          norms EdgeExp.Set.empty
      in
      guards


  let derive_constraint edge_data norm used_assignments formals tenv =
    let get_assignment lhs_access =
      let assignment_opt =
        List.find edge_data.assignments ~f:(fun (access, _) ->
            HilExp.AccessExpression.equal lhs_access access )
      in
      match assignment_opt with
      | Some assignment ->
          Some (snd assignment)
      | None ->
          let lhs_access_base = HilExp.AccessExpression.get_base lhs_access in
          if AccessPath.BaseSet.mem lhs_access_base formals then
            Some (EdgeExp.ValuePair.V (EdgeExp.T.Access lhs_access))
          else None
    in
    let wrap_derived exp_derived_opt ~wrap_func =
      match exp_derived_opt with
      | Some exp_derived -> (
        match exp_derived with
        | EdgeExp.ValuePair.V exp_derived_value ->
            Some (EdgeExp.ValuePair.V (wrap_func exp_derived_value))
        | EdgeExp.ValuePair.P (exp_derived_lb, exp_derived_ub) ->
            if EdgeExp.equal exp_derived_lb exp_derived_ub then
              Some (EdgeExp.ValuePair.V (wrap_func exp_derived_lb))
            else
              let casted_lb = wrap_func exp_derived_lb in
              let casted_ub = wrap_func exp_derived_ub in
              Some (EdgeExp.ValuePair.P (casted_lb, casted_ub)) )
      | None ->
          None
    in
    let rec derive_rhs norm =
      let process_min_max args ~min_max_f =
        (* Derive each argument and collect set of accesses *)
        let accesses, derived_args =
          EdgeExp.Set.fold
            (fun arg (accesses_acc, args_acc) ->
              let accesses, derived_arg = derive_rhs arg in
              (AccessExpressionSet.union accesses_acc accesses, args_acc @ [derived_arg]) )
            args (AccessExpressionSet.empty, [])
        in
        (* Return derived min/max expression only if all variables
           * of all arguments are defined at this LTS location *)
        if List.exists derived_args ~f:Option.is_none then (AccessExpressionSet.empty, None)
        else
          (* Arguments might contain intervals. Derive two sets for
           * lower and upper bounds and propagate the Interval to
           * the root of the expression *)
          let lb_set, ub_set =
            List.fold derived_args
              ~f:(fun (lb_set, ub_set) arg_opt ->
                match Option.value_exn arg_opt with
                | EdgeExp.ValuePair.V arg ->
                    (EdgeExp.Set.add arg lb_set, EdgeExp.Set.add arg ub_set)
                | EdgeExp.ValuePair.P (lb, ub) ->
                    (EdgeExp.Set.add lb lb_set, EdgeExp.Set.add ub ub_set) )
              ~init:(EdgeExp.Set.empty, EdgeExp.Set.empty)
          in
          let rhs =
            if EdgeExp.Set.equal lb_set ub_set then Some (EdgeExp.ValuePair.V (min_max_f lb_set))
            else Some (EdgeExp.ValuePair.P (min_max_f lb_set, min_max_f ub_set))
          in
          (accesses, rhs)
      in
      match norm with
      | EdgeExp.T.Access access -> (
        match get_assignment access with
        | Some rhs -> (
            let process_value_rhs rhs =
              let rhs_exp, _ = EdgeExp.separate rhs in
              if
                (not (EdgeExp.equal norm rhs_exp))
                && AccessExpressionSet.mem access used_assignments
              then (
                (* debug_log "############ FAIL ###########@,"; *)
                (* L.die InternalError "Edge '%a = %a' assignment previously used "
                   HilExp.AccessExpression.pp access
                   EdgeExp.pp rhs *)
                L.user_warning
                  "Edge '%a = %a' assignment previously used, skipping substitution...@."
                  HilExp.AccessExpression.pp access EdgeExp.pp rhs ;
                (AccessExpressionSet.empty, Some norm) )
              else
                let accesses =
                  if (not (EdgeExp.equal norm rhs)) && not (EdgeExp.is_zero rhs) then
                    AccessExpressionSet.singleton access
                  else AccessExpressionSet.empty
                in
                (accesses, Some rhs)
            in
            match rhs with
            | EdgeExp.ValuePair.P (lower_bound, upper_bound) -> (
                let lb_accesses, lb_rhs_opt = process_value_rhs lower_bound in
                let ub_accesses, ub_rhs_opt = process_value_rhs upper_bound in
                match (lb_rhs_opt, ub_rhs_opt) with
                | Some lb_rhs, Some ub_rhs ->
                    ( AccessExpressionSet.union lb_accesses ub_accesses
                    , Some (EdgeExp.ValuePair.P (lb_rhs, ub_rhs)) )
                | _ ->
                    (AccessExpressionSet.empty, None) )
            | EdgeExp.ValuePair.V value_rhs -> (
                let accesses, rhs_opt = process_value_rhs value_rhs in
                match rhs_opt with
                | Some rhs ->
                    (accesses, Some (EdgeExp.ValuePair.V rhs))
                | None ->
                    (accesses, None) ) )
        | None ->
            (AccessExpressionSet.empty, None) )
      | EdgeExp.T.Const (Const.Cint _) ->
          (AccessExpressionSet.empty, Some (EdgeExp.ValuePair.V norm))
      | EdgeExp.T.BinOp (op, lexp, rexp) -> (
          let process_value_binop op lexp rexp =
            match op with
            | Binop.Shiftrt -> (
              match (EdgeExp.is_zero lexp, EdgeExp.is_zero rexp) with
              | true, true | true, false ->
                  EdgeExp.zero
              | false, true ->
                  lexp
              | false, false ->
                  EdgeExp.T.BinOp (op, lexp, rexp) )
            | _ ->
                EdgeExp.T.BinOp (op, lexp, rexp)
          in
          let lexp_accesses, lexp_derived_opt = derive_rhs lexp in
          let rexp_accesses, rexp_derived_opt = derive_rhs rexp in
          match (lexp_derived_opt, rexp_derived_opt) with
          | Some lexp_derived, Some rexp_derived -> (
            match (lexp_derived, rexp_derived) with
            | EdgeExp.ValuePair.P (lexp_lb, lexp_ub), EdgeExp.ValuePair.P (rexp_lb, rexp_ub) ->
                let lb = process_value_binop op lexp_lb rexp_lb in
                let ub = process_value_binop op lexp_ub rexp_ub in
                ( AccessExpressionSet.union lexp_accesses rexp_accesses
                , Some (EdgeExp.ValuePair.P (lb, ub)) )
            | EdgeExp.ValuePair.V lexp_value, EdgeExp.ValuePair.P (rexp_lb, rexp_ub) ->
                let lb = process_value_binop op lexp_value rexp_lb in
                let ub = process_value_binop op lexp_value rexp_ub in
                ( AccessExpressionSet.union lexp_accesses rexp_accesses
                , Some (EdgeExp.ValuePair.P (lb, ub)) )
            | EdgeExp.ValuePair.P (lexp_lb, lexp_ub), EdgeExp.ValuePair.V rexp_value ->
                let lb = process_value_binop op lexp_lb rexp_value in
                let ub = process_value_binop op lexp_ub rexp_value in
                ( AccessExpressionSet.union lexp_accesses rexp_accesses
                , Some (EdgeExp.ValuePair.P (lb, ub)) )
            | EdgeExp.ValuePair.V lexp_value, EdgeExp.ValuePair.V rexp_value ->
                ( AccessExpressionSet.union lexp_accesses rexp_accesses
                , Some (EdgeExp.ValuePair.V (process_value_binop op lexp_value rexp_value)) ) )
          | _ ->
              (* Some expression variable is not defined on this edge *)
              (AccessExpressionSet.empty, None) )
      | EdgeExp.T.Cast (typ, exp) ->
          let cast_derived_value exp =
            if EdgeExp.is_zero exp then exp else EdgeExp.T.Cast (typ, exp)
          in
          let accesses, exp_derived_opt = derive_rhs exp in
          (accesses, wrap_derived exp_derived_opt ~wrap_func:cast_derived_value)
      | EdgeExp.T.UnOp (Unop.Neg, exp, typ) ->
          let negate_derived_value exp =
            if EdgeExp.is_zero exp then exp else EdgeExp.T.UnOp (Unop.Neg, exp, typ)
          in
          let accesses, exp_derived_opt = derive_rhs exp in
          (accesses, wrap_derived exp_derived_opt ~wrap_func:negate_derived_value)
      | EdgeExp.T.UnOp _ ->
          assert false
      | EdgeExp.T.Max args ->
          process_min_max args ~min_max_f:(fun x -> EdgeExp.T.Max x)
      | EdgeExp.T.Min args ->
          process_min_max args ~min_max_f:(fun x -> EdgeExp.T.Min x)
      | _ ->
          (AccessExpressionSet.empty, Some (EdgeExp.ValuePair.V norm))
    in
    (* Separate assignment_rhs.Value into norm and constant part and create
     * DC.rhs.Value out of it. Do additional processing and simplify, try to
     * derive new norm if possible *)
    let process_assignment_rhs_value rhs_value =
      (* Separate and simplify the rhs expression and get
       * "cannnonical" form which might be equal to the lhs
       * norm in which case we dont create a new norm *)
      let rhs_terms, rhs_const_opt = EdgeExp.split_exp_new rhs_value in
      let rhs_norm_terms = List.map rhs_terms ~f:EdgeExp.multiply_term_by_frac in
      let rhs_norm = EdgeExp.merge_exp_list rhs_norm_terms in
      debug_log "[Expression] %a@," EdgeExp.pp rhs_norm ;
      if Option.is_some rhs_const_opt then
        debug_log "[Expression const] %a@," DifferenceConstraint.pp_const_part
          (Option.value_exn rhs_const_opt) ;
      let rhs_simplified = EdgeExp.merge rhs_norm rhs_const_opt in
      if EdgeExp.equal norm rhs_value || EdgeExp.equal norm rhs_simplified then
        (DC.make_value_rhs norm, EdgeExp.Set.empty)
      else
        (* Derived RHS expression is not equal to the original norm *)
        let lhs_norm, lhs_const_opt = EdgeExp.separate norm in
        let rhs_norm, rhs_const_opt =
          if EdgeExp.is_zero rhs_norm then
            match rhs_const_opt with
            | Some (rhs_op, rhs_const) ->
                (* non-const part is zero, make the const part the norm *)
                let const_lit =
                  match rhs_op with
                  | Binop.PlusA _ ->
                      rhs_const
                  | Binop.MinusA _ ->
                      IntLit.neg rhs_const
                  | _ ->
                      assert false
                in
                (EdgeExp.T.Const (Const.Cint const_lit), None)
            | None ->
                ((* 0 + None *)
                 EdgeExp.zero, None)
          else (rhs_norm, rhs_const_opt)
        in
        if EdgeExp.equal lhs_norm rhs_norm then
          let value_rhs =
            match (lhs_const_opt, rhs_const_opt) with
            | Some (lhs_op, lhs_const), Some (rhs_op, rhs_const) -> (
                assert (Binop.equal lhs_op rhs_op) ;
                match lhs_op with
                | Binop.PlusA _ ->
                    let diff = IntLit.sub rhs_const lhs_const in
                    DC.make_value_rhs ~const_part:(lhs_op, diff) norm
                | Binop.MinusA typ_opt ->
                    (* [lhs_norm] (-) lhs_const, [rhs_norm] (-) rhs_const --->  +(-(rhs_const - lhs_const)) *)
                    let diff = IntLit.neg (IntLit.sub rhs_const lhs_const) in
                    DC.make_value_rhs ~const_part:(Binop.PlusA typ_opt, diff) norm
                | Binop.Shiftrt ->
                    let diff = IntLit.sub rhs_const lhs_const in
                    DC.make_value_rhs ~const_part:(lhs_op, diff) norm
                | _ ->
                    assert false )
            | None, Some (rhs_op, rhs_const) -> (
              match rhs_op with
              | Binop.PlusA _ ->
                  DC.make_value_rhs ~const_part:(rhs_op, rhs_const) norm
              | Binop.MinusA typ_opt ->
                  DC.make_value_rhs ~const_part:(Binop.PlusA typ_opt, IntLit.neg rhs_const) norm
              | Binop.Shiftrt ->
                  DC.make_value_rhs ~const_part:(rhs_op, rhs_const) norm
              | _ ->
                  debug_log "%a' <= %a %a %a\n" EdgeExp.pp lhs_norm EdgeExp.pp rhs_norm Binop.pp
                    rhs_op IntLit.pp rhs_const ;
                  assert false )
            | _ ->
                assert false
          in
          (value_rhs, EdgeExp.Set.empty)
        else
          (* TODO: this is incorrect. If we return rhs_norm which is different from  *)
          let value_rhs =
            match rhs_const_opt with
            | Some (rhs_op, rhs_const) ->
                if EdgeExp.is_variable rhs_norm formals tenv then
                  match rhs_op with
                  | Binop.PlusA _ ->
                      DC.make_value_rhs ~const_part:(rhs_op, rhs_const) rhs_norm
                  | Binop.MinusA typ_opt ->
                      DC.make_value_rhs
                        ~const_part:(Binop.PlusA typ_opt, IntLit.neg rhs_const)
                        rhs_norm
                  | Binop.Shiftrt ->
                      (* TODO *)
                      (* debug_log "Merged: %a\n" EdgeExp.pp rhs_simplified; *)
                      DC.make_value_rhs ~const_part:(rhs_op, rhs_const) rhs_norm
                  | Binop.Mult _ ->
                      DC.make_value_rhs rhs_simplified
                  | _ ->
                      L.die InternalError "lhs_norm: %a, rhs_norm: %a, rhs_op: %a, rhs_const: %a"
                        EdgeExp.pp lhs_norm EdgeExp.pp rhs_norm Binop.pp rhs_op IntLit.pp rhs_const
                else DC.make_value_rhs rhs_simplified
            | None ->
                DC.make_value_rhs rhs_norm
          in
          (value_rhs, EdgeExp.Set.singleton rhs_norm)
    in
    let substituted_accesses, derived_rhs_opt = derive_rhs norm in
    match derived_rhs_opt with
    | Some derived_rhs -> (
      match derived_rhs with
      | EdgeExp.ValuePair.V derived_rhs_value ->
          let dc_rhs, norm_set = process_assignment_rhs_value derived_rhs_value in
          (substituted_accesses, Some (DC.Value dc_rhs), norm_set)
      | EdgeExp.ValuePair.P (lb, ub) ->
          let lb_dc_rhs, lb_norm_set = process_assignment_rhs_value lb in
          let ub_dc_rhs, ub_norm_set = process_assignment_rhs_value ub in
          ( substituted_accesses
          , Some (DC.Pair (lb_dc_rhs, ub_dc_rhs))
          , EdgeExp.Set.union lb_norm_set ub_norm_set ) )
    | None ->
        (AccessExpressionSet.empty, None, EdgeExp.Set.empty)
end

include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Node) (EdgeData)
module NodeSet = Caml.Set.Make (V)
module EdgeSet = Caml.Set.Make (E)
module EdgeMap = Caml.Map.Make (E)
include DefaultDot

let pp_element fmt (kind, branch, loc) =
  F.fprintf fmt "%a[%s](%B)" Sil.pp_if_kind kind (Location.to_string loc) branch


let edge_label : EdgeData.t -> string =
 fun edge_data ->
  match edge_data.branch_info with
  | Some prune_info ->
      F.asprintf "%a\n" pp_element prune_info
  | None ->
      ""


let vertex_attributes node = [`Shape `Box; `Label (Node.to_string node)]

let vertex_name vertex = string_of_int (Node.hash vertex)

let edge_attributes : E.t -> 'a list =
 fun (_, edge_data, _) ->
  let label = edge_label edge_data in
  let label = if edge_data.backedge then label ^ "[backedge]\n" else label in
  let call_list =
    List.map (EdgeExp.CallPair.Set.elements edge_data.calls) ~f:(fun call_assignment ->
        match call_assignment with
        | EdgeExp.CallPair.V ((_, _, _, loc) as call) ->
            F.asprintf "%s : %a" (EdgeExp.call_to_string call) Location.pp loc
        | EdgeExp.CallPair.P (((_, _, _, loc1) as lb_call), ub_call) ->
            F.asprintf "[%s; %s] : %a" (EdgeExp.call_to_string lb_call)
              (EdgeExp.call_to_string ub_call) Location.pp loc1
        | _ ->
            assert false )
  in
  let calls_str = String.concat ~sep:"\n" call_list in
  let conditions =
    List.map (EdgeExp.Set.elements edge_data.conditions) ~f:(fun cond -> EdgeExp.to_string cond)
  in
  let assignments =
    List.map edge_data.assignments ~f:(fun (lhs, rhs) ->
        F.asprintf "%a = %s" HilExp.AccessExpression.pp lhs (EdgeExp.ValuePair.to_string rhs) )
  in
  let label =
    F.asprintf "%s\n%s\n%s\n%s" label
      (String.concat ~sep:"\n" conditions)
      (String.concat ~sep:"\n" assignments)
      calls_str
  in
  (* Perform replacement to escape all harmful characters which corrupt dot file *)
  (* Remove newlines from string arguments of function calls and such to make it more readable *)
  let label =
    String.substr_replace_all label ~pattern:"\"" ~with_:"\\\""
    |> String.substr_replace_all ~pattern:"\\n" ~with_:""
  in
  [`Label label; `Color 4711]
