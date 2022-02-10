(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)


open! IStd
open LooperUtils

module F = Format
module L = Logging
module LTS = LabeledTransitionSystem


let debug_log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.fprintf (List.hd_exn !debug_fmt) fmt

let console_log : ('a, F.formatter, unit) format -> 'a = fun fmt -> F.printf fmt


type procedure_data = {
  nodes: LTS.NodeSet.t;
  edges: LTS.EdgeSet.t;
  norms: EdgeExp.Set.t;
  formals: AccessPath.BaseSet.t;
  analysis_data: LooperSummary.t InterproceduralAnalysis.t;
  call_summaries: LooperSummary.t Location.Map.t;
  lts: LTS.t
}


type construction_temp_data = {
  last_node: LTS.Node.t;
  loophead_stack: Procdesc.Node.t Stack.t;
  edge_data: LTS.EdgeData.t;
  ident_map: (EdgeExp.value_pair * Typ.t) Ident.Map.t;
  ident_map_2: EdgeExp.value_pair Ident.Map.t;

  node_map: LTS.Node.t Procdesc.NodeMap.t;
  potential_norms: EdgeExp.Set.t;
  loop_heads: Location.t list;
  loop_modified: AccessExpressionSet.t;
  
  scope_locals: AccessExpressionSet.t list;
  (* scope_locals: AccessExpressionSet.t list; *)
  (* locals: AccessExpressionSet.t; *)
  locals: AccessExpressionSet.t AccessPath.BaseMap.t;
  (* locals: AccessPath.BaseSet.t;
  local_accesses: AccessExpressionSet.t; *)

  (* type_map: Typ.t PvarMap.t; *)
  tenv: Tenv.t;
  exe_env: Exe_env.t;
  procname: Procname.t;

  proc_data: procedure_data;
}


let pp_nodekind kind = match kind with
  | Procdesc.Node.Start_node -> "Start_node"
  | Procdesc.Node.Exit_node -> "Exit_node"
  | Procdesc.Node.Stmt_node stmt -> F.asprintf "Stmt_node(%a)" Procdesc.Node.pp_stmt stmt
  | Procdesc.Node.Join_node -> "Join_node"
  | Procdesc.Node.Prune_node (branch, ifkind, _) -> F.asprintf "Prune_node(%B, %a)" branch Sil.pp_if_kind ifkind
  | Procdesc.Node.Skip_node string -> F.asprintf "Skip_node (%s)" string


let is_join_node node = match Procdesc.Node.get_kind node with
  | Procdesc.Node.Join_node -> true
  | _ -> false


let is_exit_node node = match Procdesc.Node.get_kind node with
  | Procdesc.Node.Exit_node -> true
  | _ -> false



let exec_instr : construction_temp_data -> Sil.instr -> construction_temp_data = fun graph_data instr ->
  (* let ap_id_resolver var = match var with
  | Var.LogicalVar id -> (
    match Ident.Map.find id graph_data.ident_map with
    | Access path, _ -> Some path
    | _ -> assert(false)
  )
  | Var.ProgramVar _ -> assert(false)
  in *)

  (* let ap_id_resolver = EdgeExp.T.Access_path_id_resolver graph_data.ident_map in *)

  (* let rec map_idents hil_exp = match hil_exp with
  | HilExp.AccessExpression ae -> (

  )
  | HilExp.UnaryOperator (unop, exp, typ) ->
      HilExp.UnaryOperator (unop, map_idents exp, typ)
  | HilExp.BinaryOperator (op, lexp, rexp) ->
      HilExp.BinaryOperator (op, map_idents lexp, map_idents rexp)
  | HilExp.Cast (typ, exp) ->
      HilExp.Cast (typ, map_idents exp)
  | HilExp.Closure _
  | HilExp.Constant _
  | HilExp.Exception _
  | HilExp.Sizeof _ -> hil_exp
  in *)

  let call_id_resolver ident =
    match Ident.Map.find_opt ident graph_data.ident_map_2 with
    | Some (EdgeExp.Value exp) -> exp
    | Some (EdgeExp.Pair _) -> (
      (* same problem as with ae_id_resolver *)
      assert(false)
    )
    | None -> assert(false)
  in

  let ae_id_resolver var = match var with
  | Var.LogicalVar id -> (
    match Ident.Map.find_opt id graph_data.ident_map_2 with
    | Some (EdgeExp.Value exp) -> (
      match exp with
      | EdgeExp.T.Access path -> Some path
      | _ -> (
        (* Replace idents mapped to more complex expressions later.
        * HilExp.of_sil signature requires this function to return 
        * access expression type. More complex expressions occur due
        * to return values of function calls *)
        None
      )
    )
    | Some (EdgeExp.Pair _) -> (
      (* Figure this out later, too complicated for now. Will probably
       * have to write my own conversion functions for SIL -> HIL
       * because of this... *)
      assert(false)
    )
    | None -> L.die InternalError "Missing mapped expression for '%a' identifier" Ident.pp id
  )
  | Var.ProgramVar _ -> None
  in

  (* stolen from starvation.ml *)
  (* let rec get_access_expr (hilexp : HilExp.t) = match hilexp with
  | AccessExpression access_exp ->
      Some access_exp
  | Cast (_, hilexp) | Exception hilexp | UnaryOperator (_, hilexp, _) ->
      get_access_expr hilexp
  | BinaryOperator _ | Closure _ | Constant _ | Sizeof _ ->
      None
  in *)

  let add_local access locals = 
    let access_base = HilExp.AccessExpression.get_base access in
    AccessPath.BaseMap.update access_base (fun key_opt -> 
      match key_opt with
      | Some access_set -> Some (AccessExpressionSet.add access access_set)
      | None -> Some (AccessExpressionSet.singleton access)
    ) locals
  in


  let is_loop_prune (kind : Sil.if_kind) = match kind with
  | Ik_dowhile | Ik_for | Ik_while -> true
  | _ -> false
  in

  let in_loop = not (List.is_empty graph_data.loop_heads) in


  (* let lb = EdgeExp.map_accesses exp ~f:(fun access _ -> 
    match LTS.EdgeData.get_assignment_rhs graph_data.edge_data access with
    | Value value_rhs -> value_rhs, None
    | EdgeExp.Pair (lb, _) -> lb, None
  ) None |> fst |> process_rhs_value
  in *)


  (* Can't make it the EdgeExp module function due to cyclical dependency *)
  let rec substitute_call_args edge_data args = List.fold args ~init:([], [], [])
  ~f:(fun (lb_acc, ub_acc, typ_acc) (arg, arg_typ) ->
    match substitute_assignments edge_data arg with
    | EdgeExp.Value value -> value :: lb_acc, value :: ub_acc, arg_typ :: typ_acc
    | EdgeExp.Pair (lb, ub) -> lb :: lb_acc, ub :: ub_acc, arg_typ :: typ_acc
  )

  and substitute_assignments edge_data exp = 
    let process_min_max_args args ~f = 
      let subst_args args = EdgeExp.Set.fold (fun arg (lb_set, ub_set) -> 
        match substitute_assignments edge_data arg with
        | EdgeExp.Value value -> EdgeExp.Set.add value lb_set, EdgeExp.Set.add value ub_set
        | EdgeExp.Pair (lb, ub) ->
          EdgeExp.Set.add lb lb_set, EdgeExp.Set.add ub ub_set
      ) args (EdgeExp.Set.empty, EdgeExp.Set.empty)
      in

      let lb_set, ub_set = subst_args args in
      if EdgeExp.Set.equal lb_set ub_set then EdgeExp.Value (f lb_set)
      else EdgeExp.Pair (f lb_set, f ub_set)
    in

    match exp with
    | EdgeExp.T.Access access -> LTS.EdgeData.get_assignment_rhs edge_data access
    | EdgeExp.T.BinOp (op, lexp, rexp) -> (
      let lexp_subst = substitute_assignments edge_data lexp in
      let rexp_subst = substitute_assignments edge_data rexp in
      match lexp_subst, rexp_subst with
      | EdgeExp.Value lexp_value, EdgeExp.Value rexp_value ->
        EdgeExp.Value (EdgeExp.T.BinOp (op, lexp_value, rexp_value))
      | EdgeExp.Value lexp_value, EdgeExp.Pair (rexp_lb, rexp_ub) -> (
        EdgeExp.Pair (EdgeExp.T.BinOp (op, lexp_value, rexp_lb),
                      EdgeExp.T.BinOp (op, lexp_value, rexp_ub))
      )
      | EdgeExp.Pair (lexp_lb, lexp_ub), EdgeExp.Value rexp_value -> (
        EdgeExp.Pair (EdgeExp.T.BinOp (op, lexp_lb, rexp_value),
                      EdgeExp.T.BinOp (op, lexp_ub, rexp_value))
      )
      | EdgeExp.Pair (lexp_lb, lexp_ub), EdgeExp.Pair (rexp_lb, rexp_up) -> (
        EdgeExp.Pair (EdgeExp.T.BinOp (op, lexp_lb, rexp_lb),
                      EdgeExp.T.BinOp (op, lexp_ub, rexp_up))
      )
    )
    | EdgeExp.T.UnOp (op, subexp, typ) -> (
      match substitute_assignments edge_data subexp with
      | EdgeExp.Value value -> EdgeExp.Value (EdgeExp.T.UnOp (op, value, typ))
      | EdgeExp.Pair (lb, ub) -> EdgeExp.Pair (
        EdgeExp.T.UnOp (op, lb, typ), EdgeExp.T.UnOp (op, ub, typ)
      )
    )
    | EdgeExp.T.Call (ret_typ, procname, args, loc) -> (      
      let lb_args, ub_args, arg_types = substitute_call_args edge_data args in
      if List.equal EdgeExp.equal lb_args ub_args
      then EdgeExp.Value (EdgeExp.T.Call (ret_typ, procname, List.zip_exn lb_args arg_types, loc))
      else EdgeExp.Pair (
        (EdgeExp.T.Call (ret_typ, procname, List.zip_exn lb_args arg_types, loc)),
        (EdgeExp.T.Call (ret_typ, procname, List.zip_exn ub_args arg_types, loc))
      )
    )
    | EdgeExp.T.Max args -> process_min_max_args args ~f:(fun args -> EdgeExp.T.Max args)
    | EdgeExp.T.Min args -> process_min_max_args args ~f:(fun args -> EdgeExp.T.Min args)
    | _ -> EdgeExp.Value exp
  in

  match instr with
  | Prune (cond, loc, branch, kind) -> (
    (* debug_log "[PRUNE (%s)] (%a) | %a\n" (Sil.if_kind_to_string kind) Location.pp loc Exp.pp cond; *)
    let hil_exp_cond = HilExp.of_sil ~include_array_indexes:true
      ~f_resolve_id:ae_id_resolver  ~add_deref:false cond (Typ.mk (Tint IBool))
    in
    let edge_exp_cond = EdgeExp.of_hil_exp hil_exp_cond call_id_resolver in

    (* let edge_exp_cond = EdgeExp.of_exp cond graph_data.ident_map (Typ.mk (Tint IBool)) graph_data.type_map in *)
    debug_log "@[<v4>[PRUNE] %a@,Prune type: %a@,Branch: %B@,Exp condition: %a@,EdgeExp condition: %a@,"
      Location.pp loc Sil.pp_if_kind kind branch Exp.pp cond EdgeExp.pp edge_exp_cond;
    
    let normalized_cond = EdgeExp.normalize_condition edge_exp_cond graph_data.tenv in
    let is_int_cond = EdgeExp.is_integer_condition graph_data.tenv normalized_cond in
    let is_on_loop_path = is_loop_prune kind || in_loop in

    let graph_data = if branch && is_on_loop_path && is_int_cond then (
      (* Derive norm from prune condition.
      * [x > y] -> [x - y] > 0
      * [x >= y] -> [x - y + 1] > 0 *)
      match normalized_cond with
      | EdgeExp.T.BinOp (op, lexp, rexp) -> (
        let process_gt lhs rhs = match EdgeExp.is_zero lhs, EdgeExp.is_zero rhs with
        | true, true -> EdgeExp.zero
        | true, _ -> EdgeExp.T.UnOp (Unop.Neg, rhs, None)
        | false, true -> lhs
        | _ -> EdgeExp.T.BinOp (Binop.MinusA None, lhs, rhs)
        in

        let process_op op = match op with
          | Binop.Gt -> Some (process_gt lexp rexp)
          | Binop.Ge -> Some (EdgeExp.add (process_gt lexp rexp) EdgeExp.one)
          | _ -> None
        in

        match process_op op with
        | Some new_norm -> (
          let is_modified = match new_norm with
          | EdgeExp.T.Access access -> AccessExpressionSet.mem access graph_data.loop_modified
          | _ -> false
          in
          if not (is_loop_prune kind) && not is_modified then (
            (* Prune on loop path but not loop head. Norm is only potential,
             * must be confirmed by increment/decrement on this loop path *)
            {graph_data with potential_norms = EdgeExp.Set.add new_norm graph_data.potential_norms}
          ) else (
            let init_norms = EdgeExp.Set.add (EdgeExp.simplify new_norm) graph_data.proc_data.norms in
            {graph_data with proc_data = {graph_data.proc_data with norms = init_norms}}
          )
        ) 
        | None -> graph_data
      )
      | _ -> L.(die InternalError) "Unsupported PRUNE expression!"
    ) else graph_data
    in

    debug_log "@]@,";
    { graph_data with
      loop_heads = if branch then [loc] @ graph_data.loop_heads else graph_data.loop_heads;
      scope_locals = if branch then [AccessExpressionSet.empty] @ graph_data.scope_locals else graph_data.scope_locals;

      edge_data = { graph_data.edge_data with
        branch_info = Some (kind, branch, loc);
        conditions = EdgeExp.Set.add normalized_cond graph_data.edge_data.conditions;
      };
    }
  )
  | Store {e1= Lvar lhs_pvar; typ; e2; loc} when Pvar.is_ssa_frontend_tmp lhs_pvar -> (
    (* TODO: not sure when this case occurs, but starvation checker handles it, need to check later *)
    debug_log "@[<v4>[STORE] (%a) | %a = %a : %a@," Location.pp loc Pvar.(pp Pp.text) lhs_pvar 
      Exp.pp e2 Typ.(pp Pp.text) typ;
    debug_log "SSA frontend temporary variable store@]@,";
    assert(false);
  )
  | Store {e1= Lindex (Lvar base, _)} when Pvar.is_global base -> (
    (* Ignore these assignments for now. Initialization of huge global arrays
     * cause incredible slowdown currently because Infer invokes Store instruction
     * for each initialization value *)
    graph_data
  )
  | Store {e1=lhs; typ; e2=rhs; loc} -> (
    debug_log "@[<v4>[STORE] %a@,Type: %a@,Exp: %a = %a@," 
      Location.pp loc Typ.(pp Pp.text) typ Exp.pp lhs Exp.pp rhs;

    let rhs_hil_exp = HilExp.of_sil ~include_array_indexes:true ~f_resolve_id:ae_id_resolver ~add_deref:false rhs typ in
    let lhs_hil_exp = HilExp.of_sil ~include_array_indexes:true ~f_resolve_id:ae_id_resolver ~add_deref:true lhs typ in
    
    debug_log "@[<v4>HilExp: %a = %a" HilExp.pp lhs_hil_exp HilExp.pp rhs_hil_exp;
    (match rhs_hil_exp with
    | HilExp.Cast (typ, exp) -> (
      debug_log "@,Cast to: %a, Subexp: %a@," Typ.(pp Pp.text) typ HilExp.pp exp;
      match HilExp.get_typ graph_data.tenv exp with
      | Some type_before_cast -> debug_log "Type before cast: %a" Typ.(pp Pp.text) type_before_cast;
      | None -> debug_log "Type before cast: unknown (HilExp.get_typ not fully implemented)";
    )
    | _ -> ()
    );
    debug_log "@]@,";

    (* let lhs_access = Option.value_exn (access_of_lhs_exp ~include_array_indexes:true lhs typ ~f_resolve_id:ap_id_resolver) in
    let lhs_access_exp = EdgeExp.T.Access lhs_access in *)

    (* let lhs_typ = Option.value_exn (AccessPath.get_typ lhs_access graph_data.tenv) in *)
    (* debug_log "LHS AccessPath: %a : %a\n" AccessPath.pp lhs_access Typ.(pp Pp.text) lhs_typ; *)
    let integer_widths =  Exe_env.get_integer_type_widths graph_data.exe_env graph_data.procname in

    let lhs_edge_exp = EdgeExp.of_hil_exp lhs_hil_exp call_id_resolver in
    let lhs_access = match lhs_edge_exp with
    | EdgeExp.T.Access access -> access
    | _ -> L.die InternalError "Left-hand side expression of Store instruction is not an AccessExpression: %a" 
      EdgeExp.pp lhs_edge_exp
    in
    let lhs_access_base = HilExp.AccessExpression.get_base lhs_access in

    let rhs_edge_exp = EdgeExp.of_hil_exp rhs_hil_exp call_id_resolver in
    debug_log "EdgeExp: %a = %a@," EdgeExp.pp lhs_edge_exp EdgeExp.pp rhs_edge_exp;

    let process_rhs_value value = (value 
      |> EdgeExp.simplify 
      |> EdgeExp.remove_casts_of_consts) integer_widths
    in

    let assignment_rhs = match rhs_edge_exp with
    | EdgeExp.T.Call (_, _, _, loc) as call -> (
      match Location.Map.find_opt loc graph_data.proc_data.call_summaries with
      | Some summary -> (
        match summary.return_bound with
        | Some ret_bound -> EdgeExp.Pair ret_bound
        | None -> assert(false)
      )
      | None -> EdgeExp.Value (call |> process_rhs_value)
    )
    | exp -> (
      (* TODO: this sucks and isn't correct (correctness problem in other places too!)
       * think of a better way how to solve this *)
      let lb = EdgeExp.map_accesses exp ~f:(fun access _ -> 
        match LTS.EdgeData.get_assignment_rhs graph_data.edge_data access with
        | EdgeExp.Value value_rhs -> value_rhs, None
        | EdgeExp.Pair (lb, _) -> lb, None
      ) None |> fst |> process_rhs_value
      in

      let ub = EdgeExp.map_accesses exp ~f:(fun access _ -> 
        match LTS.EdgeData.get_assignment_rhs graph_data.edge_data access with
        | Value value_rhs -> value_rhs, None
        | EdgeExp.Pair (_, ub) -> ub, None
      ) None |> fst |> process_rhs_value
      in
      if EdgeExp.equal lb ub then EdgeExp.Value lb else EdgeExp.Pair (lb, ub)
    )
    in

    debug_log "EdgeExp: %a = %s@," EdgeExp.pp lhs_edge_exp 
      (EdgeExp.value_pair_to_string assignment_rhs);

    (* Checks if its possible to confirm some potential norm due to it's
     * decrement on this edge *)
    let rec check_norms lexp rexp potential_norms = match rexp with
      | EdgeExp.Value value -> (
        match value with 
        | EdgeExp.T.BinOp ((Binop.PlusA _ | Binop.MinusA _), rhs_subexp, EdgeExp.T.Const (Const.Cint _))
          when (EdgeExp.equal lexp rhs_subexp) && EdgeExp.Set.mem rhs_subexp potential_norms -> (
            EdgeExp.Set.remove rhs_subexp potential_norms,
            EdgeExp.Set.singleton rhs_subexp
          )
        | _ -> potential_norms, EdgeExp.Set.empty
      )
      | EdgeExp.Pair (lb, ub) -> (
        let potential_norms, lb_norms = check_norms lexp (EdgeExp.Value lb) potential_norms in
        let potential_norms, ub_norms = check_norms lexp (EdgeExp.Value ub) potential_norms in
        potential_norms, EdgeExp.Set.union lb_norms ub_norms
      )
    in

    let potential_norms, new_norms = check_norms lhs_edge_exp assignment_rhs graph_data.potential_norms in

    
    (* let potential_norms, norms = match rhs_edge_exp with 
    | EdgeExp.T.BinOp ((Binop.PlusA _ | Binop.MinusA _), rhs_subexp, EdgeExp.T.Const (Const.Cint _))
      when (EdgeExp.equal lhs_edge_exp rhs_subexp) && EdgeExp.Set.mem rhs_subexp graph_data.potential_norms ->
      EdgeExp.Set.remove rhs_subexp graph_data.potential_norms, 
      EdgeExp.Set.add rhs_subexp graph_data.proc_data.norms

      (* { graph_data with
        potential_norms = EdgeExp.Set.remove rhs_subexp graph_data.potential_norms;

        proc_data = {graph_data.proc_data with 
          norms = EdgeExp.Set.add rhs_subexp graph_data.proc_data.norms
        }
      } *)
    | _ -> graph_data.potential_norms, graph_data.proc_data.norms
    in *)


    let locals, new_norms = if HilExp.AccessExpression.is_return_var lhs_access then (
      debug_log "LHS is a return variable, adding to norms@,";

      (* let new_norms = if EdgeExp.is_variable rhs_edge_exp graph_data.proc_data.formals 
      then EdgeExp.Set.add rhs_edge_exp (EdgeExp.Set.singleton lhs_edge_exp)
      else EdgeExp.Set.singleton lhs_edge_exp
      in *)

      (* debug_log "New norms: ";
      EdgeExp.Set.iter (fun norm -> debug_log "%a " EdgeExp.pp norm) new_norms;
      debug_log "@,"; *)
      add_local lhs_access graph_data.locals, EdgeExp.Set.add lhs_edge_exp new_norms

      (* { graph_data with
        locals = add_local lhs_access graph_data.locals;
        (* local_accesses = AccessExpressionSet.add lhs_access graph_data.local_accesses; *)
        (* type_map = PvarMap.add pvar typ graph_data.type_map; *)

        proc_data = {graph_data.proc_data with 
          norms = EdgeExp.Set.add lhs_edge_exp graph_data.proc_data.norms
        }
      } *)
    ) 
    else graph_data.locals, new_norms
    in

    let is_lhs_top_scope_local = List.for_all graph_data.scope_locals ~f:(fun scope ->
      let f access = AccessPath.equal_base (HilExp.AccessExpression.get_base access) lhs_access_base in
      AccessExpressionSet.find_first_opt f scope |> Option.is_empty
      (* not (AccessPath.BaseSet.mem lhs_access_base scope) *)
    )
    in

    (* let scope_locals = if not is_lhs_top_scope_local then (
      match graph_data.scope_locals with
      | scope :: higher_scopes -> [AccessExpressionSet.add lhs_access scope] @ higher_scopes
      | [] -> [AccessExpressionSet.singleton lhs_access]
    ) else graph_data.scope_locals
    in *)
    
    (* let locals, scope_locals = if is_lhs_top_scope_local then (
      add_local lhs_access_base lhs_access graph_data.locals,
      graph_data.scope_locals
    )
    else (
      add_local lhs_access_base lhs_access graph_data.locals,
      match graph_data.scope_locals with
      | scope :: higher_scopes -> [AccessPath.BaseSet.add lhs_access_base scope] @ higher_scopes
      | [] -> [AccessPath.BaseSet.singleton lhs_access_base]
    )
    in *)

    (* Only base of access expression stripped of any other sub-accesses *)
    let lhs_access_stripped = HilExp.AccessExpression.base lhs_access_base in

    (* Always add LHS access to the set of local variables. It will be removed
     * when exiting current scope if it's not a top-scope local *)
    let locals = add_local lhs_access locals in

    let scope_locals = if
      not (HilExp.AccessExpression.equal lhs_access_stripped lhs_access)
      && AccessPath.BaseMap.mem lhs_access_base locals
      && not is_lhs_top_scope_local
    then (
      match graph_data.scope_locals with
      | scope :: higher_scopes -> [AccessExpressionSet.add lhs_access scope] @ higher_scopes
      | [] -> [AccessExpressionSet.singleton lhs_access]

      (* let scope_locals = if not is_lhs_top_scope_local then (
        match graph_data.scope_locals with
        | scope :: higher_scopes -> [AccessPath.BaseSet.add lhs_access_base scope] @ higher_scopes
        | [] -> [AccessPath.BaseSet.singleton lhs_access_base]
      )
      else graph_data.scope_locals
      in *)
      (* {graph_data with locals; scope_locals} *)
    ) 
    else graph_data.scope_locals
    in


    (* Check if the access base of LHS expression is a formal pointer and add the access
     * expression to norms if it is. We need to track pointer formals due to possible side-effects *)
    let lhs_access_base_typ = snd lhs_access_base in
    let new_norms = if AccessPath.BaseSet.mem lhs_access_base graph_data.proc_data.formals 
    && Typ.is_pointer lhs_access_base_typ
    && (Typ.is_int typ || Typ.is_pointer typ) then (
      match lhs_access with
      | HilExp.AccessExpression.FieldOffset (Dereference _, _)
      | HilExp.AccessExpression.Dereference _ -> (
        debug_log "Formal base '%a' is a pointer: %a. Adding access expression '%a' to norms.@,"
          AccessPath.pp_base lhs_access_base 
          Typ.(pp Pp.text) lhs_access_base_typ
          HilExp.AccessExpression.pp lhs_access;
        EdgeExp.Set.add lhs_edge_exp new_norms
      )
      | _ -> new_norms
    ) else new_norms
    in

    let norms = EdgeExp.Set.union graph_data.proc_data.norms new_norms in

    debug_log "Norms: ";
    EdgeExp.Set.iter (fun norm -> debug_log "%a | " EdgeExp.pp norm) norms;
    debug_log "@,";


    debug_log "@]@,";
    { graph_data with
      locals;
      scope_locals;
      potential_norms;
      edge_data = LTS.EdgeData.add_assignment graph_data.edge_data lhs_access assignment_rhs;
      
      loop_modified = if in_loop  then AccessExpressionSet.add lhs_access graph_data.loop_modified 
        else graph_data.loop_modified;

      proc_data = {graph_data.proc_data with norms}
    }
  )
  | Load {id; e; typ; loc} -> (
    debug_log "@[<v4>[LOAD] %a@,Type: %a@,Exp: %a = %a@,"
      Location.pp loc Typ.(pp Pp.text) typ Ident.pp id Exp.pp e;

    let rhs_hil_expr = HilExp.of_sil ~include_array_indexes:true
      ~f_resolve_id:ae_id_resolver
      ~add_deref:true e typ
    in

    debug_log "RHS HilExp: %a = %a@," Ident.pp id HilExp.pp rhs_hil_expr;

    let rhs_edge_exp = EdgeExp.of_hil_exp rhs_hil_expr call_id_resolver in
    debug_log "RHS EdgeExp: %a = %a@," Ident.pp id EdgeExp.pp rhs_edge_exp;

    (* TODO: of_sil, of_hil_exp should work with assignment_rhs
     * and return it so we can add it to the ident_map instead
     * of just wrapping artifically *)
    let ident_map_2 = Ident.Map.add id (EdgeExp.Value rhs_edge_exp) graph_data.ident_map_2 in

    (* TODO: this is quite legacy, map_ident should probably be recursive... *)
    (* let map_ident exp = match exp with
    | Exp.Lindex _ -> (
      debug_log "Exp.Lindex@,";
      let accesses = access_of_exp ~include_array_indexes:true exp typ ~f_resolve_id:ap_id_resolver in
      assert (Int.equal (List.length accesses) 1);
      let access = List.hd_exn accesses in
      Ident.Map.add id ((EdgeExp.T.Access access), typ) graph_data.ident_map,
      graph_data.type_map
    )
    | Exp.Lfield (struct_exp, name, struct_type) -> (
      debug_log "Exp.Lfield@,";
      match struct_exp with
      | Exp.Var struct_id -> (
        match Ident.Map.find struct_id graph_data.ident_map with
        | EdgeExp.T.Access path, path_typ -> (
          let access = AccessPath.FieldAccess name in
          let ext_path = EdgeExp.T.Access (AccessPath.append path [access]) in
          Ident.Map.add id (ext_path, typ) graph_data.ident_map,
          graph_data.type_map
        )
        | ref_exp, ref_typ -> L.die InternalError "Unexpected root structure expression: %a" EdgeExp.pp ref_exp;
      )      
      | Exp.Lvar struct_pvar -> (
        let access_base = AccessPath.base_of_pvar struct_pvar struct_type in
        let field_access = AccessPath.FieldAccess name in
        let full_path : AccessPath.t = access_base, [field_access] in
        Ident.Map.add id ((EdgeExp.T.Access full_path), typ) graph_data.ident_map,
        PvarMap.add struct_pvar struct_type graph_data.type_map
      )
      | Exp.Cast (result_type, original_exp) -> (
        debug_log "Result type: %a, original exp: %a@," Typ.(pp Pp.text) result_type Exp.pp original_exp;
        L.die InternalError "Unexpected structure expression type: %a. Field: %a, Struct type: %a" 
          Exp.pp exp Fieldname.pp name Typ.(pp Pp.text) struct_type;
      )
      | exp -> (
        L.die InternalError "Unexpected structure expression type: %a. Field: %a, Struct type: %a" 
          Exp.pp exp Fieldname.pp name Typ.(pp Pp.text) struct_type;
      )
    )
    | Exp.Lvar pvar -> (
      debug_log "Exp.Lvar@,";
      let access = EdgeExp.T.Access (AccessPath.of_pvar pvar typ) in
      Ident.Map.add id (access, typ) graph_data.ident_map,
      PvarMap.add pvar typ graph_data.type_map
    )
    | Exp.Var rhs_id -> (
      debug_log "Exp.Var@,";
      let ref_exp, ref_type = Ident.Map.find rhs_id graph_data.ident_map in
      if Typ.is_pointer ref_type && Typ.equal (Typ.strip_ptr ref_type) typ then (
        debug_log "Typ: %a, Ref typ: %a, loading dereferenced value@," Typ.(pp Pp.text) typ Typ.(pp Pp.text) ref_type;
      );
      Ident.Map.add id (ref_exp, typ) graph_data.ident_map,
      graph_data.type_map
    )
    | _ -> L.(die InternalError)"Unsupported LOAD lhs-expression type!"
    in *)

    (* let ident_map, type_map = map_ident e in *)
    debug_log "@]@,";
    { graph_data with ident_map_2}

  )
  | Call ((ret_id, ret_typ), Exp.Const (Const.Cfun callee_pname), args, loc, _) -> (
    debug_log "@[<v4>[CALL] %a@,Procedure name: %a@," Location.pp loc Procname.pp callee_pname;

    debug_log "@[<v4>Processing call arguments:@,";
    let args = List.mapi args ~f:(fun idx (arg, arg_typ) ->
      debug_log "@[<v2>(%d) Exp: %a : %a@," idx Exp.pp arg Typ.(pp Pp.text) arg_typ;
      let arg_hil_exp = HilExp.of_sil ~include_array_indexes:true
        ~f_resolve_id:ae_id_resolver ~add_deref:false arg arg_typ
      in
      debug_log "HilExp: %a : %a@," HilExp.pp arg_hil_exp Typ.(pp Pp.text) arg_typ;

      let arg_edge_exp = EdgeExp.of_hil_exp arg_hil_exp call_id_resolver in
      debug_log "Transformed EdgeExp: %a@]@," EdgeExp.pp arg_edge_exp;

      arg_edge_exp, arg_typ
    )
    in
    debug_log "@]@,";


    let extract_norms arg_list = 
      debug_log "@[<v4>Extracting norms from call arguments@,";
      let norms = List.fold arg_list ~init:EdgeExp.Set.empty
      ~f:(fun norms (arg, arg_typ) -> 
        if Typ.is_int arg_typ || Typ.is_pointer arg_typ then (
          let simplified_arg = EdgeExp.simplify arg in
          debug_log "Integer argument type, simplified: %a@,"
            EdgeExp.pp simplified_arg;

          let arg_norms = EdgeExp.get_access_exp_set simplified_arg in
          debug_log "New norms: ";
          EdgeExp.Set.iter (fun norm -> debug_log "%a, " EdgeExp.pp norm) arg_norms;
          debug_log "@,";
          EdgeExp.Set.union arg_norms norms
        ) else (
          debug_log "Non-integer argument type, ignoring@,";
          norms
        )
      )
      in
      debug_log "@]@,";
      norms
    in

    let lb_args, ub_args, arg_types = substitute_call_args 
      graph_data.edge_data (List.rev args)
    in

    let create_value_call args =
      let subst_args = List.zip_exn args arg_types in
      (ret_typ, callee_pname, subst_args, loc),
      extract_norms subst_args
    in

    let call_pair, call_pair_exp, arg_norms = if List.equal EdgeExp.equal lb_args ub_args
    then (
      let call_tuple, norms = create_value_call lb_args in
      EdgeExp.CallValue call_tuple,
      EdgeExp.Value (EdgeExp.T.Call call_tuple),
      norms
    )
    else (
      let lb_value_call, lb_norms = create_value_call lb_args in
      let ub_value_call, ub_norms = create_value_call ub_args in
      EdgeExp.CallPair (lb_value_call, ub_value_call),
      EdgeExp.Pair (EdgeExp.T.Call lb_value_call, EdgeExp.T.Call ub_value_call),
      EdgeExp.Set.union lb_norms ub_norms
    )
    in

    (* let call = EdgeExp.T.Call (ret_typ, callee_pname, args, loc) in *)

    debug_log "@[<v4>Loading call summary@,";
    let payload_opt = graph_data.proc_data.analysis_data.analyze_dependency callee_pname in
    let call_summaries, return_bound, edge_data = match payload_opt with
    | Some (_, payload) -> (
      debug_log "Payload exists, substituting return bound@,";
      let subst_ret_bound_opt = match payload.return_bound with
      | Some (lb_ret_bound, ub_ret_bound) -> (
        Some (EdgeExp.subst lb_ret_bound args payload.formal_map,
              EdgeExp.subst ub_ret_bound args payload.formal_map)
      )
      | None -> None
      in
      
      debug_log "@[<v2>Substituting formals bounds:@,";
      debug_log "FormalMap: %a@," FormalMap.pp payload.formal_map;
      let edge_data = EdgeExp.Map.fold (fun formal (lb, ub) acc ->
        debug_log "Formal: %a  --->  [%a, %a]@," EdgeExp.pp formal EdgeExp.pp lb EdgeExp.pp ub;
        (* let lhs_subst = match EdgeExp.subst formal args payload.formal_map with
        | EdgeExp.T.Access access -> access
        | _ -> L.die InternalError "Unsupported formal expression: %a. 
          Only Access expressions are allowed." EdgeExp.pp formal
        in *)
        let rec extract_lhs_access exp = match exp with
        | EdgeExp.T.Access lhs_access -> lhs_access
        | EdgeExp.T.Max args when Int.equal (EdgeExp.Set.cardinal args) 1 -> (
          extract_lhs_access (EdgeExp.Set.min_elt args)
        )
        | exp -> (
          L.die InternalError "Unsupported formal expression '%a',
            access expression expected" EdgeExp.pp exp 
        ) 
        in
        
        let lhs_subst = (EdgeExp.subst formal args payload.formal_map) in
        let lhs_subst_access = extract_lhs_access lhs_subst in

        let lb_subst = EdgeExp.subst lb args payload.formal_map in
        let ub_subst = EdgeExp.subst ub args payload.formal_map in
        let bound = if EdgeExp.equal lb_subst ub_subst 
          then EdgeExp.Value lb_subst
          else EdgeExp.Pair (lb_subst, ub_subst)
        in

        debug_log "[Substituted] Formal: %a  --->  [%a, %a]@," 
        HilExp.AccessExpression.pp lhs_subst_access
          EdgeExp.pp lb_subst EdgeExp.pp ub_subst;

        (* let formal_access = match formal with
        | EdgeExp.T.Access access -> access
        | exp -> (
          L.die InternalError "Unknown expression: %a" EdgeExp.pp exp
        )
        in *)
        LTS.EdgeData.add_assignment acc lhs_subst_access bound
      ) payload.formal_bounds graph_data.edge_data
      in
      (* edge_data = LTS.EdgeData.add_assignment graph_data.edge_data lhs_access assignment_rhs; *)
      debug_log "@]@,";

      let summary = { payload with return_bound = subst_ret_bound_opt } in

      Location.Map.add loc summary graph_data.proc_data.call_summaries,
      Option.value_map subst_ret_bound_opt ~default:call_pair_exp 
        ~f:(fun subst_ret_bound -> EdgeExp.Pair subst_ret_bound),
      edge_data
    )
    | None -> (
      debug_log "Payload missing, ignoring";
      graph_data.proc_data.call_summaries,
      call_pair_exp,
      graph_data.edge_data
    )
    in

    debug_log "@]@,Adding return identifier mapping: %a = %s@]@,@," 
      Ident.pp ret_id
      (EdgeExp.value_pair_to_string return_bound);

    { graph_data with
      ident_map = Ident.Map.add ret_id (call_pair_exp, ret_typ) graph_data.ident_map;
      ident_map_2 = Ident.Map.add ret_id return_bound graph_data.ident_map_2;
      (* type_map = PvarMap.add (Pvar.mk_abduced_ret callee_pname loc) ret_typ graph_data.type_map; *)

      edge_data = { edge_data with 
        calls = EdgeExp.CallPairSet.add call_pair edge_data.calls
      };

      proc_data = {graph_data.proc_data with
        call_summaries = call_summaries;
        norms = EdgeExp.Set.union graph_data.proc_data.norms arg_norms;
      }
    }
  )
  | Metadata metadata -> (match metadata with
    | VariableLifetimeBegins (pvar, typ, loc) -> (
      debug_log "@[<v4>[VariableLifetimeBegins] %a@,Variable: %a@," Location.pp loc Pvar.pp_value pvar;
      let pvar_base_access = HilExp.AccessExpression.base (AccessPath.base_of_pvar pvar typ) in
      let scope_locals = match graph_data.scope_locals with
      | scope::higher_scopes -> (
        debug_log "Current scope variables: ";
        let variables = AccessExpressionSet.add pvar_base_access scope in
        AccessExpressionSet.iter (fun base -> debug_log "%a " HilExp.AccessExpression.pp base) variables;
        [variables] @ higher_scopes
      )
      | [] -> [AccessExpressionSet.singleton pvar_base_access]
      in

      debug_log "@]@,@,";
      { graph_data with 
        locals = add_local pvar_base_access graph_data.locals;
        scope_locals = scope_locals;
      }
    )
    | ExitScope (var_list, loc) -> (
      let exit_pvars = List.filter var_list ~f:(fun var -> Var.is_pvar var) in
      if not (List.is_empty exit_pvars) then (
        debug_log "@[<v4>[ExitScope] %a@," Location.pp loc;
        debug_log "Variables: ";
        List.iter exit_pvars ~f:(fun var -> debug_log "%a " Var.pp var);
        debug_log "@]@,@,";
      );
      graph_data
    )
    | _ -> graph_data
  )
  | instr -> (
    L.die InternalError "SIL instruction not implemented: %a"
      Sil.(pp_instr ~print_types:true Pp.text) instr
  )


let exec_node node graph_data =
  let rev_instrs = IContainer.to_rev_list ~fold:Instrs.fold (Procdesc.Node.get_instrs node) in
  List.fold (List.rev rev_instrs) ~init:graph_data ~f:exec_instr


let rec traverseCFG : Procdesc.t -> Procdesc.Node.t -> Procdesc.NodeSet.t -> construction_temp_data 
  -> (Procdesc.NodeSet.t * construction_temp_data) = 
  fun proc_desc cfg_node visited_cfg_nodes graph_data -> (

  (* console_log "[Visiting node] %a : %s\n" Procdesc.Node.pp cfg_node (pp_nodekind (Procdesc.Node.get_kind cfg_node)); *)

  let cfg_predecessors = Procdesc.Node.get_preds cfg_node in
  let cfg_successors = Procdesc.Node.get_succs cfg_node in
  let in_degree = List.length cfg_predecessors in
  let out_degree = List.length cfg_successors in
  (* console_log "[%a] In-degree: %d, Out-degree: %d\n" Procdesc.Node.pp cfg_node in_degree out_degree; *)


  (* TODO: should probably POP loophead from stack if we encounter false branch later on.
    * Otherwise we are accumulating loop heads from previous loops but it doesn't seem to
    * affect the algorithm in any way. *)
  let is_loop_head = Procdesc.is_loop_head proc_desc cfg_node in
  let is_backedge = if is_loop_head then (
    debug_log "[LOOP HEAD] %a@," Procdesc.Node.pp cfg_node;
    match Stack.top graph_data.loophead_stack with
    | Some last_cfg_loophead -> (
        debug_log "[PREVIOUS LOOP HEAD] %a@," Procdesc.Node.pp last_cfg_loophead;
        if Procdesc.Node.equal last_cfg_loophead cfg_node then (
          let _ = Stack.pop_exn graph_data.loophead_stack in
          true
        ) else (
          Stack.push graph_data.loophead_stack cfg_node;
          false
        )
    )
    | None -> (
      Stack.push graph_data.loophead_stack cfg_node;
      false
    )
  ) else false
  in

  
  if Procdesc.NodeSet.mem cfg_node visited_cfg_nodes then (
    (* console_log "[%a] Visited\n" Procdesc.Node.pp cfg_node; *)

    let graph_data = if is_join_node cfg_node || in_degree > 1 then (
      let edge_data = LTS.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
      let edge_data = if is_backedge then LTS.EdgeData.set_backedge edge_data else edge_data in
      (* console_log "IS_BACKEDGE: %B\n" is_backedge; *)
      let lts_node = Procdesc.NodeMap.find cfg_node graph_data.node_map in
      (* log "Mapped node %a\n" LTS.Node.pp node; *)
      (* log "[New edge] %a ---> %a\n" LTS.Node.pp graph_data.last_node LTS.Node.pp node; *)
      let new_edge = LTS.E.create graph_data.last_node edge_data lts_node in
      let edges = LTS.EdgeSet.add new_edge graph_data.proc_data.edges in
      { graph_data with 
        edge_data = LTS.EdgeData.default;
        proc_data = {graph_data.proc_data with edges = edges}
      }
    )
    else graph_data
    in
    (visited_cfg_nodes, graph_data)
  )
  else (
    let visited_cfg_nodes = Procdesc.NodeSet.add cfg_node visited_cfg_nodes in

    let remove_scoped_locals locals scope_locals = AccessExpressionSet.fold (fun access locals_map ->
      let access_base = HilExp.AccessExpression.get_base access in
      if HilExp.AccessExpression.is_base access then (
        AccessPath.BaseMap.remove access_base locals_map
      ) else (
        AccessPath.BaseMap.update access_base (fun accesses_opt ->
          match accesses_opt with
          | Some accesses -> (
            let accesses = AccessExpressionSet.remove access accesses in
            if AccessExpressionSet.is_empty accesses then None else Some accesses
          )
          | None -> L.die InternalError "Trying to remove missing scoped local access from locals map"
        ) locals_map
      )
    ) scope_locals graph_data.locals
    in

    let graph_data = if in_degree > 1 && not is_loop_head then (
      (* Join node *)
      let join_node_id = Procdesc.Node.get_id cfg_node in
      let join_node = LTS.Node.Join (Procdesc.Node.get_loc cfg_node, join_node_id) in
      let edge_data = LTS.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
      let new_edge = LTS.E.create graph_data.last_node edge_data join_node in
      (* log "Locals: %a\n" Pvar.Set.pp graph_data.locals;
      log "Scope locals:\n"; List.iter graph_data.scope_locals ~f:(fun scope -> log "  %a\n" Pvar.Set.pp scope; ); *)
      { graph_data with
        last_node = join_node;
        edge_data = LTS.EdgeData.default;
        locals = remove_scoped_locals graph_data.locals (List.hd_exn graph_data.scope_locals);
        scope_locals = List.tl_exn graph_data.scope_locals;
        node_map = Procdesc.NodeMap.add cfg_node join_node graph_data.node_map;

        proc_data = {graph_data.proc_data with 
          nodes = LTS.NodeSet.add join_node graph_data.proc_data.nodes;
          edges = LTS.EdgeSet.add new_edge graph_data.proc_data.edges;
        }
      }
    ) else (
      graph_data
    )
    in


    (* Execute node instructions *)
    let graph_data = exec_node cfg_node graph_data in

    let graph_data = if out_degree > 1 then (
      (* Split node, create new DCP prune node *)
      let branch_node = List.hd_exn cfg_successors in
      let loc = Procdesc.Node.get_loc branch_node in
      let branch_node_id = Procdesc.Node.get_id branch_node in
      let if_kind = match Procdesc.Node.get_kind branch_node with
      | Procdesc.Node.Prune_node (_, kind, _) -> kind
      | _ -> assert(false)
      in
      let prune_node = LTS.Node.Prune (if_kind, loc, branch_node_id) in
      let edge_data = LTS.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
      let new_edge = LTS.E.create graph_data.last_node edge_data prune_node in

      let is_pred_loophead = match List.hd cfg_predecessors with
      | Some pred -> Procdesc.is_loop_head proc_desc pred
      | _ -> false
      in
      let node_map = if is_pred_loophead then (
        let loop_head_node = List.hd_exn cfg_predecessors in
        (* console_log "Adding node to map: %a\n" Procdesc.Node.pp loop_head_node; *)
        Procdesc.NodeMap.add loop_head_node prune_node graph_data.node_map
      )
      else if in_degree > 1 then (
        (* Check if current node has 2 direct predecessors and 2 direct successors
         * which would make it merged join + split node *)
        (* console_log "Adding node to map: %a\n" Procdesc.Node.pp cfg_node; *)
        Procdesc.NodeMap.add cfg_node prune_node graph_data.node_map
      )
      else graph_data.node_map
      in

      { graph_data with 
        last_node = prune_node;
        edge_data = LTS.EdgeData.default;
        node_map = node_map;

        proc_data = {graph_data.proc_data with 
          nodes = LTS.NodeSet.add prune_node graph_data.proc_data.nodes;
          edges = LTS.EdgeSet.add new_edge graph_data.proc_data.edges;
        }
      }
    ) 
    else graph_data
    in

    if is_exit_node cfg_node then (
      let exit_node = LTS.Node.Exit in
      let edge_data = LTS.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
      let new_edge = LTS.E.create graph_data.last_node edge_data exit_node in
      let graph_data = { graph_data with 
        last_node = exit_node;
        edge_data = LTS.EdgeData.default;

        proc_data = {graph_data.proc_data with
          nodes = LTS.NodeSet.add exit_node graph_data.proc_data.nodes;
          edges = LTS.EdgeSet.add new_edge graph_data.proc_data.edges;
        }
      }
      in
      (visited_cfg_nodes, graph_data)
    )
    else (
      let last_node = graph_data.last_node in
      let loop_heads = graph_data.loop_heads in
      let locals = graph_data.locals in
      let scope_locals = graph_data.scope_locals in

      List.fold cfg_successors ~f:(fun (visited_cfg_nodes, graph_data) next_node ->
        let graph_data = { graph_data with
          last_node = last_node;
          loop_heads = loop_heads;
          locals = locals;
          scope_locals = scope_locals;
        }
        in
        traverseCFG proc_desc next_node visited_cfg_nodes graph_data
      ) ~init:(visited_cfg_nodes, graph_data)
    )
  )
)


let construct : LooperSummary.t InterproceduralAnalysis.t -> procedure_data = 
  fun summary -> (
    debug_log "@[<v>";

    let proc_desc = summary.proc_desc in
    let procname = Procdesc.get_proc_name proc_desc in
    let tenv = Exe_env.get_proc_tenv summary.exe_env procname in
    let begin_loc = Procdesc.get_loc proc_desc in
    let start_node = Procdesc.get_start_node proc_desc in
    let lts_start_node = LTS.Node.Start (procname, begin_loc) in

    let locals = Procdesc.get_locals proc_desc in
    let formals = Procdesc.get_pvar_formals proc_desc in

    let _, type_map = List.fold locals ~init:(Pvar.Set.empty, PvarMap.empty) ~f:
    (fun (locals, type_map) (local : ProcAttributes.var_data) ->
      let pvar = Pvar.mk local.name procname in
      let type_map = PvarMap.add pvar local.typ type_map in
      let locals = Pvar.Set.add pvar locals in
      locals, type_map
    )
    in

    debug_log "@[<v4>[Procedure formals]@,";
    let formals, type_map, norm_set = List.foldi formals ~f:(fun idx (formals, type_map, norm_set) (pvar, typ) ->
      debug_log "@[<v4>(%d) %a : %a" idx Pvar.(pp Pp.text) pvar Typ.(pp Pp.text) typ;
      let norm_set = if Typ.is_pointer_to_int typ then (
        debug_log "@,Pointer to int";
        norm_set
      ) 
      else if Typ.is_pointer typ then (
        (* TODO: recursively check? *)
        let underlying_type = Typ.strip_ptr typ in
        if Typ.is_struct underlying_type then (
          debug_log "@,Pointer to struct: %a" Typ.(pp Pp.text) underlying_type;
          norm_set
        ) else (
          debug_log "@,Pointer to: %a" Typ.(pp Pp.text) underlying_type;
          norm_set
        )        
      )
      else norm_set
      in
      debug_log "@]@,";
      let formal_pvar_base_access = AccessPath.base_of_pvar pvar typ in
      let type_map = PvarMap.add pvar typ type_map in
      let formals = AccessPath.BaseSet.add formal_pvar_base_access formals in
      formals, type_map, norm_set
    ) ~init:(AccessPath.BaseSet.empty, type_map, EdgeExp.Set.empty)
    in
    debug_log "@]@,";

    let construction_data = {
      last_node = lts_start_node;
      loophead_stack = Stack.create ();
      edge_data = LTS.EdgeData.default;
      ident_map = Ident.Map.empty;
      ident_map_2 = Ident.Map.empty;

      node_map = Procdesc.NodeMap.empty;
      potential_norms = EdgeExp.Set.empty;
      loop_heads = [];
      loop_modified = AccessExpressionSet.empty;

      scope_locals = [AccessExpressionSet.empty];
      locals = AccessPath.BaseMap.empty;
      (* local_accesses = AccessExpressionSet.empty; *)
      (* type_map = type_map; *)
      tenv;
      exe_env = summary.exe_env;
      procname;

      proc_data = {
        nodes = LTS.NodeSet.singleton lts_start_node;
        edges = LTS.EdgeSet.empty;
        norms = EdgeExp.Set.empty;
        formals = formals;
        analysis_data = summary;
        call_summaries = Location.Map.empty;
        lts = LTS.create ()
      }
    }
    in
    let graph_data = traverseCFG proc_desc start_node Procdesc.NodeSet.empty construction_data |> snd in

    LTS.NodeSet.iter (fun node -> LTS.add_vertex graph_data.proc_data.lts node) graph_data.proc_data.nodes;
    LTS.EdgeSet.iter (fun edge -> LTS.add_edge_e graph_data.proc_data.lts edge) graph_data.proc_data.edges;

    debug_log "@]";
    graph_data.proc_data
  )
