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
  ident_map: (EdgeExp.t * Typ.t) Ident.Map.t;
  ident_map_2: EdgeExp.t Ident.Map.t;

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

  proc_data: procedure_data;
}


let pp_nodekind kind = match kind with
  | Procdesc.Node.Start_node -> "Start_node"
  | Procdesc.Node.Exit_node -> "Exit_node"
  | Procdesc.Node.Stmt_node stmt -> F.asprintf "Stmt_node(%a)" Procdesc.Node.pp_stmt stmt
  | Procdesc.Node.Join_node -> "Join_node"
  | Procdesc.Node.Prune_node (branch, ifkind, _) -> F.asprintf "Prune_node(%B, %S)" branch (Sil.if_kind_to_string ifkind)
  | Procdesc.Node.Skip_node string -> F.asprintf "Skip_node (%s)" string


let is_join_node node = match Procdesc.Node.get_kind node with
  | Procdesc.Node.Join_node -> true
  | _ -> false


let is_exit_node node = match Procdesc.Node.get_kind node with
  | Procdesc.Node.Exit_node -> true
  | _ -> false



let exec_instr : construction_temp_data -> Sil.instr -> construction_temp_data = fun graph_data instr ->
  let ap_id_resolver var = match var with
  | Var.LogicalVar id -> (
    match Ident.Map.find id graph_data.ident_map with
    | Access path, _ -> Some path
    | _ -> assert(false)
  )
  | Var.ProgramVar _ -> assert(false)
  in

  (* let ap_id_resolver = EdgeExp.access_path_id_resolver graph_data.ident_map in *)

  let ae_id_resolver var = match var with
  | Var.LogicalVar id -> (
    match Ident.Map.find_opt id graph_data.ident_map_2 with
    | Some (EdgeExp.Access path) -> Some path
    | _ -> None
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

  match instr with
  | Prune (cond, loc, branch, kind) -> (
    (* debug_log "[PRUNE (%s)] (%a) | %a\n" (Sil.if_kind_to_string kind) Location.pp loc Exp.pp cond; *)
    let hil_exp_cond = HilExp.of_sil ~include_array_indexes:true
      ~f_resolve_id:ae_id_resolver  ~add_deref:false cond (Typ.mk (Tint IBool))
    in
    let edge_exp_cond = EdgeExp.of_hil_exp hil_exp_cond in

    (* let edge_exp_cond = EdgeExp.of_exp cond graph_data.ident_map (Typ.mk (Tint IBool)) graph_data.type_map in *)
    debug_log "@[<v4>[PRUNE] %a@,Prune type: %s@,Branch: %B@,Exp condition: %a@,EdgeExp condition: %a@,"
      Location.pp loc (Sil.if_kind_to_string kind) branch Exp.pp cond EdgeExp.pp edge_exp_cond;
    
    let normalized_cond = EdgeExp.normalize_condition edge_exp_cond graph_data.tenv in
    let is_int_cond = EdgeExp.is_integer_condition graph_data.tenv normalized_cond in
    let is_on_loop_path = is_loop_prune kind || in_loop in

    let graph_data = if branch && is_on_loop_path && is_int_cond then (
      (* Derive norm from prune condition.
      * [x > y] -> [x - y] > 0
      * [x >= y] -> [x - y + 1] > 0 *)
      match normalized_cond with
      | EdgeExp.BinOp (op, lexp, rexp) -> (
        let process_gt lhs rhs = match EdgeExp.is_zero lhs, EdgeExp.is_zero rhs with
        | true, true -> EdgeExp.zero
        | true, _ -> EdgeExp.UnOp (Unop.Neg, rhs, None)
        | false, true -> lhs
        | _ -> EdgeExp.BinOp (Binop.MinusA None, lhs, rhs)
        in

        let process_op op = match op with
          | Binop.Gt -> Some (process_gt lexp rexp)
          | Binop.Ge -> Some (EdgeExp.add (process_gt lexp rexp) EdgeExp.one)
          | _ -> None
        in

        match process_op op with
        | Some new_norm -> (
          let is_modified = match new_norm with
          | EdgeExp.Access access -> AccessExpressionSet.mem access graph_data.loop_modified
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
    let lhs_access_exp = EdgeExp.Access lhs_access in *)

    (* let lhs_typ = Option.value_exn (AccessPath.get_typ lhs_access graph_data.tenv) in *)
    (* debug_log "LHS AccessPath: %a : %a\n" AccessPath.pp lhs_access Typ.(pp Pp.text) lhs_typ; *)
    let lhs_edge_exp = EdgeExp.of_hil_exp lhs_hil_exp in
    let lhs_access = match lhs_edge_exp with
    | EdgeExp.Access access -> access
    | _ -> L.die InternalError "Left-hand side expression of Store instruction is not an AccessExpression: %a" 
      EdgeExp.pp lhs_edge_exp
    in
    let lhs_access_base = HilExp.AccessExpression.get_base lhs_access in

    let rhs_edge_exp = match EdgeExp.of_hil_exp rhs_hil_exp with
    | EdgeExp.Call (_, _, _, loc) as call -> (
      match Location.Map.find_opt loc graph_data.proc_data.call_summaries with
      | Some summary -> (
        match summary.return_bound with
        | Some ret_bound -> ret_bound
        | None -> assert(false)
      )
      | None -> call
    )
    | exp -> (
      EdgeExp.map_accesses exp 
        ~f:(fun access _ -> LTS.EdgeData.get_assignment_rhs graph_data.edge_data access, None) None |> fst
    ) 
    |> EdgeExp.simplify
    in
    debug_log "EdgeExp: %a = %a@," EdgeExp.pp lhs_edge_exp EdgeExp.pp rhs_edge_exp;

    (* Check if we can add new norm to the norm set *)
    let potential_norms, norms = match rhs_edge_exp with 
    | EdgeExp.BinOp ((Binop.PlusA _ | Binop.MinusA _), rhs_subexp, EdgeExp.Const (Const.Cint _))
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
    in


    let locals, norms = if HilExp.AccessExpression.is_return_var lhs_access then (
      debug_log "LHS is a return variable, adding to norms@,";

      (* let new_norms = if EdgeExp.is_variable rhs_edge_exp graph_data.proc_data.formals 
      then EdgeExp.Set.add rhs_edge_exp (EdgeExp.Set.singleton lhs_edge_exp)
      else EdgeExp.Set.singleton lhs_edge_exp
      in *)

      (* debug_log "New norms: ";
      EdgeExp.Set.iter (fun norm -> debug_log "%a " EdgeExp.pp norm) new_norms;
      debug_log "@,"; *)
      add_local lhs_access graph_data.locals, EdgeExp.Set.add lhs_edge_exp norms

      (* { graph_data with
        locals = add_local lhs_access graph_data.locals;
        (* local_accesses = AccessExpressionSet.add lhs_access graph_data.local_accesses; *)
        (* type_map = PvarMap.add pvar typ graph_data.type_map; *)

        proc_data = {graph_data.proc_data with 
          norms = EdgeExp.Set.add lhs_edge_exp graph_data.proc_data.norms
        }
      } *)
    ) 
    else graph_data.locals, norms
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
    let norms = if AccessPath.BaseSet.mem lhs_access_base graph_data.proc_data.formals 
    && Typ.is_pointer lhs_access_base_typ then (
      debug_log "Formal base '%a' is a pointer: %a. Adding access expression '%a' to norms.@,"
        AccessPath.pp_base lhs_access_base 
        Typ.(pp Pp.text) lhs_access_base_typ
        HilExp.AccessExpression.pp lhs_access;

      EdgeExp.Set.add lhs_edge_exp norms
    ) else norms
    in

    debug_log "Norms: ";
    EdgeExp.Set.iter (fun norm -> debug_log "%a | " EdgeExp.pp norm) norms;
    debug_log "@,";


    debug_log "@]@,";
    { graph_data with
      locals;
      scope_locals;
      potential_norms;
      edge_data = LTS.EdgeData.add_assignment graph_data.edge_data lhs_access rhs_edge_exp;
      
      loop_modified = if in_loop  then AccessExpressionSet.add lhs_access graph_data.loop_modified 
        else graph_data.loop_modified;

      proc_data = {graph_data.proc_data with norms}
    }
  )
  | Load {id; e; typ; loc} -> (
    debug_log "@[<v4>[LOAD] %a@,Type: %a@,Exp: %a = %a@,"
      Location.pp loc Typ.(pp Pp.text) typ Ident.pp id Exp.pp e;

    let rhs_hil_expr = HilExp.of_sil ~include_array_indexes:true ~f_resolve_id:ae_id_resolver ~add_deref:true e typ in
    debug_log "RHS HilExp: %a = %a@," Ident.pp id HilExp.pp rhs_hil_expr;

    let rhs_edge_exp = EdgeExp.of_hil_exp rhs_hil_expr in
    debug_log "RHS EdgeExp: %a = %a@," Ident.pp id EdgeExp.pp rhs_edge_exp;

    let ident_map_2 = Ident.Map.add id rhs_edge_exp graph_data.ident_map_2 in

    (* TODO: this is quite legacy, map_ident should probably be recursive... *)
    (* let map_ident exp = match exp with
    | Exp.Lindex _ -> (
      debug_log "Exp.Lindex@,";
      let accesses = access_of_exp ~include_array_indexes:true exp typ ~f_resolve_id:ap_id_resolver in
      assert (Int.equal (List.length accesses) 1);
      let access = List.hd_exn accesses in
      Ident.Map.add id ((EdgeExp.Access access), typ) graph_data.ident_map,
      graph_data.type_map
    )
    | Exp.Lfield (struct_exp, name, struct_type) -> (
      debug_log "Exp.Lfield@,";
      match struct_exp with
      | Exp.Var struct_id -> (
        match Ident.Map.find struct_id graph_data.ident_map with
        | EdgeExp.Access path, path_typ -> (
          let access = AccessPath.FieldAccess name in
          let ext_path = EdgeExp.Access (AccessPath.append path [access]) in
          Ident.Map.add id (ext_path, typ) graph_data.ident_map,
          graph_data.type_map
        )
        | ref_exp, ref_typ -> L.die InternalError "Unexpected root structure expression: %a" EdgeExp.pp ref_exp;
      )      
      | Exp.Lvar struct_pvar -> (
        let access_base = AccessPath.base_of_pvar struct_pvar struct_type in
        let field_access = AccessPath.FieldAccess name in
        let full_path : AccessPath.t = access_base, [field_access] in
        Ident.Map.add id ((EdgeExp.Access full_path), typ) graph_data.ident_map,
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
      let access = EdgeExp.Access (AccessPath.of_pvar pvar typ) in
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

    let rec substitute edge_data exp = match exp with
    | EdgeExp.Access access -> LTS.EdgeData.get_assignment_rhs edge_data access
    | EdgeExp.BinOp (op, lexp, rexp) -> EdgeExp.BinOp (op, substitute edge_data lexp, substitute edge_data rexp)
    | EdgeExp.UnOp (op, subexp, typ) -> EdgeExp.UnOp (op, substitute edge_data subexp, typ)
    | EdgeExp.Call (ret_typ, procname, args, loc) -> (
      let args = List.map args ~f:(fun (arg, typ) -> (substitute edge_data arg, typ)) in
      EdgeExp.Call (ret_typ, procname, args, loc)
    )
    | EdgeExp.Max args -> EdgeExp.Max (List.map args ~f:(substitute edge_data))
    | EdgeExp.Min args -> EdgeExp.Max (List.map args ~f:(substitute edge_data))
    | _ -> exp
    in

    debug_log "@[<v4>Processing call arguments:@,";
    let args, arg_norms = List.foldi args ~f:(fun idx (args, norms) (arg, arg_typ) ->
      debug_log "@[<v2>(%d) %a : %a@," idx Exp.pp arg Typ.(pp Pp.text) arg_typ;
      let arg_hil_exp = HilExp.of_sil ~include_array_indexes:true 
        ~f_resolve_id:ae_id_resolver ~add_deref:false arg arg_typ
      in
      let arg_edge_exp = EdgeExp.of_hil_exp arg_hil_exp |> substitute graph_data.edge_data in
      debug_log "Transformed EdgeExp: %a@," EdgeExp.pp arg_edge_exp;

      if Typ.is_int arg_typ then (
        let simplified_arg_edge_exp = EdgeExp.simplify arg_edge_exp in
        debug_log "Integer argument type, simplified: %a@]@," EdgeExp.pp simplified_arg_edge_exp;
        let arg_norms = EdgeExp.get_access_exp_set simplified_arg_edge_exp in
        (simplified_arg_edge_exp, arg_typ) :: args, EdgeExp.Set.union arg_norms norms
      ) else (
        debug_log "Non-integer argument type, ignoring@]@,";
        (arg_edge_exp, arg_typ) :: args, norms
      )
    ) ~init:([], EdgeExp.Set.empty)
    in
    debug_log "@]@,";

    let args = List.rev args in
    let call = EdgeExp.Call (ret_typ, callee_pname, args, loc) in

    debug_log "@[<v4>Loading call summary@,";
    let payload_opt = graph_data.proc_data.analysis_data.analyze_dependency callee_pname in
    let call_summaries = match payload_opt with
    | Some (_, payload) -> (
      debug_log "Payload exists, substituting return bound@]@,";
      let subst_ret_bound = match payload.return_bound with
      | Some ret_bound -> Some (EdgeExp.subst ret_bound args payload.formal_map)
      | None -> None
      in
      let summary = { payload with return_bound = subst_ret_bound } in
      Location.Map.add loc summary graph_data.proc_data.call_summaries
    )
    | None -> (
      debug_log "Payload missing, ignoring@]@,";
      graph_data.proc_data.call_summaries
    )
    in

    debug_log "@]@,";
    { graph_data with
      ident_map = Ident.Map.add ret_id (call, ret_typ) graph_data.ident_map;
      (* type_map = PvarMap.add (Pvar.mk_abduced_ret callee_pname loc) ret_typ graph_data.type_map; *)

      edge_data = { graph_data.edge_data with 
        calls = EdgeExp.Set.add call graph_data.edge_data.calls
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


let construct : Tenv.t -> Procdesc.t -> LooperSummary.t InterproceduralAnalysis.t -> procedure_data = 
  fun tenv proc_desc summary -> (
    debug_log "@[<v>";

    let proc_name = Procdesc.get_proc_name proc_desc in
    let begin_loc = Procdesc.get_loc proc_desc in
    let start_node = Procdesc.get_start_node proc_desc in
    let lts_start_node = LTS.Node.Start (proc_name, begin_loc) in

    let locals = Procdesc.get_locals proc_desc in
    let formals = Procdesc.get_pvar_formals proc_desc in

    let proc_name = Procdesc.get_proc_name proc_desc in
    let _, type_map = List.fold locals ~init:(Pvar.Set.empty, PvarMap.empty) ~f:
    (fun (locals, type_map) (local : ProcAttributes.var_data) ->
      let pvar = Pvar.mk local.name proc_name in
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
      tenv = tenv;

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
