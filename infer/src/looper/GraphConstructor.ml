(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
open LooperUtils
module F = Format
module L = Logging
module LTS = LabeledTransitionSystem
module InstrCFG = ProcCfg.NormalOneInstrPerNode

let console_log : ('a, F.formatter, unit) format -> 'a = fun fmt -> F.printf fmt

type procedure_data =
  { nodes: LTS.NodeSet.t
  ; edges: LTS.EdgeSet.t
  ; norms: EdgeExp.Set.t
  ; formals: AccessPath.BaseSet.t
  ; analysis_data: LooperSummary.t InterproceduralAnalysis.t
  ; call_summaries: LooperSummary.model_summary Location.Map.t
  ; lts: LTS.t }

type construction_temp_data =
  { last_node: LTS.Node.t
  ; last_split_info: (LTS.Node.t * Sil.if_kind) option
  ; branch_not_reachable: bool
  ; loop_heads: LTS.Node.t list
  ; edge_data: LTS.EdgeData.t
  ; ident_map: EdgeExp.ValuePair.t Ident.Map.t
  ; node_map: LTS.Node.t Procdesc.NodeMap.t
  ; potential_norms: EdgeExp.Set.t
  ; loop_modified: AccessExpressionSet.t
  ; scope_locals: AccessExpressionSet.t list
  ; locals: AccessExpressionSet.t AccessPath.BaseMap.t
  ; tenv: Tenv.t
  ; exe_env: Exe_env.t
  ; proc_desc: Procdesc.t
  ; procname: Procname.t
  ; active_prover: Provers.prover_data }

let pp_nodekind kind =
  match kind with
  | Procdesc.Node.Start_node ->
      "Start_node"
  | Procdesc.Node.Exit_node ->
      "Exit_node"
  | Procdesc.Node.Stmt_node stmt ->
      F.asprintf "Stmt_node(%a)" Procdesc.Node.pp_stmt stmt
  | Procdesc.Node.Join_node ->
      "Join_node"
  | Procdesc.Node.Prune_node (branch, ifkind, _) ->
      F.asprintf "Prune_node(%B, %a)" branch Sil.pp_if_kind ifkind
  | Procdesc.Node.Skip_node string ->
      F.asprintf "Skip_node (%s)" string


let is_infer_join_node node =
  match Procdesc.Node.get_kind node with Procdesc.Node.Join_node -> true | _ -> false


let is_exit_node node =
  match Procdesc.Node.get_kind node with Procdesc.Node.Exit_node -> true | _ -> false


let is_ignored_function procname =
  match Procname.get_method procname with "__infer_skip" -> true | _ -> false


let is_loop_if_kind kind = match kind with Sil.Ik_bexp _ | Sil.Ik_if _ -> false | _ -> true

let exec_instr :
    construction_temp_data * procedure_data -> Sil.instr -> construction_temp_data * procedure_data
    =
 fun (graph_data, proc_data) instr ->
  let proc_ret_type = Procdesc.get_ret_type graph_data.proc_desc in
  let integer_type_widths =
    Exe_env.get_integer_type_widths graph_data.exe_env graph_data.procname
  in
  let test_resolver var =
    match var with
    | Var.LogicalVar id -> (
      match Ident.Map.find_opt id graph_data.ident_map with
      | Some value_pair ->
          (Some value_pair, false)
      | None ->
          (* L.die InternalError "Missing mapped expression for '%a' identifier" Ident.pp id ; *)
          debug_log "Missing mapped expression for '%a' identifier" Ident.pp id ;
          (None, true) )
    | Var.ProgramVar _ ->
        (None, false)
  in
  let ae_id_resolver var =
    match var with
    | Var.LogicalVar id -> (
      match Ident.Map.find_opt id graph_data.ident_map with
      | Some (EdgeExp.ValuePair.V exp) -> (
        match exp with
        | EdgeExp.T.Access path ->
            Some path
        | _ ->
            (* Replace idents mapped to more complex expressions later.
               * HilExp.of_sil signature requires this function to return
               * access expression type. More complex expressions occur due
               * to return values of function calls *)
            None )
      | Some (EdgeExp.ValuePair.P _) ->
          assert
            (* Figure this out later, too complicated for now. Will probably
             * have to write my own conversion functions for SIL -> HIL
             * because of this... *)
            false
      | None ->
          (* L.die InternalError "Missing mapped expression for '%a' identifier" Ident.pp id ; *)
          debug_log "Missing mapped expression for '%a' identifier" Ident.pp id ;
          None )
    | Var.ProgramVar _ ->
        None
  in
  let is_top_scope_local local_base graph_data =
    List.for_all graph_data.scope_locals ~f:(fun scope ->
        let f access = AccessPath.equal_base (HilExp.AccessExpression.get_base access) local_base in
        not (AccessExpressionSet.exists f scope) )
  in
  let add_local access locals =
    let access_base = HilExp.AccessExpression.get_base access in
    AccessPath.BaseMap.update access_base
      (fun key_opt ->
        match key_opt with
        | Some access_set ->
            Some (AccessExpressionSet.add access access_set)
        | None ->
            Some (AccessExpressionSet.singleton access) )
      locals
  in
  let is_loop_prune (kind : Sil.if_kind) =
    match kind with Ik_dowhile | Ik_for | Ik_while -> true | _ -> false
  in
  let in_loop = not (List.is_empty graph_data.loop_heads) in
  (* Can't make it the EdgeExp module function due to cyclical dependency *)
  let rec substitute_call_args edge_data args =
    List.fold args ~init:([], [], []) ~f:(fun (lb_acc, ub_acc, typ_acc) (arg, arg_typ) ->
        match substitute_assignments edge_data arg with
        | EdgeExp.ValuePair.V value ->
            (value :: lb_acc, value :: ub_acc, arg_typ :: typ_acc)
        | EdgeExp.ValuePair.P (lb, ub) ->
            (lb :: lb_acc, ub :: ub_acc, arg_typ :: typ_acc) )
  and substitute_assignments edge_data exp =
    let process_min_max_args args ~f =
      let subst_args args =
        EdgeExp.Set.fold
          (fun arg (lb_set, ub_set) ->
            match substitute_assignments edge_data arg with
            | EdgeExp.ValuePair.V value ->
                (EdgeExp.Set.add value lb_set, EdgeExp.Set.add value ub_set)
            | EdgeExp.ValuePair.P (lb, ub) ->
                (EdgeExp.Set.add lb lb_set, EdgeExp.Set.add ub ub_set) )
          args
          (EdgeExp.Set.empty, EdgeExp.Set.empty)
      in
      let lb_set, ub_set = subst_args args in
      if EdgeExp.Set.equal lb_set ub_set then EdgeExp.ValuePair.V (f lb_set)
      else EdgeExp.ValuePair.P (f lb_set, f ub_set)
    in
    match exp with
    | EdgeExp.T.Access access ->
        LTS.EdgeData.get_assignment_rhs edge_data access
    | EdgeExp.T.BinOp (op, lexp, rexp) ->
        let lexp_subst = substitute_assignments edge_data lexp in
        let rexp_subst = substitute_assignments edge_data rexp in
        EdgeExp.ValuePair.create_binop op lexp_subst rexp_subst
    | EdgeExp.T.Cast (typ, exp) -> (
        debug_log "CAST: %a@," EdgeExp.pp exp ;
        match substitute_assignments edge_data exp with
        | EdgeExp.ValuePair.V value ->
            EdgeExp.ValuePair.V (EdgeExp.T.Cast (typ, value))
        | EdgeExp.ValuePair.P (lb, ub) ->
            EdgeExp.ValuePair.P (EdgeExp.T.Cast (typ, lb), EdgeExp.T.Cast (typ, ub)) )
    | EdgeExp.T.UnOp (op, subexp, typ) -> (
      match substitute_assignments edge_data subexp with
      | EdgeExp.ValuePair.V value ->
          EdgeExp.ValuePair.V (EdgeExp.T.UnOp (op, value, typ))
      | EdgeExp.ValuePair.P (lb, ub) ->
          EdgeExp.ValuePair.P (EdgeExp.T.UnOp (op, lb, typ), EdgeExp.T.UnOp (op, ub, typ)) )
    | EdgeExp.T.Call (ret_typ, procname, args, loc) ->
        let lb_args, ub_args, arg_types = substitute_call_args edge_data args in
        if List.equal EdgeExp.equal lb_args ub_args then
          EdgeExp.ValuePair.V
            (EdgeExp.T.Call (ret_typ, procname, List.zip_exn lb_args arg_types, loc))
        else
          EdgeExp.ValuePair.P
            ( EdgeExp.T.Call (ret_typ, procname, List.zip_exn lb_args arg_types, loc)
            , EdgeExp.T.Call (ret_typ, procname, List.zip_exn ub_args arg_types, loc) )
    | EdgeExp.T.Max args ->
        process_min_max_args args ~f:(fun args -> EdgeExp.T.Max args)
    | EdgeExp.T.Min args ->
        process_min_max_args args ~f:(fun args -> EdgeExp.T.Min args)
    | _ ->
        EdgeExp.ValuePair.V exp
  in
  match instr with
  | Prune (cond, loc, branch, kind) ->
      (* debug_log "[PRUNE (%s)] (%a) | %a\n" (Sil.if_kind_to_string kind) Location.pp loc Exp.pp cond; *)
      let edge_exp_cond_pair =
        EdgeExp.of_sil_exp ~include_array_indexes:true ~f_resolve_id:ae_id_resolver ~test_resolver
          ~add_deref:false cond (Typ.mk (Tint IBool))
      in
      debug_log
        "@[<v4>[PRUNE] %a@,Prune type: %a@,Branch: %B@,Exp condition: %a@,EdgeExp condition: %a@,"
        Location.pp loc Sil.pp_if_kind kind branch Exp.pp cond EdgeExp.ValuePair.pp
        edge_exp_cond_pair ;
      let is_norm_modified norm =
        match norm with
        | EdgeExp.T.Access access ->
            AccessExpressionSet.mem access graph_data.loop_modified
        | _ ->
            false
      in
      let normalized_cond_opt, condition_norm_opt =
        match edge_exp_cond_pair with
        | EdgeExp.ValuePair.V cond ->
            EdgeExp.normalize_condition cond graph_data.tenv
        | EdgeExp.ValuePair.P (_, ub_cond) ->
            EdgeExp.normalize_condition ub_cond graph_data.tenv
      in
      debug_log "Normalized condition: " ;
      let condition_always_false =
        match normalized_cond_opt with
        | Some condition ->
            debug_log "%a@," EdgeExp.pp condition ;
            EdgeExp.always_false condition graph_data.tenv graph_data.active_prover
        | None ->
            debug_log "None@," ;
            false
      in
      let graph_data = {graph_data with branch_not_reachable= condition_always_false} in
      let graph_data, proc_data =
        if branch then (
          (* Derive norm from prune condition.
             * [x > y] -> [x - y] > 0
             * [x >= y] -> [x - y + 1] > 0 *)
          (* TODO: Confirm that the conversion is truly producing
             lower/upper bound for the purpose of norm extraction from
             the loop condition.
             Also, do we need the lower bound condition for anything? *)
          let edge_data =
            match normalized_cond_opt with
            | Some normalized_cond
              when (not (EdgeExp.is_zero normalized_cond)) && not (EdgeExp.is_one normalized_cond)
              ->
                LTS.EdgeData.add_condition graph_data.edge_data normalized_cond
            | _ ->
                graph_data.edge_data
          in
          debug_log "Condition norm: %s@,"
            (Option.value_map condition_norm_opt ~default:"None" ~f:(fun condition ->
                 EdgeExp.to_string condition ) ) ;
          (* Add condition only on TRUE branch for now to avoid dealing with boolean
             expression simplification due to Prune node merging in LTS graphs.
             We will probably need the FALSE branch conditions later too *)
          let graph_data =
            { graph_data with
              edge_data
            ; scope_locals= [AccessExpressionSet.empty] @ graph_data.scope_locals }
          in
          let loop_prune = is_loop_prune kind in
          debug_log "is_loop_prune: %B@,in_loop: %B@," loop_prune in_loop ;
          match condition_norm_opt with
          | Some condition_norm when loop_prune || in_loop ->
              let new_norm = EdgeExp.simplify condition_norm in
              (* let norms = EdgeExp.Set.add new_norm proc_data.norms in
                 let edge_data = LTS.EdgeData.add_condition_norm graph_data.edge_data new_norm in
                 ({graph_data with edge_data}, {proc_data with norms}) *)
              let norm_modified = is_norm_modified new_norm in
              debug_log "norm_modified: %B@," norm_modified ;
              if (not loop_prune) && not norm_modified then
                (* Prune on loop path but not loop head. Norm is only potential,
                   * must be confirmed by increment/decrement on this loop path *)
                let potential_norms = EdgeExp.Set.add new_norm graph_data.potential_norms in
                ({graph_data with potential_norms}, proc_data)
              else
                (* let edge_data = graph_data.edge_data. *)
                let norms = EdgeExp.Set.add new_norm proc_data.norms in
                let edge_data = LTS.EdgeData.add_condition_norm graph_data.edge_data new_norm in
                ({graph_data with edge_data}, {proc_data with norms})
          | _ ->
              (graph_data, proc_data) )
        else (graph_data, proc_data)
      in
      let graph_data =
        { graph_data with
          edge_data= {graph_data.edge_data with branch_info= Some (kind, branch, loc)} }
      in
      debug_log "@]@," ;
      (graph_data, proc_data)
  | Store {e1= Lvar lhs_pvar; typ; e2; loc} when Pvar.is_ssa_frontend_tmp lhs_pvar ->
      (* TODO: not sure when this case occurs, but starvation checker handles it, need to check later *)
      debug_log "@[<v4>[STORE] (%a) | %a = %a : %a@," Location.pp loc
        Pvar.(pp Pp.text)
        lhs_pvar Exp.pp e2
        Typ.(pp Pp.text)
        typ ;
      debug_log "SSA frontend temporary variable store@]@," ;
      assert false
  | Store {e1= Lindex (Lvar base, _)} when Pvar.is_global base ->
      (* Ignore these assignments for now. Initialization of huge global arrays
       * cause incredible slowdown currently because Infer invokes Store instruction
       * for each initialization value *)
      (graph_data, proc_data)
  | Store {e1= lhs; typ; e2= rhs; loc} ->
      debug_log "@[<v4>[STORE] %a@,Type: %a@,Exp: %a = %a@," Location.pp loc
        Typ.(pp Pp.text)
        typ Exp.pp lhs Exp.pp rhs ;
      let rhs_edge_exp_pair =
        EdgeExp.of_sil_exp ~include_array_indexes:true ~f_resolve_id:ae_id_resolver ~test_resolver
          ~add_deref:false rhs typ
      in
      let lhs_edge_exp, lhs_is_return =
        match
          EdgeExp.of_sil_exp ~include_array_indexes:true ~f_resolve_id:ae_id_resolver ~test_resolver
            ~add_deref:true lhs typ
        with
        | EdgeExp.ValuePair.V e ->
            EdgeExp.map_accesses e ~init:false ~f:(fun access acc ->
                if HilExp.AccessExpression.is_return_var access then
                  (* Adjust the type of return variable based on the return type
                     of the analyzed procedure. There are some inconsistencies otherwise *)
                  let var, _ = HilExp.AccessExpression.get_base access in
                  let new_base = (var, proc_ret_type) in
                  let access =
                    HilExp.AccessExpression.replace_base new_base access
                      ~remove_deref_after_base:false
                  in
                  (EdgeExp.T.Access access, true)
                else (EdgeExp.T.Access access, acc) )
        | pair ->
            L.die InternalError
              "Left-hand side expression of\n\
              \      Store instruction cannot be EdgeExp.ValuePair.P: %a" EdgeExp.ValuePair.pp pair
      in
      debug_log "@[<v4>EdgeExp: %a = %a" EdgeExp.pp lhs_edge_exp EdgeExp.ValuePair.pp
        rhs_edge_exp_pair ;
      let check_casts exp_pair =
        let check_value exp =
          match exp with
          | EdgeExp.T.Cast (typ, exp) -> (
              debug_log "@,Cast to: %a, Subexp: %a@," Typ.(pp Pp.text) typ EdgeExp.pp exp ;
              match EdgeExp.get_typ graph_data.tenv exp with
              | Some type_before_cast ->
                  debug_log "Type before cast: %a" Typ.(pp Pp.text) type_before_cast
              | None ->
                  debug_log "Type before cast: unknown (EdgeExp.get_typ not fully implemented)" )
          | _ ->
              ()
        in
        match exp_pair with
        | EdgeExp.ValuePair.V exp ->
            check_value exp
        | EdgeExp.ValuePair.P (lb, ub) ->
            check_value lb ;
            check_value ub
      in
      check_casts rhs_edge_exp_pair ;
      debug_log "@]@," ;
      let lhs_access =
        match lhs_edge_exp with
        | EdgeExp.T.Access access ->
            access
        | _ ->
            L.die InternalError
              "Left-hand side expression of Store instruction is not an AccessExpression: %a"
              EdgeExp.pp lhs_edge_exp
      in
      let lhs_access_base = HilExp.AccessExpression.get_base lhs_access in
      let simplify value =
        (value |> EdgeExp.simplify |> EdgeExp.remove_casts_of_consts) integer_type_widths
      in
      let process_rhs_value value =
        match value with
        | EdgeExp.T.Call (_, _, _, loc) as call -> (
          match Location.Map.find_opt loc proc_data.call_summaries with
          | Some (LooperSummary.Real summary) -> (
            match summary.return_bound with Some pair -> pair | None -> assert false )
          | Some (LooperSummary.Model model) -> (
            match model.return_bound with Some pair -> pair | None -> assert false )
          | None ->
              EdgeExp.ValuePair.V (call |> simplify) )
        | _ ->
            EdgeExp.ValuePair.map_accesses value ~f:(fun access ->
                LTS.EdgeData.get_assignment_rhs graph_data.edge_data access )
            |> EdgeExp.ValuePair.map ~f:simplify
      in
      debug_log "@[<v2>[Pre-Merge] EdgeExp: %a = @,%a@]@," EdgeExp.pp lhs_edge_exp
        EdgeExp.ValuePair.pp_multiline rhs_edge_exp_pair ;
      (* TODO: Investigate if some of these cases can actually
         occur in reality or not, seems weird *)
      let assignment_rhs =
        match rhs_edge_exp_pair with
        | EdgeExp.ValuePair.V rhs_value ->
            process_rhs_value rhs_value
        | EdgeExp.ValuePair.P (lb, ub) ->
            let x, y = (process_rhs_value lb, process_rhs_value ub) in
            debug_log "@[<v2>RHS LB: @,%a@]@," EdgeExp.ValuePair.pp_multiline x ;
            debug_log "@[<v2>RHS UB: @,%a@]@," EdgeExp.ValuePair.pp_multiline y ;
            EdgeExp.ValuePair.merge x y
      in
      debug_log "@[<v2>[Post-Merge] EdgeExp: %a = @,%a@]@," EdgeExp.pp lhs_edge_exp
        EdgeExp.ValuePair.pp_multiline assignment_rhs ;
      (* Checks if its possible to confirm some potential norm due to it's
       * decrement on this edge *)
      let rec check_norms lexp rexp potential_norms =
        match rexp with
        | EdgeExp.ValuePair.V value -> (
          match value with
          | EdgeExp.T.BinOp
              ((Binop.PlusA _ | Binop.MinusA _), rhs_subexp, EdgeExp.T.Const (Const.Cint _))
            when EdgeExp.equal lexp rhs_subexp && EdgeExp.Set.mem rhs_subexp potential_norms ->
              (EdgeExp.Set.remove rhs_subexp potential_norms, EdgeExp.Set.singleton rhs_subexp)
          | _ ->
              (potential_norms, EdgeExp.Set.empty) )
        | EdgeExp.ValuePair.P (lb, ub) ->
            let potential_norms, lb_norms =
              check_norms lexp (EdgeExp.ValuePair.V lb) potential_norms
            in
            let potential_norms, ub_norms =
              check_norms lexp (EdgeExp.ValuePair.V ub) potential_norms
            in
            (potential_norms, EdgeExp.Set.union lb_norms ub_norms)
      in
      let potential_norms, new_norms =
        check_norms lhs_edge_exp assignment_rhs graph_data.potential_norms
      in
      let locals, new_norms =
        if lhs_is_return then (
          let ret_typ = HilExp.AccessExpression.get_typ lhs_access graph_data.tenv in
          debug_log "Return type: %s@,"
            (Option.value_map ret_typ ~default:"None" ~f:(fun v -> Typ.to_string v)) ;
          debug_log "LHS is a return variable, adding to norms@," ;
          (add_local lhs_access graph_data.locals, EdgeExp.Set.add lhs_edge_exp new_norms) )
        else (graph_data.locals, new_norms)
      in
      (* let locals, new_norms =
           if HilExp.AccessExpression.is_return_var lhs_access then (
             let ret_typ = HilExp.AccessExpression.get_typ lhs_access graph_data.tenv in
             debug_log "Proc return type: %a@," Typ.(pp Pp.text) proc_ret_type ;
             debug_log "Return type: %s@,"
               (Option.value_map ret_typ ~default:"None" ~f:(fun v -> Typ.to_string v)) ;
             let var, _ = HilExp.AccessExpression.get_base lhs_access in
             let new_base = (var, proc_ret_type) in
             let lhs_access =
               HilExp.AccessExpression.replace_base new_base lhs_access ~remove_deref_after_base:false
             in
             debug_log "LHS is a return variable, adding to norms@," ;
             (add_local lhs_access graph_data.locals, EdgeExp.Set.add lhs_edge_exp new_norms) )
           else (graph_data.locals, new_norms)
         in *)
      (* let is_lhs_top_scope_local =
           List.for_all graph_data.scope_locals ~f:(fun scope ->
               let f access =
                 AccessPath.equal_base (HilExp.AccessExpression.get_base access) lhs_access_base
               in
               AccessExpressionSet.exists f scope )
         in *)
      (* Only base of access expression stripped of any other sub-accesses *)
      let lhs_access_stripped = HilExp.AccessExpression.base lhs_access_base in
      (* Always add LHS access to the set of local variables. It will be removed
       * when exiting current scope if it's not a top-scope local *)
      let locals = add_local lhs_access locals in
      let scope_locals =
        if
          (not (HilExp.AccessExpression.equal lhs_access_stripped lhs_access))
          && AccessPath.BaseMap.mem lhs_access_base locals
          && not (is_top_scope_local lhs_access_base graph_data)
        then
          match graph_data.scope_locals with
          | scope :: higher_scopes ->
              [AccessExpressionSet.add lhs_access scope] @ higher_scopes
          | [] ->
              [AccessExpressionSet.singleton lhs_access]
        else graph_data.scope_locals
      in
      (* Check if the access base of LHS expression is a formal pointer and add the access
       * expression to norms if it is. We need to track pointer formals due to possible side-effects *)
      let lhs_access_base_typ = snd lhs_access_base in
      let new_norms =
        if
          AccessPath.BaseSet.mem lhs_access_base proc_data.formals
          && Typ.is_pointer lhs_access_base_typ
          && EdgeExp.is_integer_type typ
        then
          match lhs_access with
          | HilExp.AccessExpression.FieldOffset (Dereference _, _)
          | HilExp.AccessExpression.Dereference _ ->
              debug_log
                "Formal base '%a' is a pointer: %a. Adding access expression '%a' to norms.@,"
                AccessPath.pp_base lhs_access_base
                Typ.(pp Pp.text)
                lhs_access_base_typ HilExp.AccessExpression.pp lhs_access ;
              EdgeExp.Set.add lhs_edge_exp new_norms
          | _ ->
              new_norms
        else new_norms
      in
      let norms = EdgeExp.Set.union proc_data.norms new_norms in
      let edge_data = LTS.EdgeData.add_assignment graph_data.edge_data lhs_access assignment_rhs in
      let loop_modified =
        if in_loop then AccessExpressionSet.add lhs_access graph_data.loop_modified
        else graph_data.loop_modified
      in
      let graph_data =
        {graph_data with locals; scope_locals; potential_norms; edge_data; loop_modified}
      in
      debug_log "Norms: " ;
      EdgeExp.Set.iter (fun norm -> debug_log "%a | " EdgeExp.pp norm) norms ;
      debug_log "@,@]@," ;
      (graph_data, {proc_data with norms})
  | Load {id; e; typ; loc} ->
      debug_log "@[<v4>[LOAD] %a@,Type: %a@,Exp: %a = %a@," Location.pp loc
        Typ.(pp Pp.text)
        typ Ident.pp id Exp.pp e ;
      let rhs_edge_exp_pair =
        EdgeExp.of_sil_exp ~include_array_indexes:true ~f_resolve_id:ae_id_resolver ~test_resolver
          ~add_deref:true e typ
      in
      debug_log "RHS EdgeExp: %a = %a@," Ident.pp id EdgeExp.ValuePair.pp rhs_edge_exp_pair ;
      (* TODO: of_sil, of_hil_exp should work with assignment_rhs
       * and return it so we can add it to the ident_map instead
       * of just wrapping artifically *)
      let ident_map = Ident.Map.add id rhs_edge_exp_pair graph_data.ident_map in
      debug_log "@]@," ;
      ({graph_data with ident_map}, proc_data)
  | Call (_, Exp.Const (Const.Cfun name), _, loc, _) when is_ignored_function name ->
      debug_log "@[<v4>[CALL] %a@,Procedure name: %a@,Ignoring function call@]@," Location.pp loc
        Procname.pp name ;
      (graph_data, proc_data)
  | Call ((ret_id, ret_typ), Exp.Const (Const.Cfun callee_pname), args, loc, _) ->
      debug_log "@[<v4>[CALL] %a@, Procedure name: %a@," Location.pp loc Procname.pp callee_pname ;
      debug_log "@[<v4>Processing call arguments:@," ;
      let process_func_arg idx (lb_acc, ub_acc, types_acc, accesses_acc) (arg, arg_typ) =
        debug_log "@[<v2>(%d) Exp: %a : %a@," idx Exp.pp arg Typ.(pp Pp.text) arg_typ ;
        let arg_edge_exp =
          EdgeExp.of_sil_exp ~include_array_indexes:true ~f_resolve_id:ae_id_resolver ~test_resolver
            ~add_deref:false arg arg_typ
        in
        debug_log "EdgeExp: %a : %a@," EdgeExp.ValuePair.pp arg_edge_exp Typ.(pp Pp.text) arg_typ ;
        (* We don't have to check monotonicity here. We're simply
           substituting assignments to get lowest lower bound
           and highest upper bound for every argument *)
        let subst_pair_arg =
          match arg_edge_exp with
          | EdgeExp.ValuePair.V value ->
              substitute_assignments graph_data.edge_data value
          | EdgeExp.ValuePair.P (lb, ub) ->
              let lb_subst = substitute_assignments graph_data.edge_data lb in
              let ub_subst = substitute_assignments graph_data.edge_data ub in
              EdgeExp.ValuePair.merge lb_subst ub_subst
        in
        debug_log "Substituted: %a@]@," EdgeExp.ValuePair.pp subst_pair_arg ;
        let types_acc = arg_typ :: types_acc in
        match subst_pair_arg with
        | EdgeExp.ValuePair.V v ->
            let accesses = AccessExpressionSet.union accesses_acc (EdgeExp.get_accesses v) in
            (v :: lb_acc, v :: ub_acc, types_acc, accesses)
        | EdgeExp.ValuePair.P (lb, ub) ->
            let lb_accesses = EdgeExp.get_accesses lb in
            let ub_accesses = EdgeExp.get_accesses ub in
            let accesses =
              AccessExpressionSet.union accesses_acc
                (AccessExpressionSet.union lb_accesses ub_accesses)
            in
            (lb :: lb_acc, ub :: ub_acc, types_acc, accesses)
      in
      let lb_args_rev, ub_args_rev, arg_types_rev, arg_accesses =
        List.foldi args ~f:process_func_arg ~init:([], [], [], AccessExpressionSet.empty)
      in
      debug_log "@]@," ;
      let lb_args, ub_args, arg_types =
        (List.rev lb_args_rev, List.rev ub_args_rev, List.rev arg_types_rev)
      in
      let args_lb_ub_equal = List.equal EdgeExp.equal lb_args ub_args in
      let extract_norms arg_list =
        debug_log "@[<v4>Extracting norms from call arguments@," ;
        let norms =
          List.fold arg_list ~init:EdgeExp.Set.empty ~f:(fun norms (arg, arg_typ) ->
              if EdgeExp.is_integer_type arg_typ then (
                (* let simplified_arg = EdgeExp.simplify arg in *)
                (* debug_log "Integer argument type, simplified: %a@," EdgeExp.pp simplified_arg ; *)
                let arg_norms = EdgeExp.get_access_exp_set arg in
                debug_log "New norms: " ;
                EdgeExp.Set.iter (fun norm -> debug_log "%a, " EdgeExp.pp norm) arg_norms ;
                debug_log "@," ;
                EdgeExp.Set.union arg_norms norms )
              else (
                debug_log "Non-integer argument type, ignoring@," ;
                norms ) )
        in
        debug_log "@]@," ;
        norms
      in
      let create_value_call args =
        let subst_args = List.zip_exn args arg_types in
        ((ret_typ, callee_pname, subst_args, loc), extract_norms subst_args)
      in
      let call_pair, call_pair_exp, arg_norms =
        if args_lb_ub_equal then
          let call_tuple, norms = create_value_call lb_args in
          (EdgeExp.CallPair.V call_tuple, EdgeExp.ValuePair.V (EdgeExp.T.Call call_tuple), norms)
        else
          let lb_value_call, lb_norms = create_value_call lb_args in
          let ub_value_call, ub_norms = create_value_call ub_args in
          ( EdgeExp.CallPair.P (lb_value_call, ub_value_call)
          , EdgeExp.ValuePair.P (EdgeExp.T.Call lb_value_call, EdgeExp.T.Call ub_value_call)
          , EdgeExp.Set.union lb_norms ub_norms )
      in
      debug_log "@[<v4>Loading call summary@," ;
      let rec extract_access exp =
        match exp with
        | EdgeExp.T.Access lhs_access ->
            lhs_access
        | EdgeExp.T.Max args when Int.equal (EdgeExp.Set.cardinal args) 1 ->
            extract_access (EdgeExp.Set.min_elt args)
        | exp ->
            L.die InternalError
              "Unsupported formal expression '%a',\n            access expression expected"
              EdgeExp.pp exp
      in
      let payload_opt = proc_data.analysis_data.analyze_dependency callee_pname in
      let call_summaries, return_bound, edge_data =
        match payload_opt with
        | Some payload ->
            (* We have to check monotonicity here to correctly substitute
               lower or upper bound of each argument to the payload bounds *)
            let lb_args = List.zip_exn lb_args arg_types in
            let ub_args = List.zip_exn ub_args arg_types in
            debug_log "Payload exists, substituting return bound@," ;
            let subst_ret_bound_opt =
              match payload.return_bound with
              | Some (EdgeExp.ValuePair.P (lb_ret_bound, ub_ret_bound)) ->
                  let lb_subst = EdgeExp.subst lb_ret_bound lb_args payload.formal_map in
                  let ub_subst = EdgeExp.subst ub_ret_bound ub_args payload.formal_map in
                  if EdgeExp.equal lb_subst ub_subst then Some (EdgeExp.ValuePair.V ub_subst)
                  else Some (EdgeExp.ValuePair.P (lb_subst, ub_subst))
              | Some (EdgeExp.ValuePair.V ret_bound) ->
                  (* TODO: We should check if lb_args == ub_args and create a ret_bound pair if not *)
                  if args_lb_ub_equal then
                    let subst_bound = EdgeExp.subst ret_bound ub_args payload.formal_map in
                    Some (EdgeExp.ValuePair.V subst_bound)
                  else
                    let lb_subst = EdgeExp.subst ret_bound lb_args payload.formal_map in
                    let ub_subst = EdgeExp.subst ret_bound ub_args payload.formal_map in
                    if EdgeExp.equal lb_subst ub_subst then Some (EdgeExp.ValuePair.V ub_subst)
                    else Some (EdgeExp.ValuePair.P (lb_subst, ub_subst))
              | None ->
                  None
            in
            debug_log "@[<v2>Substituting formals bounds:@," ;
            debug_log "FormalMap: %a@," FormalMap.pp payload.formal_map ;
            let edge_data =
              EdgeExp.Map.fold
                (fun formal (lb, ub) acc ->
                  debug_log "Formal: %a  --->  [%a, %a]@," EdgeExp.pp formal EdgeExp.pp lb
                    EdgeExp.pp ub ;
                  (* TODO: This is probably not a good approach. Maybe we should
                     use some kind of access path sets for left hand side? Seems
                     that different kind of analysis type would be more suitable *)
                  let lb_lhs_subst = EdgeExp.subst formal lb_args payload.formal_map in
                  let ub_lhs_subst = EdgeExp.subst formal ub_args payload.formal_map in
                  let lb_lhs_subst_access = extract_access lb_lhs_subst in
                  let ub_lhs_subst_access = extract_access ub_lhs_subst in
                  let lb_subst = EdgeExp.subst lb lb_args payload.formal_map in
                  let ub_subst = EdgeExp.subst ub ub_args payload.formal_map in
                  let bound =
                    if EdgeExp.equal lb_subst ub_subst then EdgeExp.ValuePair.V lb_subst
                    else EdgeExp.ValuePair.P (lb_subst, ub_subst)
                  in
                  debug_log "[Substituted] Formal: [%a, %a]  --->  [%a, %a]@,"
                    HilExp.AccessExpression.pp lb_lhs_subst_access HilExp.AccessExpression.pp
                    ub_lhs_subst_access EdgeExp.pp lb_subst EdgeExp.pp ub_subst ;
                  let acc = LTS.EdgeData.add_assignment acc lb_lhs_subst_access bound in
                  LTS.EdgeData.add_assignment acc ub_lhs_subst_access bound )
                payload.formal_bounds graph_data.edge_data
            in
            debug_log "@]@," ;
            let real_summary =
              LooperSummary.Real {payload with return_bound= subst_ret_bound_opt}
            in
            let call_summaries = Location.Map.add loc real_summary proc_data.call_summaries in
            let return_bound_pair = Option.value subst_ret_bound_opt ~default:call_pair_exp in
            (call_summaries, return_bound_pair, edge_data)
        | None -> (
            let arg_pairs = EdgeExp.ValuePair.make_list lb_args ub_args in
            debug_log "callee_pname: %a@," Procname.pp callee_pname ;
            match LooperCostModels.Call.get_model callee_pname arg_pairs graph_data.exe_env with
            | Some call_model ->
                (* debug_log "[CostModel] Model cost: %a@," LooperSummary.Model.pp call_model ; *)
                let edge_data =
                  EdgeExp.Map.fold
                    (fun ptr_arg (lb, ub) acc ->
                      debug_log "Side-effect: %a  --->  [%a, %a]@," EdgeExp.pp ptr_arg EdgeExp.pp lb
                        EdgeExp.pp ub ;
                      let arg_access =
                        HilExp.AccessExpression.dereference (extract_access ptr_arg)
                      in
                      let output_bound = EdgeExp.ValuePair.P (lb, ub) in
                      LTS.EdgeData.add_assignment acc arg_access output_bound )
                    call_model.side_effects graph_data.edge_data
                in
                let model_summary = LooperSummary.Model call_model in
                let call_summaries = Location.Map.add loc model_summary proc_data.call_summaries in
                let return_bound_pair =
                  Option.value call_model.return_bound ~default:call_pair_exp
                in
                (call_summaries, return_bound_pair, edge_data)
            | None ->
                debug_log "[CostModel] NOT FOUND@," ;
                (proc_data.call_summaries, call_pair_exp, graph_data.edge_data) )
      in
      debug_log "@]@,Adding return identifier mapping: %a = @,%a@]@," Ident.pp ret_id
        EdgeExp.ValuePair.pp_multiline return_bound ;
      (* Check if some variables used in arg expressions should be added to set of local variables *)
      let locals =
        AccessExpressionSet.fold
          (fun access locals_acc ->
            let access = HilExp.AccessExpression.dereference access in
            debug_log "Checking if local: %a@," HilExp.AccessExpression.pp access ;
            let access_base = HilExp.AccessExpression.get_base access in
            let is_formal = AccessPath.BaseSet.mem access_base proc_data.formals in
            if (not is_formal) && is_top_scope_local access_base graph_data then (
              debug_log "is local@," ;
              AccessPath.BaseMap.update access_base
                (fun v_opt ->
                  match v_opt with
                  | Some v ->
                      Some (AccessExpressionSet.add access v)
                  | None ->
                      Some (AccessExpressionSet.singleton access) )
                locals_acc )
            else (
              debug_log "not local@," ;
              locals_acc ) )
          arg_accesses graph_data.locals
      in
      ( { graph_data with
          ident_map= Ident.Map.add ret_id return_bound graph_data.ident_map
        ; locals
        ; edge_data= {edge_data with calls= EdgeExp.CallPair.Set.add call_pair edge_data.calls} }
      , {proc_data with call_summaries; norms= EdgeExp.Set.union proc_data.norms arg_norms} )
  | Metadata metadata -> (
    match metadata with
    | VariableLifetimeBegins (pvar, typ, loc) ->
        debug_log "@[<v4>[VariableLifetimeBegins] %a@,Variable: %a@," Location.pp loc Pvar.pp_value
          pvar ;
        let pvar_base_access = HilExp.AccessExpression.base (AccessPath.base_of_pvar pvar typ) in
        let scope_locals =
          match graph_data.scope_locals with
          | scope :: higher_scopes ->
              debug_log "Current scope variables: " ;
              let variables = AccessExpressionSet.add pvar_base_access scope in
              AccessExpressionSet.iter
                (fun base -> debug_log "%a " HilExp.AccessExpression.pp base)
                variables ;
              [variables] @ higher_scopes
          | [] ->
              [AccessExpressionSet.singleton pvar_base_access]
        in
        debug_log "@]@,@," ;
        ( {graph_data with locals= add_local pvar_base_access graph_data.locals; scope_locals}
        , proc_data )
    | ExitScope (var_list, loc) ->
        let exit_pvars = List.filter var_list ~f:(fun var -> Var.is_pvar var) in
        if not (List.is_empty exit_pvars) then (
          debug_log "@[<v4>[ExitScope] %a@," Location.pp loc ;
          debug_log "Variables: " ;
          List.iter exit_pvars ~f:(fun var -> debug_log "%a " Var.pp var) ;
          debug_log "@]@,@," ) ;
        (graph_data, proc_data)
    | _ ->
        (graph_data, proc_data) )
  | instr ->
      L.die InternalError "SIL instruction not implemented: %a"
        Sil.(pp_instr ~print_types:true Pp.text)
        instr


let exec_node node graph_data =
  let rev_instrs = IContainer.to_rev_list ~fold:Instrs.fold (Procdesc.Node.get_instrs node) in
  List.fold (List.rev rev_instrs) ~init:graph_data ~f:(fun acc instr -> exec_instr acc instr)


let remove_scoped_locals scope_locals locals =
  AccessExpressionSet.fold
    (fun access locals_map ->
      let access_base = HilExp.AccessExpression.get_base access in
      if HilExp.AccessExpression.is_base access then
        AccessPath.BaseMap.remove access_base locals_map
      else
        AccessPath.BaseMap.update access_base
          (fun accesses_opt ->
            match accesses_opt with
            | Some accesses ->
                let accesses = AccessExpressionSet.remove access accesses in
                if AccessExpressionSet.is_empty accesses then None else Some accesses
            | None ->
                L.die InternalError "Trying to remove missing scoped local access from locals map"
            )
          locals_map )
    scope_locals locals


let node_map_update key_node value_node cfg_node_opt =
  match cfg_node_opt with
  | Some node ->
      Some node
  | None ->
      debug_log "[NodeMap (%d)] Added: %a -> %a@," __LINE__ Procdesc.Node.pp key_node LTS.Node.pp
        value_node ;
      Some value_node


let create_looper_join_node cfg_node (graph_data, proc_data) =
  (* Join node *)
  let join_node_id = Procdesc.Node.get_id cfg_node in
  let join_node = LTS.Node.Join (Procdesc.Node.get_loc cfg_node, join_node_id) in
  debug_log "[JOIN NODE] %a@," Procdesc.Node.pp cfg_node ;
  let edge_data = LTS.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
  debug_log "[NEW EDGE] join_node: %a ----> %a@," LTS.Node.pp graph_data.last_node LTS.Node.pp
    join_node ;
  let new_edge = LTS.E.create graph_data.last_node edge_data join_node in
  let current_scope_locals, outer_scope_locals =
    match graph_data.scope_locals with
    | x :: xs ->
        (x, xs)
    | [] ->
        L.die InternalError "[create_join_node] Empty scope_locals list"
  in
  debug_log "[NodeMap (%d)] Added: %a -> %a@," __LINE__ Procdesc.Node.pp cfg_node LTS.Node.pp
    join_node ;
  let graph_data_updated =
    { graph_data with
      last_node= join_node
    ; edge_data= LTS.EdgeData.default
    ; locals= remove_scoped_locals current_scope_locals graph_data.locals
    ; scope_locals= outer_scope_locals
    ; node_map= Procdesc.NodeMap.add cfg_node join_node graph_data.node_map }
  in
  let proc_data_updated =
    { proc_data with
      nodes= LTS.NodeSet.add join_node proc_data.nodes
    ; edges= LTS.EdgeSet.add new_edge proc_data.edges }
  in
  (graph_data_updated, proc_data_updated)


let process_visited_cfg_node cfg_node proc_desc (graph_data, proc_data) =
  let edge_equal (s1, d1) (s2, d2) = LTS.Node.equal s1 s2 && LTS.Node.equal d1 d2 in
  let cfg_predecessors = Procdesc.Node.get_preds cfg_node in
  let in_degree = List.length cfg_predecessors in
  if is_infer_join_node cfg_node || in_degree > 1 then (
    let lts_node = Procdesc.NodeMap.find cfg_node graph_data.node_map in
    debug_log "Retrieved node: %a -> %a@," Procdesc.Node.pp cfg_node LTS.Node.pp lts_node ;
    (* Two paths are merging together so we have to merge conditions from
       both paths *)
    let edges, existing_edge_found =
      LTS.EdgeSet.fold
        (fun (src, edge_data, dst) (mapped_edges, found_edge) ->
          let edge_data, found =
            if edge_equal (src, dst) (graph_data.last_node, lts_node) then
              match (edge_data.branch_info, graph_data.edge_data.branch_info) with
              | Some (_, left_branch, _), Some (_, right_branch, _)
                when Bool.equal left_branch right_branch && Bool.equal left_branch true ->
                  let current_conditions = graph_data.edge_data.conditions in
                  let current_condition_norms = graph_data.edge_data.condition_norms in
                  let previous_conditions = edge_data.conditions in
                  let previous_condition_norms = edge_data.condition_norms in
                  ( { edge_data with
                      conditions= current_conditions @ previous_conditions
                    ; condition_norms= current_condition_norms @ previous_condition_norms }
                  , true )
              | _ ->
                  (edge_data, found_edge)
            else (edge_data, found_edge)
          in
          (LTS.EdgeSet.add (src, edge_data, dst) mapped_edges, found) )
        proc_data.edges (LTS.EdgeSet.empty, false)
    in
    let edges =
      if existing_edge_found then edges
      else
        let is_backedge = Procdesc.is_loop_head proc_desc cfg_node in
        debug_log "[NEW EDGE] %a ----> %a@," LTS.Node.pp graph_data.last_node LTS.Node.pp lts_node ;
        let edge_data = LTS.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
        let edge_data = LTS.EdgeData.set_backedge_flag edge_data ~is_backedge in
        let new_edge = LTS.E.create graph_data.last_node edge_data lts_node in
        LTS.EdgeSet.add new_edge proc_data.edges
    in
    let graph_data_updated =
      {graph_data with edge_data= LTS.EdgeData.default; last_split_info= None}
    in
    let proc_data_updated = {proc_data with edges} in
    (graph_data_updated, proc_data_updated) )
  else (graph_data, proc_data)


let process_split_node node successors predecessors (graph_data, proc_data) =
  (* Split node *)
  let branch_node = List.hd_exn successors in
  let current_if_kind =
    match Procdesc.Node.get_kind branch_node with
    | Procdesc.Node.Prune_node (_, kind, _) ->
        kind
    | _ ->
        L.die InternalError "Unexpected node type '%a' after split node" Procdesc.Node.pp
          branch_node
  in
  match graph_data.last_split_info with
  | Some (last_prune_node, last_if_kind) when Sil.equal_if_kind last_if_kind current_if_kind ->
      (* Should be compound condition of one loop/if statement.
         Do not create new node and merge instead *)
      debug_log "Last prune node: %a@," LTS.Node.pp last_prune_node ;
      let node_map =
        Procdesc.NodeMap.update node (node_map_update node last_prune_node) graph_data.node_map
      in
      ({graph_data with node_map}, proc_data)
  | _ ->
      (* Mismatching if-kinds or no available split info, create new node *)
      let loc = Procdesc.Node.get_loc branch_node in
      let branch_node_id = Procdesc.Node.get_id branch_node in
      let prune_node = LTS.Node.Prune (current_if_kind, loc, branch_node_id) in
      let edge_data = LTS.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
      let new_edge = LTS.E.create graph_data.last_node edge_data prune_node in
      debug_log "[NEW EDGE] %a@," LTS.pp_edge new_edge ;
      (* Check if it is a loop head and add the join node into scope stack *)
      let prev_node = List.hd_exn predecessors in
      let prev_is_loop_head = Procdesc.is_loop_head graph_data.proc_desc prev_node in
      let loop_heads, node_map =
        if prev_is_loop_head then
          ( prune_node :: graph_data.loop_heads
          , Procdesc.NodeMap.add prev_node prune_node graph_data.node_map )
        else (graph_data.loop_heads, Procdesc.NodeMap.add node prune_node graph_data.node_map)
      in
      let graph_data =
        { graph_data with
          last_split_info= Some (prune_node, current_if_kind)
        ; loop_heads
        ; last_node= prune_node
        ; edge_data= LTS.EdgeData.default
        ; node_map }
      in
      let proc_data =
        { proc_data with
          nodes= LTS.NodeSet.add prune_node proc_data.nodes
        ; edges= LTS.EdgeSet.add new_edge proc_data.edges }
      in
      (graph_data, proc_data)


let process_cfg_node cfg_node (graph_data, proc_data) =
  let cfg_predecessors = Procdesc.Node.get_preds cfg_node in
  let cfg_successors = Procdesc.Node.get_succs cfg_node in
  let in_degree = List.length cfg_predecessors in
  let out_degree = List.length cfg_successors in
  let node_is_loop_head = Procdesc.is_loop_head graph_data.proc_desc cfg_node in
  debug_log "In-degree: %d@,Out-degree: %d@,Loop head: %B@," in_degree out_degree node_is_loop_head ;
  let graph_data, proc_data =
    if in_degree > 1 && not node_is_loop_head then
      create_looper_join_node cfg_node (graph_data, proc_data)
    else (graph_data, proc_data)
  in
  let graph_data =
    if is_infer_join_node cfg_node then {graph_data with last_split_info= None} else graph_data
  in
  (* Execute node instructions *)
  let graph_data, proc_data = exec_node cfg_node (graph_data, proc_data) in
  if out_degree > 1 then
    process_split_node cfg_node cfg_successors cfg_predecessors (graph_data, proc_data)
  else (
    debug_log "[Warning] Experimental code branch, do-while related@," ;
    let node_map =
      Procdesc.NodeMap.update cfg_node
        (node_map_update cfg_node graph_data.last_node)
        graph_data.node_map
    in
    ({graph_data with node_map}, proc_data) )


let rec traverseCFG :
       Procdesc.t
    -> Procdesc.Node.t
    -> Procdesc.NodeSet.t
    -> construction_temp_data * procedure_data
    -> Procdesc.NodeSet.t * construction_temp_data * procedure_data =
 fun proc_desc cfg_node visited_cfg_nodes (graph_data, proc_data) ->
  (* console_log "[Visiting node] %a : %s\n" Procdesc.Node.pp cfg_node (pp_nodekind (Procdesc.Node.get_kind cfg_node)); *)
  (* console_log "[%a] In-degree: %d, Out-degree: %d\n" Procdesc.Node.pp cfg_node in_degree out_degree; *)
  (* TODO: should probably POP loophead from stack if we encounter false branch later on.
     * Otherwise we are accumulating loop heads from previous loops but it doesn't seem to
     * affect the algorithm in any way. *)
  debug_log "[traverseCFG] %a@," Procdesc.Node.pp cfg_node ;
  debug_log "Node not reachable: %B@," graph_data.branch_not_reachable ;
  if graph_data.branch_not_reachable then (visited_cfg_nodes, graph_data, proc_data)
  else if Procdesc.NodeSet.mem cfg_node visited_cfg_nodes then (
    debug_log "[VISITED NODE] %a@," Procdesc.Node.pp cfg_node ;
    (* console_log "[%a] Visited\n" Procdesc.Node.pp cfg_node; *)
    let graph_data, proc_data =
      process_visited_cfg_node cfg_node proc_desc (graph_data, proc_data)
    in
    (visited_cfg_nodes, graph_data, proc_data) )
  else (
    debug_log "@[<v2>[NODE] %a@," Procdesc.Node.pp cfg_node ;
    let visited_cfg_nodes = Procdesc.NodeSet.add cfg_node visited_cfg_nodes in
    let graph_data, proc_data = process_cfg_node cfg_node (graph_data, proc_data) in
    debug_log "@]@," ;
    if is_exit_node cfg_node then (
      debug_log "[EXIT NODE] %a@," Procdesc.Node.pp cfg_node ;
      let exit_node = LTS.Node.Exit in
      let edge_data = LTS.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
      debug_log "[NEW EDGE] exit_node: %a ----> %a@," LTS.Node.pp graph_data.last_node LTS.Node.pp
        exit_node ;
      let new_edge = LTS.E.create graph_data.last_node edge_data exit_node in
      let graph_data = {graph_data with last_node= exit_node; edge_data= LTS.EdgeData.default} in
      let proc_data =
        { proc_data with
          nodes= LTS.NodeSet.add exit_node proc_data.nodes
        ; edges= LTS.EdgeSet.add new_edge proc_data.edges }
      in
      (visited_cfg_nodes, graph_data, proc_data) )
    else
      let last_node = graph_data.last_node in
      let last_split_info = graph_data.last_split_info in
      let branch_not_reachable = graph_data.branch_not_reachable in
      let loop_heads = graph_data.loop_heads in
      let locals = graph_data.locals in
      let scope_locals = graph_data.scope_locals in
      let edge_data = graph_data.edge_data in
      let cfg_successors = Procdesc.Node.get_succs cfg_node in
      List.fold cfg_successors
        ~f:(fun (visited_cfg_nodes, graph_data, proc_data) next_node ->
          let graph_data =
            { graph_data with
              last_node
            ; last_split_info
            ; branch_not_reachable
            ; loop_heads
            ; locals
            ; scope_locals
            ; edge_data }
          in
          traverseCFG proc_desc next_node visited_cfg_nodes (graph_data, proc_data) )
        ~init:(visited_cfg_nodes, graph_data, proc_data) )


let construct : LooperSummary.t InterproceduralAnalysis.t -> procedure_data =
 fun analysis_data ->
  let open IOption.Let_syntax in
  debug_log "@[<v>" ;
  let proc_desc = analysis_data.proc_desc in
  let procname = Procdesc.get_proc_name proc_desc in
  let tenv = Exe_env.get_proc_tenv analysis_data.exe_env procname in
  let begin_loc = Procdesc.get_loc proc_desc in
  let start_node = Procdesc.get_start_node proc_desc in
  let lts_start_node = LTS.Node.Start (procname, begin_loc) in
  let formals = Procdesc.get_pvar_formals proc_desc in
  let prover_map = Provers.get_prover_map analysis_data in
  let active_prover = Provers.ProverMap.find Z3 prover_map in
  debug_log "@[<v4>[Procedure formals]@," ;
  let formals =
    List.foldi formals
      ~f:(fun idx formals (pvar, typ) ->
        debug_log "@[<v4>(%d) %a : %a" idx Pvar.(pp Pp.text) pvar Typ.(pp Pp.text) typ ;
        debug_log "@]@," ;
        let formal_pvar_base_access = AccessPath.base_of_pvar pvar typ in
        let formals = AccessPath.BaseSet.add formal_pvar_base_access formals in
        formals )
      ~init:AccessPath.BaseSet.empty
  in
  debug_log "@]@," ;
  let construction_data =
    { last_node= lts_start_node
    ; last_split_info= None
    ; branch_not_reachable= false
    ; edge_data= LTS.EdgeData.default
    ; ident_map= Ident.Map.empty
    ; node_map= Procdesc.NodeMap.empty
    ; potential_norms= EdgeExp.Set.empty
    ; loop_heads= []
    ; loop_modified= AccessExpressionSet.empty
    ; scope_locals= [AccessExpressionSet.empty]
    ; locals= AccessPath.BaseMap.empty
    ; tenv
    ; exe_env= analysis_data.exe_env
    ; proc_desc
    ; procname
    ; active_prover }
  in
  let proc_data =
    { nodes= LTS.NodeSet.singleton lts_start_node
    ; edges= LTS.EdgeSet.empty
    ; norms= EdgeExp.Set.empty
    ; formals
    ; analysis_data
    ; call_summaries= Location.Map.empty
    ; lts= LTS.create () }
  in
  let _, _, proc_data =
    traverseCFG proc_desc start_node Procdesc.NodeSet.empty (construction_data, proc_data)
  in
  LTS.NodeSet.iter (fun node -> LTS.add_vertex proc_data.lts node) proc_data.nodes ;
  LTS.EdgeSet.iter (fun edge -> LTS.add_edge_e proc_data.lts edge) proc_data.edges ;
  debug_log "@]" ;
  proc_data
