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
  ; const_assignments: Const.t AccessExpressionMap.t
  ; ident_map: EdgeExp.ValuePair.t Ident.Map.t
  ; formals_map: HilExp.access_expression AccessExpressionMap.t
  ; fn_ptr_map: Procname.t AccessExpressionMap.t
  ; node_map: LTS.Node.t Procdesc.NodeMap.t
  ; potential_norms: EdgeExp.Set.t
  ; loop_modified: AccessExpressionSet.t
  ; scope_locals: AccessExpressionSet.t list
  ; locals: AccessExpressionSet.t AccessPath.BaseMap.t
  ; tenv: Tenv.t
  ; exe_env: Exe_env.t
  ; proc_desc: Procdesc.t
  ; procname: Procname.t
  ; err_log: Errlog.t
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
  let of_sil_exp ~add_deref e typ =
    EdgeExp.of_sil_exp ~include_array_indexes:true ~f_resolve_id:ae_id_resolver ~test_resolver
      ~formal_map:graph_data.formals_map ~add_deref e typ
  in
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
  let exec_call_instr (ret_id, ret_typ) procname args loc flags =
    debug_log "@[<v4>Processing call arguments:@," ;
    let process_func_arg idx (lb_acc, ub_acc, types_acc, accesses_acc) (arg, arg_typ) =
      debug_log "@[<v2>(%d) Exp: %a : %a@," idx Exp.pp arg Typ.(pp Pp.text) arg_typ ;
      let arg_edge_exp = of_sil_exp ~add_deref:false arg arg_typ in
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
      ((ret_typ, procname, subst_args, loc), extract_norms subst_args)
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
            "Unsupported formal expression '%a',\n            access expression expected" EdgeExp.pp
            exp
    in
    let payload_opt = proc_data.analysis_data.analyze_dependency procname in
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
                debug_log "Formal: %a  --->  [%a, %a]@," EdgeExp.pp formal EdgeExp.pp lb EdgeExp.pp
                  ub ;
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
          let real_summary = LooperSummary.Real {payload with return_bound= subst_ret_bound_opt} in
          let call_summaries = Location.Map.add loc real_summary proc_data.call_summaries in
          let return_bound_pair = Option.value subst_ret_bound_opt ~default:call_pair_exp in
          (call_summaries, return_bound_pair, edge_data)
      | None -> (
          let arg_pairs = EdgeExp.ValuePair.make_list lb_args ub_args in
          debug_log "callee_pname: %a@," Procname.pp procname ;
          match LooperCostModels.Call.get_model procname arg_pairs graph_data.exe_env with
          | Some call_model ->
              (* debug_log "[CostModel] Model cost: %a@," LooperSummary.Model.pp call_model ; *)
              let edge_data =
                EdgeExp.Map.fold
                  (fun ptr_arg (lb, ub) acc ->
                    debug_log "Side-effect: %a  --->  [%a, %a]@," EdgeExp.pp ptr_arg EdgeExp.pp lb
                      EdgeExp.pp ub ;
                    let arg_access = HilExp.AccessExpression.dereference (extract_access ptr_arg) in
                    let output_bound = EdgeExp.ValuePair.P (lb, ub) in
                    LTS.EdgeData.add_assignment acc arg_access output_bound )
                  call_model.side_effects graph_data.edge_data
              in
              let model_summary = LooperSummary.Model call_model in
              let call_summaries = Location.Map.add loc model_summary proc_data.call_summaries in
              let return_bound_pair = Option.value call_model.return_bound ~default:call_pair_exp in
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
  in
  let process_store_lhs lhs typ =
    match of_sil_exp ~add_deref:true lhs typ with
    | EdgeExp.ValuePair.V e -> (
      match e with
      | EdgeExp.T.Access lhs_access ->
          if HilExp.AccessExpression.is_return_var lhs_access then
            (* Adjust the type of return variable based on the return type
               of the analyzed procedure. There are some inconsistencies otherwise *)
            let var, _ = HilExp.AccessExpression.get_base lhs_access in
            let new_base = (var, proc_ret_type) in
            let replaced_access =
              HilExp.AccessExpression.replace_base new_base lhs_access
                ~remove_deref_after_base:false
            in
            (replaced_access, true)
          else (lhs_access, false)
      | _ ->
          L.die InternalError
            "Left-hand side expression of Store instruction is not an AccessExpression: %a"
            EdgeExp.pp e )
    | pair ->
        L.die InternalError
          "Left-hand side expression of\n      Store instruction cannot be EdgeExp.ValuePair.P: %a"
          EdgeExp.ValuePair.pp pair
  in
  let process_store_rhs rhs typ =
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
          let test =
            EdgeExp.ValuePair.map_accesses value ~f:(fun access ->
                (* Try to propagate previous assignments stored on this edge *)
                LTS.EdgeData.get_assignment_rhs graph_data.edge_data access
                (* let process_value exp =
                     match exp with
                     | EdgeExp.T.Access access ->
                         EdgeExp.T.Access (map_formal access)
                     | _ ->
                         exp
                   in
                   match rhs with
                   | EdgeExp.ValuePair.V v ->
                       EdgeExp.ValuePair.V (process_value v)
                   | EdgeExp.ValuePair.P (lb, ub) ->
                       EdgeExp.ValuePair.P (process_value lb, process_value ub) *) )
          in
          EdgeExp.ValuePair.map ~f:simplify test
    in
    let exp_pair = of_sil_exp ~add_deref:false rhs typ in
    (* debug_log "@[<v2>[Pre-Merge] EdgeExp: %a = @,%a@]@," EdgeExp.pp lhs_edge_exp
       EdgeExp.ValuePair.pp_multiline rhs_edge_exp_pair ; *)
    (* TODO: Investigate if some of these cases can actually
       occur in reality or not, seems weird *)
    match exp_pair with
    | EdgeExp.ValuePair.V rhs_value ->
        process_rhs_value rhs_value
    | EdgeExp.ValuePair.P (lb, ub) ->
        let x, y = (process_rhs_value lb, process_rhs_value ub) in
        debug_log "@[<v2>RHS LB: @,%a@]@," EdgeExp.ValuePair.pp_multiline x ;
        debug_log "@[<v2>RHS UB: @,%a@]@," EdgeExp.ValuePair.pp_multiline y ;
        EdgeExp.ValuePair.merge x y
    (* debug_log "@[<v2>[Post-Merge] EdgeExp: %a = @,%a@]@," EdgeExp.pp lhs_edge_exp
       EdgeExp.ValuePair.pp_multiline assignment_rhs ; *)
  in
  match instr with
  | Prune (cond, loc, branch, kind) ->
      (* debug_log "[PRUNE (%s)] (%a) | %a\n" (Sil.if_kind_to_string kind) Location.pp loc Exp.pp cond; *)
      let edge_exp_cond_pair = of_sil_exp ~add_deref:false cond (Typ.mk (Tint IBool)) in
      debug_log
        "@[<v4>[PRUNE] %a@,Prune type: %a@,Branch: %B@,Exp condition: %a@,EdgeExp condition: %a@,"
        Location.pp loc Sil.pp_if_kind kind branch Exp.pp cond EdgeExp.ValuePair.pp
        edge_exp_cond_pair ;
      let is_norm_modified norm =
        EdgeExp.exists_access norm ~f:(fun access ->
            AccessExpressionSet.mem access graph_data.loop_modified )
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
            false
            (* try
                 EdgeExp.always_false condition graph_data.const_assignments graph_data.tenv
                   graph_data.active_prover
               with _ ->
                 debug_log "[EdgeExp.always_false] Failed to determine@," ;
                 false *)
        | None ->
            debug_log "None@," ;
            false
      in
      (* if condition_always_false then
           report_issue IssueType.looper_condition_always_false ~loc
             "Else-branch of condition is always false" ;
         let graph_data = {graph_data with branch_not_reachable= condition_always_false} in *)
      let edge_data =
        match normalized_cond_opt with
        | Some normalized_cond
          when (not (EdgeExp.is_zero normalized_cond)) && not (EdgeExp.is_one normalized_cond) ->
            LTS.EdgeData.add_condition graph_data.edge_data normalized_cond
        | _ ->
            graph_data.edge_data
      in
      let graph_data, proc_data =
        if branch then (
          (* Derive norm from prune condition.
             * [x > y] -> [x - y] > 0
             * [x >= y] -> [x - y + 1] > 0 *)
          (* TODO: Confirm that the conversion is truly producing
             lower/upper bound for the purpose of norm extraction from
             the loop condition.
             Also, do we need the lower bound condition for anything? *)
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
              (* let new_norm =
                   match kind with
                   | Sil.Ik_dowhile ->
                       EdgeExp.T.BinOp (Binop.PlusA None, new_norm, EdgeExp.one)
                   | _ ->
                       new_norm
                 in *)
              (* let norms = EdgeExp.Set.add new_norm proc_data.norms in
                 let edge_data = LTS.EdgeData.add_condition_norm graph_data.edge_data new_norm in
                 ({graph_data with edge_data}, {proc_data with norms}) *)
              let norm_modified = is_norm_modified new_norm in
              debug_log "norm_modified: %B@," norm_modified ;
              if (not loop_prune) && not norm_modified then (
                (* Prune on loop path but not loop head. Norm is only potential,
                   * must be confirmed by increment/decrement on this loop path *)
                debug_log "New potential norm: %a@," EdgeExp.pp new_norm ;
                let potential_norms = EdgeExp.Set.add new_norm graph_data.potential_norms in
                ({graph_data with potential_norms}, proc_data) )
              else (
                debug_log "New norm: %a@," EdgeExp.pp new_norm ;
                let norms = EdgeExp.Set.add new_norm proc_data.norms in
                let edge_data = LTS.EdgeData.add_condition_norm graph_data.edge_data new_norm in
                ({graph_data with edge_data}, {proc_data with norms}) )
          | _ ->
              (graph_data, proc_data) )
        else
          let graph_data = {graph_data with edge_data} in
          (graph_data, proc_data)
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
      let is_fun_ptr = Typ.is_pointer_to_function typ in
      debug_log "@[<v4>[STORE] %a@,Type: %a@,Exp: %a = %a@,Pointer to function: %B@," Location.pp
        loc
        Typ.(pp Pp.text)
        typ Exp.pp lhs Exp.pp rhs is_fun_ptr ;
      let rhs_exp_pair = process_store_rhs rhs typ in
      let lhs_access, lhs_is_return = process_store_lhs lhs typ in
      let lhs_exp = EdgeExp.T.Access lhs_access in
      let ((_, lhs_base_typ) as lhs_base) = HilExp.AccessExpression.get_base lhs_access in
      debug_log "@[<v4>EdgeExp: %a = %a" HilExp.AccessExpression.pp lhs_access EdgeExp.ValuePair.pp
        rhs_exp_pair ;
      check_casts rhs_exp_pair ;
      debug_log "@]@," ;
      let norms_to_str norm_set =
        List.map (EdgeExp.Set.elements norm_set) ~f:EdgeExp.to_string |> String.concat ~sep:" | "
      in
      (* Checks if its possible to confirm some potential norm due to it's
       * decrement on this edge *)
      let extract_norms rexp potential_norms =
        debug_log "@[<v2>[Extract norms]@," ;
        debug_log "Potential norms: %s@," (norms_to_str potential_norms) ;
        let process_rhs_value rhs potential_norms =
          match rhs with
          | EdgeExp.T.BinOp
              ((Binop.PlusA _ | Binop.MinusA _), rhs_subexp, EdgeExp.T.Const (Const.Cint _))
            when EdgeExp.equal lhs_exp rhs_subexp ->
              (* Increment or decrement of variable: v = v +/- C, check if it confirms any norms *)
              let confirmed_norms =
                EdgeExp.Set.filter
                  (fun potential_norm ->
                    EdgeExp.exists_access potential_norm
                      ~f:(HilExp.AccessExpression.equal lhs_access) )
                  potential_norms
              in
              debug_log "Confirmed norms: %s@," (norms_to_str confirmed_norms) ;
              (EdgeExp.Set.diff potential_norms confirmed_norms, confirmed_norms)
          | _ ->
              (potential_norms, EdgeExp.Set.empty)
        in
        (* Extract norms from the RHS *)
        let potential_norms, new_norms =
          match rexp with
          | EdgeExp.ValuePair.V value ->
              process_rhs_value value potential_norms
          | EdgeExp.ValuePair.P (lb, ub) ->
              let potential_norms, lb_norms = process_rhs_value lb potential_norms in
              let potential_norms, ub_norms = process_rhs_value ub potential_norms in
              (potential_norms, EdgeExp.Set.union lb_norms ub_norms)
        in
        (* Extract norms from the LHS *)
        let new_norms =
          if
            AccessPath.BaseSet.mem lhs_base proc_data.formals
            && Typ.is_pointer lhs_base_typ && EdgeExp.is_integer_type typ
          then
            (* Access base of LHS is a formal pointer, add to norms
               We need to track pointer formals due to possible side-effects *)
            match lhs_access with
            | HilExp.AccessExpression.FieldOffset (Dereference _, _)
            | HilExp.AccessExpression.Dereference _ ->
                debug_log
                  "Formal base '%a' is a pointer: %a. Adding access expression '%a' to norms.@,"
                  AccessPath.pp_base lhs_base
                  Typ.(pp Pp.text)
                  lhs_base_typ HilExp.AccessExpression.pp lhs_access ;
                EdgeExp.Set.add lhs_exp new_norms
            | _ ->
                new_norms
          else if lhs_is_return then (
            (* LHS is a return variable, add to norms
               We need to track return variable to compute VB(return) at the end *)
            let ret_typ = HilExp.AccessExpression.get_typ lhs_access graph_data.tenv in
            debug_log "Return type: %s@,"
              (Option.value_map ret_typ ~default:"None" ~f:(fun v -> Typ.to_string v)) ;
            debug_log "LHS is a return variable, adding to norms@," ;
            EdgeExp.Set.add lhs_exp new_norms )
          else new_norms
        in
        debug_log "@]@," ;
        (potential_norms, new_norms)
      in
      let rec process_function_pointer lhs_access rexp_pair fn_ptr_map =
        match rexp_pair with
        | EdgeExp.ValuePair.V (EdgeExp.T.Const (Const.Cfun procname)) ->
            AccessExpressionMap.add lhs_access procname fn_ptr_map
        | EdgeExp.ValuePair.V (EdgeExp.T.Access rhs_access) -> (
          match AccessExpressionMap.find_opt rhs_access fn_ptr_map with
          | Some procname ->
              AccessExpressionMap.add lhs_access procname fn_ptr_map
          | None ->
              fn_ptr_map )
        | EdgeExp.ValuePair.P (lb, ub) ->
            (* TODO: we should probably store a set of possible indirect
               function calls, instantiate all of them and take the max(...)
               during the bound analysis to stay "sound" *)
            let fn_ptr_map =
              process_function_pointer lhs_access (EdgeExp.ValuePair.V lb) fn_ptr_map
            in
            process_function_pointer lhs_access (EdgeExp.ValuePair.V ub) fn_ptr_map
        | _ ->
            fn_ptr_map
      in
      let locals =
        if lhs_is_return then add_local lhs_access graph_data.locals else graph_data.locals
      in
      (* Always add LHS access to the set of local variables. It will be removed
       * when exiting current scope if it's not a top-scope local *)
      let locals = add_local lhs_access locals in
      let scope_locals =
        (* Only base of access expression stripped of any other sub-accesses *)
        let lhs_access_stripped = HilExp.AccessExpression.base lhs_base in
        if
          (not (HilExp.AccessExpression.equal lhs_access_stripped lhs_access))
          && AccessPath.BaseMap.mem lhs_base locals
          && not (is_top_scope_local lhs_base graph_data)
        then
          match graph_data.scope_locals with
          | scope :: higher_scopes ->
              [AccessExpressionSet.add lhs_access scope] @ higher_scopes
          | [] ->
              [AccessExpressionSet.singleton lhs_access]
        else graph_data.scope_locals
      in
      let edge_data = LTS.EdgeData.add_assignment graph_data.edge_data lhs_access rhs_exp_pair in
      debug_log "in_loop: %B@," in_loop ;
      let loop_modified =
        if in_loop then AccessExpressionSet.add lhs_access graph_data.loop_modified
        else graph_data.loop_modified
      in
      let fn_ptr_map =
        if is_fun_ptr then process_function_pointer lhs_access rhs_exp_pair graph_data.fn_ptr_map
        else graph_data.fn_ptr_map
      in
      let const_assignments =
        match rhs_exp_pair with
        | EdgeExp.ValuePair.V (Const const) ->
            AccessExpressionMap.add lhs_access const graph_data.const_assignments
        | _ ->
            (* Variable not const anymore, do not constant value any further *)
            AccessExpressionMap.remove lhs_access graph_data.const_assignments
      in
      let potential_norms, new_norms = extract_norms rhs_exp_pair graph_data.potential_norms in
      let norms = EdgeExp.Set.union proc_data.norms new_norms in
      debug_log "Norms: %s@," (norms_to_str norms) ;
      debug_log "@,@]@," ;
      let graph_data =
        { graph_data with
          locals
        ; scope_locals
        ; potential_norms
        ; edge_data
        ; const_assignments
        ; loop_modified
        ; fn_ptr_map }
      in
      (graph_data, {proc_data with norms})
  | Load {id; e; typ; loc} ->
      debug_log "@[<v4>[LOAD] %a@,Type: %a@,Exp: %a = %a@," Location.pp loc
        Typ.(pp Pp.text)
        typ Ident.pp id Exp.pp e ;
      let rhs_edge_exp_pair = of_sil_exp ~add_deref:true e typ in
      (* let rhs_edge_exp_pair =
           let assignments = graph_data.edge_data.assignments in
           match rhs_edge_exp_pair with
           | EdgeExp.ValuePair.V rhs ->
               let rhs_mapped, _ =
                 EdgeExp.map_accesses rhs
                   ~f:(fun rhs_access _ ->
                     let assignment_opt =
                       List.find assignments ~f:(fun (access, _) ->
                           HilExp.AccessExpression.equal rhs_access access )
                     in
                     match assignment_opt with
                     | Some (_, EdgeExp.ValuePair.V rhs) ->
                         (rhs, ())
                     | _ ->
                         (EdgeExp.T.Access rhs_access, ()) )
                   ~init:()
               in
               EdgeExp.ValuePair.V rhs_mapped
           | _ ->
               rhs_edge_exp_pair
         in *)
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
  | Call ((ret_id, ret_typ), exp, args, loc, flags) -> (
      debug_log "@[<v4>[CALL] %a@,exp: %a@," Location.pp loc Exp.pp exp ;
      (* debug_log "@[<v4>[CALL] %a@,Procedure name: %a@," Location.pp loc Procname.pp procname ; *)
      (* TODO: ret_typ is not correct, should be something else? *)
      match of_sil_exp ~add_deref:false exp ret_typ with
      | EdgeExp.ValuePair.V (Const (Cfun callee_pname)) ->
          debug_log "Procedure name: %a@," Procname.pp callee_pname ;
          exec_call_instr (ret_id, ret_typ) callee_pname args loc flags
      | EdgeExp.ValuePair.V (Access call_access) -> (
          debug_log "Call Access: %a@," HilExp.AccessExpression.pp call_access ;
          match AccessExpressionMap.find_opt call_access graph_data.fn_ptr_map with
          | Some callee_pname ->
              debug_log "Indirect call procedure name: %a@," Procname.pp callee_pname ;
              exec_call_instr (ret_id, ret_typ) callee_pname args loc flags
          | None ->
              debug_log "Indirect call procedure not found@," ;
              (graph_data, proc_data) )
      | exp ->
          debug_log "[Warning] Unsupported call expression %a, skipping@," EdgeExp.ValuePair.pp exp ;
          (graph_data, proc_data) )
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
  let graph_data =
    if Procdesc.is_loop_head proc_desc cfg_node then
      {graph_data with loop_heads= List.tl_exn graph_data.loop_heads}
    else graph_data
  in
  if is_infer_join_node cfg_node || in_degree > 1 then (
    let lts_node = Procdesc.NodeMap.find cfg_node graph_data.node_map in
    debug_log "Retrieved node: %a -> %a@," Procdesc.Node.pp cfg_node LTS.Node.pp lts_node ;
    (* Two paths are merging together so we have to merge conditions from
       both paths *)
    let join_incoming_edges (left : LTS.EdgeData.t) (right : LTS.EdgeData.t) =
      match (left.branch_info, right.branch_info) with
      | Some (_, left_branch, _), Some (_, right_branch, _)
        when Bool.equal left_branch right_branch && Bool.equal left_branch true ->
          debug_log "JOINING@," ;
          debug_log "left: %s@,"
            (EdgeExp.output_exp_dnf left.conditions ~or_sep:" ||\n" ~and_sep:" && ") ;
          debug_log "right: %s@,"
            (EdgeExp.output_exp_dnf right.conditions ~or_sep:" ||\n" ~and_sep:" && ") ;
          let current_conditions = right.conditions in
          let current_condition_norms = right.condition_norms in
          let previous_conditions = left.conditions in
          let previous_condition_norms = left.condition_norms in
          let merged =
            { left with
              conditions= current_conditions @ previous_conditions
            ; condition_norms= current_condition_norms @ previous_condition_norms }
          in
          (merged, true)
      | _ ->
          debug_log "IGNORING@," ;
          (left, false)
    in
    let edges, existing_edge_found =
      LTS.EdgeSet.fold
        (fun (src, edge_data, dst) (mapped_edges, found_edge) ->
          debug_log "Merging two incoming edges@," ;
          let edge_data, found =
            if edge_equal (src, dst) (graph_data.last_node, lts_node) then (
              debug_log "Edge equal@," ;
              join_incoming_edges edge_data graph_data.edge_data
              (* debug_log "Edge equal@," ;
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
              *) )
            else (
              debug_log "Edge NOT equal@," ;
              (edge_data, found_edge) )
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
      let node_map =
        if prev_is_loop_head then Procdesc.NodeMap.add prev_node prune_node graph_data.node_map
        else Procdesc.NodeMap.add node prune_node graph_data.node_map
      in
      let graph_data =
        { graph_data with
          last_split_info= Some (prune_node, current_if_kind)
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


let process_infer_loop_head cfg_node (graph_data, proc_data) =
  let join_node_id = Procdesc.Node.get_id cfg_node in
  let join_node = LTS.Node.Join (Procdesc.Node.get_loc cfg_node, join_node_id) in
  let edge_data = LTS.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
  let new_edge = LTS.E.create graph_data.last_node edge_data join_node in
  let loop_heads = join_node :: graph_data.loop_heads in
  let graph_data =
    {graph_data with last_node= join_node; loop_heads; edge_data= LTS.EdgeData.default}
  in
  let proc_data =
    { proc_data with
      nodes= LTS.NodeSet.add join_node proc_data.nodes
    ; edges= LTS.EdgeSet.add new_edge proc_data.edges }
  in
  (graph_data, proc_data)


let process_cfg_node cfg_node (graph_data, proc_data) =
  let cfg_predecessors = Procdesc.Node.get_preds cfg_node in
  let cfg_successors = Procdesc.Node.get_succs cfg_node in
  let in_degree = List.length cfg_predecessors in
  let out_degree = List.length cfg_successors in
  let node_is_loop_head = Procdesc.is_loop_head graph_data.proc_desc cfg_node in
  let infer_join_node = is_infer_join_node cfg_node in
  debug_log "In-degree: %d@,Out-degree: %d@,Loop head: %B@," in_degree out_degree node_is_loop_head ;
  let graph_data, proc_data =
    if in_degree > 1 && not node_is_loop_head then
      create_looper_join_node cfg_node (graph_data, proc_data)
    else (graph_data, proc_data)
  in
  let graph_data =
    if infer_join_node then {graph_data with last_split_info= None} else graph_data
  in
  (* Execute node instructions *)
  let graph_data, proc_data = exec_node cfg_node (graph_data, proc_data) in
  if out_degree > 1 then
    process_split_node cfg_node cfg_successors cfg_predecessors (graph_data, proc_data)
  else
    let is_goto_label = (not infer_join_node) && node_is_loop_head in
    debug_log
      "[Warning] Experimental code branch, do-while related@,\
       is_infer_join_node: %B@,\
       is_goto_label: %B@,"
      infer_join_node is_goto_label ;
    let graph_data, proc_data =
      if node_is_loop_head then process_infer_loop_head cfg_node (graph_data, proc_data)
      else (graph_data, proc_data)
    in
    let node_map =
      Procdesc.NodeMap.update cfg_node
        (node_map_update cfg_node graph_data.last_node)
        graph_data.node_map
    in
    ({graph_data with node_map}, proc_data)


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
  let formal_pvars = Procdesc.get_pvar_formals proc_desc in
  let prover_map = Provers.get_prover_map analysis_data in
  let active_prover = Provers.ProverMap.find Z3 prover_map in
  let report_issue = Reporting.log_issue proc_desc analysis_data.err_log Looper in
  debug_log "@[<v4>[Procedure formals]@," ;
  let formals, formal_mapping, locals =
    List.foldi formal_pvars
      ~f:(fun idx (set_acc, map_acc, locals_acc) (formal_pvar, formal_typ) ->
        debug_log "(%d) %a : %a" idx Pvar.(pp Pp.text) formal_pvar Typ.(pp Pp.text) formal_typ ;
        let shadow_formal_name = Pvar.to_string formal_pvar ^ "_shadow" in
        let shadow_pvar = Pvar.mk (Mangled.from_string shadow_formal_name) procname in
        let shadow_base = AccessPath.base_of_pvar shadow_pvar (Typ.mk (Tint IUInt)) in
        let formal_base = (Var.of_pvar formal_pvar, formal_typ) in
        let shadow_access = HilExp.AccessExpression.base shadow_base in
        let formal_access = HilExp.AccessExpression.base formal_base in
        let set_acc = AccessPath.BaseSet.add formal_base set_acc in
        let map_acc = AccessExpressionMap.add formal_access shadow_access map_acc in
        let locals_acc =
          AccessPath.BaseMap.add shadow_base
            (AccessExpressionSet.singleton shadow_access)
            locals_acc
        in
        (set_acc, map_acc, locals_acc) )
      ~init:(AccessPath.BaseSet.empty, AccessExpressionMap.empty, AccessPath.BaseMap.empty)
  in
  debug_log "@]@," ;
  let construction_data =
    { last_node= lts_start_node
    ; last_split_info= None
    ; branch_not_reachable= false
    ; edge_data= LTS.EdgeData.default
    ; const_assignments= AccessExpressionMap.empty
    ; ident_map= Ident.Map.empty
    ; formals_map= formal_mapping
    ; fn_ptr_map= AccessExpressionMap.empty
    ; node_map= Procdesc.NodeMap.empty
    ; potential_norms= EdgeExp.Set.empty
    ; loop_heads= []
    ; loop_modified= AccessExpressionSet.empty
    ; scope_locals= [AccessExpressionSet.empty]
    ; locals
    ; tenv
    ; exe_env= analysis_data.exe_env
    ; proc_desc
    ; procname
    ; err_log= analysis_data.err_log
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
  let merge_assignments const_assignments assignments =
    List.fold const_assignments ~init:(assignments, false)
      ~f:(fun (assignments_acc, modified) (const_lhs, rhs_const) ->
        debug_log "Checking const lhs: %a@," HilExp.AccessExpression.pp const_lhs ;
        List.fold assignments_acc ~init:([], modified) ~f:(fun (acc, modified) (lhs, rhs) ->
            if HilExp.AccessExpression.equal const_lhs lhs then (
              debug_log "Equal: %a = %a@,RHS: %a@," HilExp.AccessExpression.pp const_lhs
                HilExp.AccessExpression.pp lhs EdgeExp.ValuePair.pp rhs ;
              match rhs with
              | EdgeExp.ValuePair.V (EdgeExp.T.Access rhs_access)
                when HilExp.AccessExpression.equal lhs rhs_access ->
                  debug_log "Mapping@," ;
                  ((lhs, rhs_const) :: acc, true)
              | _ ->
                  ((lhs, rhs) :: acc, modified) )
            else ((lhs, rhs) :: acc, modified) ) )
  in
  LTS.NodeSet.iter (fun node -> LTS.add_vertex proc_data.lts node) proc_data.nodes ;
  (* Add edges to LTS and modify the initial edge to contain assignments of the shadow variables *)
  LTS.EdgeSet.iter
    (fun (src, edge_data, dst) ->
      let edge_data =
        if LTS.Node.is_start src then
          (* For each formal f add assignment f_shadow = f to the initial edge
             It is done as post-processing step to avoid possible double assignments on the initial edge *)
          AccessExpressionMap.fold
            (fun formal shadow (edge_data_acc : LTS.EdgeData.t) ->
              let shadow_base = HilExp.AccessExpression.get_base shadow in
              let formal_base = HilExp.AccessExpression.get_base formal in
              let assignments =
                List.map edge_data_acc.assignments ~f:(fun (lhs, rhs) ->
                    debug_log "Mapping: %a = %a@," HilExp.AccessExpression.pp lhs
                      EdgeExp.ValuePair.pp rhs ;
                    let mapped_rhs =
                      match rhs with
                      | EdgeExp.ValuePair.V exp ->
                          let rhs, _ =
                            EdgeExp.map_accesses exp ~init:() ~f:(fun rhs_access _ ->
                                let rhs_base = HilExp.AccessExpression.get_base rhs_access in
                                (* AccessPath.equal_base *)
                                if AccessPath.equal_base rhs_base shadow_base then (
                                  debug_log "Equal: %a@,Setting: %a@," HilExp.AccessExpression.pp
                                    rhs_access HilExp.AccessExpression.pp formal ;
                                  let replaced =
                                    HilExp.AccessExpression.replace_base formal_base rhs_access
                                      ~remove_deref_after_base:true
                                  in
                                  (EdgeExp.T.Access replaced, ()) )
                                else (EdgeExp.T.Access rhs_access, ()) )
                          in
                          EdgeExp.ValuePair.V rhs
                      | _ ->
                          rhs
                    in
                    debug_log "Mapped: %a = %a@," HilExp.AccessExpression.pp lhs
                      EdgeExp.ValuePair.pp mapped_rhs ;
                    (* let mapped_rhs =
                         match rhs with
                         | EdgeExp.ValuePair.V (EdgeExp.T.Access rhs_access)
                           when HilExp.AccessExpression.equal shadow rhs_access ->
                             EdgeExp.ValuePair.V (EdgeExp.T.Access formal)
                         | _ ->
                             rhs
                       in *)
                    (lhs, mapped_rhs) )
              in
              {edge_data_acc with assignments} )
            formal_mapping edge_data
        else edge_data
      in
      let edge = (src, edge_data, dst) in
      LTS.add_edge_e proc_data.lts edge )
    proc_data.edges ;
  let rec propagate_const_assignments const_nodes =
    if not (LTS.NodeSet.is_empty const_nodes) then (
      (* Pop one node from set of unprocessed nodes *)
      let node = LTS.NodeSet.min_elt const_nodes in
      debug_log "Propagating const assignments for: %a@," LTS.Node.pp node ;
      let nodes = LTS.NodeSet.remove node const_nodes in
      let backedge_in_edges, in_edges =
        List.partition_tf (LTS.pred_e proc_data.lts node)
          ~f:(fun (_, (edge_data : LTS.EdgeData.t), _) -> edge_data.backedge)
      in
      let shared_const_assignments =
        List.map in_edges ~f:(fun ((_, edge_data, _) as edge) ->
            debug_log "Processing edge: %a@," LTS.pp_edge edge ;
            LTS.EdgeData.get_const_assignments edge_data )
        |> List.reduce ~f:(fun l1 l2 ->
               List.iter l1 ~f:(fun assignment ->
                   debug_log "L1 assignment: %a@," LTS.pp_assignment assignment ) ;
               List.iter l2 ~f:(fun assignment ->
                   debug_log "L2 assignment: %a@," LTS.pp_assignment assignment ) ;
               (* Perform list intersection *)
               let rec intersect list1 list2 =
                 match list1 with
                 | [] ->
                     []
                 | head :: tail ->
                     if List.mem list2 head ~equal:LTS.equal_assignment then
                       head :: intersect tail list2
                     else intersect tail list2
               in
               intersect l1 l2 )
        |> Option.value ~default:[]
      in
      List.iter shared_const_assignments ~f:(fun assignment ->
          debug_log "Const assignment: %a@," LTS.pp_assignment assignment ) ;
      let rec backward_path_check ((current_node, (edge_data : LTS.EdgeData.t), _) as edge)
          path_nodes path_edges assignments_acc =
        debug_log "Checking edge: %a@," LTS.pp_edge edge ;
        let assignments_acc =
          List.filter assignments_acc ~f:(fun (lhs, _) ->
              (* Prune constant assignments, continue propagating only if for constant assignment "e = C"
                 the edge contains invariant assignment "e = e" *)
              let dummy_assignment = (lhs, EdgeExp.ValuePair.V (EdgeExp.T.Access lhs)) in
              List.exists edge_data.assignments ~f:(LTS.equal_assignment dummy_assignment) )
        in
        let path_edges = LTS.EdgeSet.add edge path_edges in
        if LTS.Node.equal current_node node then (path_nodes, path_edges, assignments_acc)
        else if LTS.NodeSet.mem current_node path_nodes then
          (path_nodes, path_edges, assignments_acc)
        else
          let pred_edges = LTS.pred_e proc_data.lts current_node in
          let path_nodes = LTS.NodeSet.add current_node path_nodes in
          List.fold pred_edges ~init:(path_nodes, path_edges, assignments_acc)
            ~f:(fun (path_nodes, visited_edges, assignments_acc) backward_edge ->
              backward_path_check backward_edge path_nodes visited_edges assignments_acc )
      in
      let _, _, pruned_const_assignments =
        List.fold
          ~init:(LTS.NodeSet.empty, LTS.EdgeSet.empty, shared_const_assignments)
          ~f:(fun (path_nodes, path_edges, assignments_acc) edge ->
            backward_path_check edge path_nodes path_edges assignments_acc )
          backedge_in_edges
      in
      (* debug_log "@[<v2>Pruned const assignments:@," ;
         List.iter pruned_const_assignments ~f:(fun assignment ->
             debug_log "%a@," LTS.pp_assignment assignment ) ;
         debug_log "@]@," ;
         debug_log "@[<v2>Path edges:@," ;
         LTS.EdgeSet.iter
           (fun ((src, edge_data, dst) as edge) -> debug_log "%a@," LTS.pp_edge edge)
           path_edges ;
         debug_log "@]@," ; *)
      (* let _, in_edge_data, _ = List.hd_exn in_edges in
         let const_assignments =
           List.filter in_edge_data.assignments ~f:(fun assignment ->
               LTS.is_const_assignment assignment |> Option.is_some )
         in *)
      let nodes =
        if not (List.is_empty pruned_const_assignments) then
          let out_edges = LTS.succ_e proc_data.lts node in
          List.fold out_edges ~init:nodes
            ~f:(fun nodes_acc ((src, (out_edge_data : LTS.EdgeData.t), dst) as out_edge) ->
              debug_log "Modifying edge: %a@," LTS.pp_edge out_edge ;
              let assignments, modified =
                merge_assignments pruned_const_assignments out_edge_data.assignments
              in
              if modified then (
                LTS.remove_edge_e proc_data.lts out_edge ;
                let new_edge_data = {out_edge_data with assignments} in
                LTS.add_edge_e proc_data.lts (src, new_edge_data, dst) ;
                LTS.NodeSet.add dst nodes_acc )
              else nodes_acc )
        else nodes
      in
      propagate_const_assignments nodes )
  in
  (* Propagate constant assignments to help the further analysis. Helps with do-while loops *)
  let const_nodes =
    LTS.fold_edges_e
      (fun (_, edge_data, dst) acc ->
        let const_assignments = LTS.EdgeData.get_const_assignments edge_data in
        (* let in_degree = LTS.in_degree proc_data.lts dst in
           if has_const_assignment && Int.equal in_degree 1 then LTS.NodeSet.add dst acc else acc *)
        if List.is_empty const_assignments then acc else LTS.NodeSet.add dst acc )
      proc_data.lts LTS.NodeSet.empty
  in
  LTS.NodeSet.iter
    (fun node -> debug_log "Node with const assignment: %a@," LTS.Node.pp node)
    const_nodes ;
  propagate_const_assignments const_nodes ;
  (* Extract updated edges *)
  let edges =
    LTS.fold_edges_e (fun edge acc -> LTS.EdgeSet.add edge acc) proc_data.lts LTS.EdgeSet.empty
  in
  (* Check always-false conditions and cut-off unreachable nodes *)
  let create_and_term and_terms =
    List.reduce_exn (EdgeExp.Set.elements and_terms) ~f:(fun and1 and2 ->
        EdgeExp.T.BinOp (Binop.LAnd, and1, and2) )
  in
  let rec cut_branch access_edge node =
    let _, in_edges =
      List.partition_tf (LTS.pred_e proc_data.lts node)
        ~f:(fun (_, (edge_data : LTS.EdgeData.t), _) -> edge_data.backedge)
    in
    LTS.remove_edge_e proc_data.lts access_edge ;
    if Int.equal (List.length in_edges) 1 then (
      (* Only 1 incoming edge, can cut the branch *)
      (* let in_edge = List.hd_exn in_edges in
         LTS.remove_edge_e proc_data.lts in_edge; *)
      let out_edges = LTS.succ_e proc_data.lts node in
      List.iter out_edges ~f:(fun ((_, _, dst) as out_edge) -> cut_branch out_edge dst) ;
      LTS.remove_vertex proc_data.lts node )
  in
  let remove_unreachable node =
    if LTS.mem_vertex proc_data.lts node then
      let out_edges = LTS.succ_e proc_data.lts node in
      match node with
      | LTS.Node.Prune (_, loc, _) ->
          List.iter out_edges ~f:(fun ((_, (edge_data : LTS.EdgeData.t), dst) as edge) ->
              let dnf_condition_opt =
                List.map edge_data.conditions ~f:(fun and_terms -> create_and_term and_terms)
                |> List.reduce ~f:(fun x y -> EdgeExp.T.BinOp (Binop.LOr, x, y))
              in
              let always_false =
                match dnf_condition_opt with
                | Some condition ->
                    let always_false =
                      EdgeExp.always_false condition AccessExpressionMap.empty tenv active_prover
                    in
                    debug_log "[%a] Always FALSE: %B@," EdgeExp.pp condition always_false ;
                    always_false
                | _ ->
                    false
              in
              if always_false then (
                let msg = F.asprintf "Prune branch '%a' is always false" LTS.pp_edge edge in
                report_issue IssueType.looper_condition_always_false ~loc msg ;
                cut_branch edge dst ) )
      | _ ->
          ()
  in
  let prune_nodes =
    LTS.NodeSet.filter
      (fun node -> match node with LTS.Node.Prune _ -> true | _ -> false)
      proc_data.nodes
  in
  LTS.NodeSet.iter (fun prune_node -> remove_unreachable prune_node) prune_nodes ;
  (* debug_log "Normalized condition: " ;
     let condition_always_false =
       match normalized_cond_opt with
       | Some condition ->
           debug_log "%a@," EdgeExp.pp condition ;
           false
           (* try
                EdgeExp.always_false condition graph_data.const_assignments graph_data.tenv
                  graph_data.active_prover
              with _ ->
                debug_log "[EdgeExp.always_false] Failed to determine@," ;
                false *)
       | None ->
           debug_log "None@," ;
           false
     in *)
  debug_log "@]" ;
  {proc_data with edges}
