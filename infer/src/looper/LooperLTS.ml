(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)


open! IStd
open LooperUtils

module F = Format
module L = Logging
module DCP = DifferenceConstraintProgram


let debug_log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.fprintf (List.hd_exn !debug_fmt) fmt


module GraphData = struct
  type t = {
    last_node: DCP.Node.t;
    loophead_stack: Procdesc.Node.t Stack.t;
    nodes: DCP.NodeSet.t;
    edges: DCP.EdgeSet.t;
    edge_data: DCP.EdgeData.t;
    ident_map: EdgeExp.t Ident.Map.t;
    node_map: DCP.Node.t Procdesc.NodeMap.t;
    potential_norms: EdgeExp.Set.t;
    norms: EdgeExp.Set.t;
    loop_heads: Location.t list;
    loop_modified: AccessSet.t;
    
    scope_locals: AccessSet.t list;
    locals: AccessSet.t;
    formals: Pvar.Set.t;
    type_map: Typ.t PvarMap.t;
    tenv: Tenv.t;
    analysis_data: LooperSummary.t InterproceduralAnalysis.t;
    call_summaries: LooperSummary.t Location.Map.t;
  }

  let make tenv proc_desc analysis_data start_node = 
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
    let formals, type_map = List.fold formals ~init:(Pvar.Set.empty, type_map) ~f:(fun (formals, type_map) (pvar, typ) ->
      let type_map = PvarMap.add pvar typ type_map in
      let formals = Pvar.Set.add pvar formals in
      formals, type_map
    )
    in
    {
      last_node = start_node;
      loophead_stack = Stack.create ();
      nodes = DCP.NodeSet.singleton start_node;
      edges = DCP.EdgeSet.empty;
      edge_data = DCP.EdgeData.empty;
      ident_map = Ident.Map.empty;
      node_map = Procdesc.NodeMap.empty;
      potential_norms = EdgeExp.Set.empty;
      norms = EdgeExp.Set.empty;
      loop_heads = [];
      loop_modified = AccessSet.empty;

      scope_locals = [AccessSet.empty];
      locals = AccessSet.empty;
      formals = formals;
      type_map = type_map;
      tenv = tenv;
      analysis_data = analysis_data;
      call_summaries = Location.Map.empty;
    }
end

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

let is_decl_node node = match Procdesc.Node.get_kind node with
| Procdesc.Node.Stmt_node DeclStmt -> true
| _ -> false


module GraphConstructor = struct
  let exec_instr : GraphData.t -> Sil.instr -> GraphData.t = fun graph_data instr ->
    let ap_id_resolver = EdgeExp.access_path_id_resolver graph_data.ident_map in

    let is_loop_prune (kind : Sil.if_kind) = match kind with
    | Ik_dowhile | Ik_for | Ik_while -> true
    | _ -> false
    in


    match instr with
    | Prune (cond, loc, branch, kind) -> (
      (* debug_log "[PRUNE (%s)] (%a) | %a\n" (Sil.if_kind_to_string kind) Location.pp loc Exp.pp cond; *)
      let cond = EdgeExp.of_exp cond graph_data.ident_map (Typ.mk (Tint IBool)) graph_data.type_map in
      debug_log "[PRUNE (%s)] (%a) | %a\n" (Sil.if_kind_to_string kind) Location.pp loc EdgeExp.pp cond;
      let normalized_cond = EdgeExp.normalize_condition cond graph_data.tenv in

      let in_loop = not (List.is_empty graph_data.loop_heads) in
      let is_int_expr = EdgeExp.is_int normalized_cond graph_data.type_map graph_data.tenv in

      let graph_data = if branch && (is_loop_prune kind || in_loop) && is_int_expr then (
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
            | Binop.Ge -> Some (EdgeExp.BinOp (Binop.PlusA None, (process_gt lexp rexp), EdgeExp.one))
            | _ -> None
          in
          match process_op op with
          | Some new_norm -> (
            let is_modified = match new_norm with
            | EdgeExp.Access access -> AccessSet.mem access graph_data.loop_modified
            | _ -> false
            in
            if not (is_loop_prune kind) && not is_modified then (
              (* Prune on loop path but not loop head. Norm is only potential,
              * must be confirmed by increment/decrement on this loop path *)
              { graph_data with potential_norms = EdgeExp.Set.add new_norm graph_data.potential_norms; }
            ) else (
              let init_norms = EdgeExp.Set.add (EdgeExp.simplify new_norm) graph_data.norms in
              { graph_data with norms = init_norms; } : GraphData.t
            )
          ) 
          | None -> graph_data
        )
        | _ -> L.(die InternalError)"Unsupported PRUNE expression!"
      ) else graph_data
      in

      { graph_data with
        loop_heads = if branch then [loc] @ graph_data.loop_heads else graph_data.loop_heads;
        scope_locals = if branch then [AccessSet.empty] @ graph_data.scope_locals else graph_data.scope_locals;

        edge_data = { graph_data.edge_data with
          branch_info = Some (kind, branch, loc);
          conditions = EdgeExp.Set.add normalized_cond graph_data.edge_data.conditions;
        };
      }
    )
    | Store {e1=lhs; typ; e2=rhs; loc} -> (
      debug_log "[STORE] (%a) | %a = %a\n" Location.pp loc Exp.pp lhs Exp.pp rhs;
      match lhs with
      | Exp.Lvar pvar when Pvar.is_clang_tmp pvar -> (
        debug_log "clang_tmp\n";
        graph_data
      )
      | Exp.Lvar pvar when Pvar.is_ssa_frontend_tmp pvar -> (
        debug_log "[SSA_FRONTEND_TMP] %a\n" Pvar.pp_value pvar;
        graph_data
      )
      | Exp.Lvar pvar when Pvar.is_cpp_temporary pvar -> (
        debug_log "[CPP_TEMPORARY] %a\n" Pvar.pp_value pvar;
        graph_data
      )
      | _ -> (
        let lhs_access = Option.value_exn (access_of_lhs_exp ~include_array_indexes:true lhs typ ~f_resolve_id:ap_id_resolver) in
        let lhs_access_exp = EdgeExp.Access lhs_access in

        let rhs_exp = match EdgeExp.of_exp rhs graph_data.ident_map typ graph_data.type_map with
        | EdgeExp.Call (_, _, _, loc) as call -> (
          match Location.Map.find_opt loc graph_data.call_summaries with
          | Some summary -> (
            match summary.return_bound with
            | Some ret_bound -> ret_bound
            | None -> assert(false)
          )
          | None -> call
        )
        | exp -> (
          let exp, _ = EdgeExp.map_accesses exp ~f:(fun access _ -> 
            DCP.EdgeData.get_assignment_rhs graph_data.edge_data access, None
          ) None
          in
          
          EdgeExp.simplify exp
        )
        in

        debug_log "[STORE] (%a) | %a = %a\n" Location.pp loc EdgeExp.pp lhs_access_exp EdgeExp.pp rhs_exp;

        let is_plus_minus_op op = match op with
        | Binop.PlusA _ | Binop.MinusA _ -> true 
        | _ -> false
        in

        (* Check if we can add new norm to the norm set *)
        let graph_data = match rhs_exp with 
        | EdgeExp.BinOp (op, (EdgeExp.Access _ as rhs_access_exp), EdgeExp.Const (Const.Cint _)) -> (
          if EdgeExp.equal lhs_access_exp rhs_access_exp then (
            if is_plus_minus_op op && EdgeExp.Set.mem rhs_access_exp graph_data.potential_norms then (
              { graph_data with
                potential_norms = EdgeExp.Set.remove rhs_access_exp graph_data.potential_norms;
                norms = EdgeExp.Set.add (EdgeExp.simplify rhs_access_exp) graph_data.norms;
              }
            ) else (
              graph_data
            )
          ) else graph_data
        )
        | _ -> graph_data
        in
        
        let graph_data = match lhs with
        | Exp.Lvar pvar when Pvar.is_return pvar -> (
          let new_norms = EdgeExp.Set.singleton lhs_access_exp in
          let new_norms = match rhs_exp with
          | EdgeExp.Inf
          | EdgeExp.Call _
          | EdgeExp.Const _
          | EdgeExp.Max _
          | EdgeExp.Min _ -> new_norms
          | _ -> EdgeExp.Set.add (EdgeExp.simplify rhs_exp) new_norms
          in
          { graph_data with 
            norms = EdgeExp.Set.union graph_data.norms new_norms;
            locals = AccessSet.add lhs_access graph_data.locals;
            type_map = PvarMap.add pvar typ graph_data.type_map
          }
        )
        | _ -> graph_data
        in

        let is_top_scope_local access = List.for_all graph_data.scope_locals ~f:(fun scope ->
          not (AccessSet.mem access scope)
        )
        in
        
        let locals = if is_top_scope_local lhs_access 
        then AccessSet.add lhs_access graph_data.locals
        else graph_data.locals
        in

        let graph_data = match lhs_access with
        | (base, access_list) when not (List.is_empty access_list) -> (
          let base_access = ((base, []) : AccessPath.t) in
          debug_log "Adding access '%a' to scope locals\n" AccessPath.pp lhs_access;
          if AccessSet.mem base_access graph_data.locals then (
            let scope_locals = match graph_data.scope_locals with
            | scope::tail -> [AccessSet.add lhs_access scope] @ tail
            | [] -> [AccessSet.singleton lhs_access]
            in
            { graph_data with 
              locals = AccessSet.add lhs_access graph_data.locals;
              scope_locals = scope_locals;
            }
          ) 
          else graph_data
        )
        | _ -> graph_data
        in

        let loop_modified = match List.is_empty graph_data.loop_heads with
        | false -> AccessSet.add lhs_access graph_data.loop_modified
        | _ -> graph_data.loop_modified 
        in

        { graph_data with
          locals = locals;
          edge_data = DCP.EdgeData.add_assignment graph_data.edge_data lhs_access rhs_exp;
          loop_modified = loop_modified;
        }
      )
    )
    | Load {id; e; typ; loc;} -> (
      debug_log "[LOAD] (%a) | %a = %a\n" Location.pp loc Ident.pp id Exp.pp e;
      let map_ident exp = match exp with
      | Exp.Lindex _ -> (
        let accesses = access_of_exp ~include_array_indexes:true exp typ ~f_resolve_id:ap_id_resolver in
        assert (Int.equal (List.length accesses) 1);
        let access = List.hd_exn accesses in
        Ident.Map.add id (EdgeExp.Access access) graph_data.ident_map
      )
      | Exp.Lfield (struct_exp, name, _) -> (
        match struct_exp with
        | Exp.Var struct_id -> (
          match Ident.Map.find struct_id graph_data.ident_map with
          | EdgeExp.Access path -> (
            let access = AccessPath.FieldAccess name in
            let ext_path = EdgeExp.Access (AccessPath.append path [access]) in
            Ident.Map.add id ext_path graph_data.ident_map
          )
          | _ -> assert(false)
        )
        | _ -> assert(false)
      )
      | Exp.Lvar pvar -> (
        let access = EdgeExp.Access (AccessPath.of_pvar pvar typ) in
        Ident.Map.add id access graph_data.ident_map
      )
      | Exp.Var rhs_id -> (
        let exp = Ident.Map.find rhs_id graph_data.ident_map in
        Ident.Map.add id exp graph_data.ident_map
      )
      | _ -> L.(die InternalError)"Unsupported LOAD lhs-expression type!"
      in

      { graph_data with ident_map = map_ident e }
    )
    | Call ((ret_id, ret_typ), Exp.Const (Const.Cfun callee_pname), args, loc, _) -> (
      debug_log "[CALL] (%a) | %a\n" Location.pp loc Procname.pp callee_pname;
      let ret_pvar = Pvar.mk_abduced_ret callee_pname loc in
      let graph_data = { graph_data with
        type_map = PvarMap.add ret_pvar ret_typ graph_data.type_map;
      }
      in

      let rec substitute edge_data exp = match exp with
      | EdgeExp.Access access -> DCP.EdgeData.get_assignment_rhs edge_data access
      | EdgeExp.BinOp (op, lexp, rexp) -> (
        let lexp, rexp = substitute edge_data lexp, substitute edge_data rexp in
        match lexp, rexp with
        | EdgeExp.Const Const.Cint c1, EdgeExp.Const Const.Cint c2 -> 
          EdgeExp.Const (Const.Cint (EdgeExp.eval_consts op c1 c2))
        | _ -> exp
      )
      | EdgeExp.UnOp (op, subexp, typ) -> EdgeExp.UnOp (op, substitute edge_data subexp, typ)
      | EdgeExp.Call (ret_typ, procname, args, loc) -> (
        let args = List.map args ~f:(fun (arg, typ) -> (substitute edge_data arg, typ)) in
        EdgeExp.Call (ret_typ, procname, args, loc)
      )
      | EdgeExp.Max args -> EdgeExp.Max (List.map args ~f:(substitute edge_data))
      | EdgeExp.Min args -> EdgeExp.Max (List.map args ~f:(substitute edge_data))
      | _ -> exp
      in

      let args, arg_norms = List.fold args ~init:([], EdgeExp.Set.empty) ~f:(fun (args, norms) (arg, arg_typ) ->
        let arg = EdgeExp.of_exp arg graph_data.ident_map arg_typ graph_data.type_map in
        debug_log "Simplify argument expression: %a\n" EdgeExp.pp arg;
        let arg = substitute graph_data.edge_data arg |> EdgeExp.simplify in
        let arg_norms = EdgeExp.get_accesses arg in
        (arg, arg_typ) :: args, if Typ.is_int arg_typ then EdgeExp.Set.union arg_norms norms else norms
      )
      in

      let args = List.rev args in
      let call = EdgeExp.Call (ret_typ, callee_pname, args, loc) in
      let payload_opt = graph_data.analysis_data.analyze_dependency callee_pname in
      let call_summaries = match payload_opt with
      | Some (_, payload) -> (
        let subst_ret_bound = match payload.return_bound with
        | Some ret_bound -> Some (EdgeExp.subst ret_bound args payload.formal_map)
        | None -> None
        in
        let summary = { payload with return_bound = subst_ret_bound } in
        Location.Map.add loc summary graph_data.call_summaries
      )
      | None -> graph_data.call_summaries
      in

      { graph_data with 
        norms = EdgeExp.Set.union graph_data.norms arg_norms;
        ident_map = Ident.Map.add ret_id call graph_data.ident_map;
        call_summaries = call_summaries;
        edge_data = { graph_data.edge_data with 
          calls = EdgeExp.Set.add call graph_data.edge_data.calls
        }
      }
    )
    | Metadata metadata -> (match metadata with
      | VariableLifetimeBegins (pvar, typ, loc) -> (
        debug_log "[VariableLifetimeBegins] (%a) | %a\n" Location.pp loc Pvar.pp_value pvar;
        let pvar_access = AccessPath.of_pvar pvar typ in
        let scope_locals = match graph_data.scope_locals with
        | scope::tail -> (
          debug_log "[Scope variables] ";
          let variables = AccessSet.add pvar_access scope in
          AccessSet.iter (fun path -> debug_log "%a " AccessPath.pp path) variables;
          debug_log "\n";
          [variables] @ tail
        )
        | [] -> [AccessSet.singleton pvar_access]
        in
        { graph_data with 
          locals = AccessSet.add pvar_access graph_data.locals;
          scope_locals = scope_locals;
        }
      )
      | _ -> graph_data
    )
    | instr -> (
      debug_log "[UNKNOWN INSTRUCTION] %a\n" Sil.(pp_instr ~print_types:true Pp.text) instr;
      assert(false)
    )


  let exec_node node graph_data =
    let rev_instrs = IContainer.to_rev_list ~fold:Instrs.fold (Procdesc.Node.get_instrs node) in
    List.fold (List.rev rev_instrs) ~init:graph_data ~f:exec_instr


  let rec traverseCFG : Procdesc.t -> Procdesc.Node.t -> Procdesc.NodeSet.t -> GraphData.t -> (Procdesc.NodeSet.t * GraphData.t) = 
  fun proc_desc node visited graph_data -> (
    (* TODO: should probably POP loophead from stack if we encounter false branch later on.
     * Otherwise we are accumulating loop heads from previous loops but it doesn't seem to
     * affect the algorithm in any way. *)
    let is_loop_head = Procdesc.is_loop_head proc_desc node in
    let is_backedge = if is_loop_head then (
      debug_log "[LOOP HEAD] %a\n" Procdesc.Node.pp node;
      match Stack.top graph_data.loophead_stack with
      | Some last_loophead -> (
          debug_log "[PREVIOUS LOOP HEAD] %a\n" Procdesc.Node.pp last_loophead;
          if Procdesc.Node.equal last_loophead node then (
            let _ = Stack.pop_exn graph_data.loophead_stack in
            true
          ) else (
            Stack.push graph_data.loophead_stack node;
            false
          )
      )
      | None -> (
        Stack.push graph_data.loophead_stack node;
        false
      )
    ) else false
    in

    if Procdesc.NodeSet.mem node visited then (
      (* log "[Visited Node] %a : %s\n" Procdesc.Node.pp node (pp_nodekind (Procdesc.Node.get_kind node)); *)
      let preds = Procdesc.Node.get_preds node in
      let graph_data = if is_join_node node || List.length preds > 1 then (
        let edge_data = DCP.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
        let edge_data = if is_backedge then DCP.EdgeData.set_backedge edge_data else edge_data in
        let node = Procdesc.NodeMap.find node graph_data.node_map in
        (* log "Mapped node %a\n" DCP.Node.pp node; *)
        (* log "[New edge] %a ---> %a\n" DCP.Node.pp graph_data.last_node DCP.Node.pp node; *)
        let new_edge = DCP.E.create graph_data.last_node edge_data node in
        let edges = DCP.EdgeSet.add new_edge graph_data.edges in
        { graph_data with 
          edges = edges;
          edge_data = DCP.EdgeData.empty;
        }
      )
      else graph_data
      in
      (visited, graph_data)
    )
    else (
      let visited = Procdesc.NodeSet.add node visited in
      (* log "[Node] %a : %s\n" Procdesc.Node.pp node (pp_nodekind (Procdesc.Node.get_kind node)); *)

      let preds = Procdesc.Node.get_preds node in
      let graph_data = if List.length preds > 1 && not is_loop_head then (
        (* Join node *)
        let join_node_id = Procdesc.Node.get_id node in
        let join_node = DCP.Node.Join (Procdesc.Node.get_loc node, join_node_id) in
        (* log "[New Join] %a\n" DCP.Node.pp join_node; *)
        let edge_data = DCP.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
        let new_edge = DCP.E.create graph_data.last_node edge_data join_node in
        (* log "Locals: %a\n" Pvar.Set.pp graph_data.locals;
        log "Scope locals:\n"; List.iter graph_data.scope_locals ~f:(fun scope -> log "  %a\n" Pvar.Set.pp scope; ); *)
        { graph_data with 
          nodes = DCP.NodeSet.add join_node graph_data.nodes;
          edges = DCP.EdgeSet.add new_edge graph_data.edges;
          last_node = join_node;
          edge_data = DCP.EdgeData.empty;

          locals = AccessSet.diff graph_data.locals (List.hd_exn graph_data.scope_locals);
          scope_locals = List.tl_exn graph_data.scope_locals;
          node_map = Procdesc.NodeMap.add node join_node graph_data.node_map
        }
      ) else graph_data
      in


      (* Execute node instructions *)
      let graph_data = exec_node node graph_data in

      let successors = Procdesc.Node.get_succs node in
      let graph_data = if List.length successors > 1 then (
        (* Split node, create new DCP prune node *)
        let branch_node = List.hd_exn successors in
        let loc = Procdesc.Node.get_loc branch_node in
        let branch_node_id = Procdesc.Node.get_id branch_node in
        let if_kind = match Procdesc.Node.get_kind branch_node with
        | Procdesc.Node.Prune_node (_, kind, _) -> kind
        | _ -> assert(false)
        in
        let prune_node = DCP.Node.Prune (if_kind, loc, branch_node_id) in
        let edge_data = DCP.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
        let new_edge = DCP.E.create graph_data.last_node edge_data prune_node in
        let node_map = match List.hd preds with
        | Some pred when Procdesc.is_loop_head proc_desc pred -> Procdesc.NodeMap.add pred prune_node graph_data.node_map
        | _ -> graph_data.node_map
        in
        { graph_data with 
          nodes = DCP.NodeSet.add prune_node graph_data.nodes;
          edges = DCP.EdgeSet.add new_edge graph_data.edges;
          last_node = prune_node;
          edge_data = DCP.EdgeData.empty;
          node_map = node_map
        }
      ) 
      else graph_data
      in

      if is_exit_node node then (
        let exit_node = DCP.Node.Exit in
        let edge_data = DCP.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
        let edge_data = {edge_data with exit_edge = true } in
        let new_edge = DCP.E.create graph_data.last_node edge_data exit_node in
        let graph_data = { graph_data with 
          nodes = DCP.NodeSet.add exit_node graph_data.nodes;
          edges = DCP.EdgeSet.add new_edge graph_data.edges;
          last_node = exit_node;
          edge_data = DCP.EdgeData.empty;
        }
        in
        (visited, graph_data)
      )
      else (
        let last_node = graph_data.last_node in
        let loop_heads = graph_data.loop_heads in
        let locals = graph_data.locals in
        let scope_locals = graph_data.scope_locals in
        List.fold successors ~init:(visited, graph_data) ~f:(fun (visited, graph_data) next_node ->
          let graph_data : GraphData.t = { graph_data with
            last_node = last_node;
            loop_heads = loop_heads;
            locals = locals;
            scope_locals = scope_locals;
          }
          in
          traverseCFG proc_desc next_node visited graph_data
        )
      )
    )
  )


  let create_lts : Tenv.t -> Procdesc.t -> LooperSummary.t InterproceduralAnalysis.t -> GraphData.t = 
  fun tenv proc_desc summary -> (
    let proc_name = Procdesc.get_proc_name proc_desc in
    let begin_loc = Procdesc.get_loc proc_desc in
    let start_node = Procdesc.get_start_node proc_desc in
    let dcp_start_node = DCP.Node.Start (proc_name, begin_loc) in
    let graph_data = GraphData.make tenv proc_desc summary dcp_start_node in
    snd (traverseCFG proc_desc start_node Procdesc.NodeSet.empty graph_data)
  )
end
