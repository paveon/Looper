open! IStd

module F = Format
module L = Logging
module Domain = LooperDomain


module Payload = SummaryPayload.Make (struct
  type t = Domain.EdgeExp.summary

  let field = Payloads.Fields.looper
end)


let log : ('a, Format.formatter, unit) format -> 'a = fun fmt -> F.printf fmt

module GraphData = struct
  type t = {
    last_node: Domain.DCP.Node.t;
    nodes: Domain.DCP.NodeSet.t;
    edges: Domain.DCP.EdgeSet.t;
    edge_data: Domain.DCP.EdgeData.t;
    ident_map: Domain.EdgeExp.t Ident.Map.t;
    field_map: Pvar.t Fieldname.Map.t;
    node_map: Domain.DCP.Node.t Procdesc.NodeMap.t;
    potential_norms: Domain.EdgeExp.Set.t;
    norms: Domain.EdgeExp.Set.t;
    loop_heads: Location.t list;
    loop_modified: Domain.AccessSet.t;
    
    scope_locals: Pvar.Set.t list;
    locals: Pvar.Set.t;
    formals: Pvar.Set.t;
    type_map: Typ.t Domain.PvarMap.t;
    tenv: Tenv.t;
    summary: Summary.t;
  }

  let make tenv proc_desc summary start_node = 
    let open Domain in
    let locals = Procdesc.get_locals proc_desc in
    let formals = Procdesc.get_pvar_formals proc_desc in

    let proc_name = Procdesc.get_proc_name proc_desc in
    let locals, type_map = List.fold locals ~init:(Pvar.Set.empty, PvarMap.empty) ~f:
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
    log "Locals: %a\n" Pvar.Set.pp locals;
    {
    last_node = start_node;
    nodes = Domain.DCP.NodeSet.singleton start_node;
    edges = Domain.DCP.EdgeSet.empty;
    edge_data = Domain.DCP.EdgeData.empty;
    ident_map = Ident.Map.empty;
    (* ident_map2 = Ident.Map.empty; *)
    field_map = Fieldname.Map.empty;
    node_map = Procdesc.NodeMap.empty;
    potential_norms = Domain.EdgeExp.Set.empty;
    norms = Domain.EdgeExp.Set.empty;
    loop_heads = [];
    loop_modified = Domain.AccessSet.empty;

    (* locals = locals; *)
    scope_locals = [Pvar.Set.empty];
    locals = Pvar.Set.empty;
    formals = formals;
    type_map = type_map;
    tenv = tenv;
    summary = summary
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



module TransferFunctions = struct
  (* Take an abstract state and instruction, produce a new abstract state *)
  let exec_instr : GraphData.t -> Sil.instr -> GraphData.t = fun graph_data instr ->
    let open Domain in

    match instr with
    | Sil.Prune (cond, loc, branch, kind) -> (
      (* log "[PRUNE (%s)] (%a) | %a\n" (Sil.if_kind_to_string kind) Location.pp loc Exp.pp cond; *)
      (* let cond = EdgeExp.of_exp cond graph_data.ident_map2 graph_data.type_map in *)
      let cond = EdgeExp.of_exp cond graph_data.ident_map graph_data.type_map in
      log "[PRUNE (%s)] (%a) | %a\n" (Sil.if_kind_to_string kind) Location.pp loc EdgeExp.pp cond;

      let normalized_cond = EdgeExp.normalize_condition cond graph_data.tenv in

      let in_loop = not (List.is_empty graph_data.loop_heads) in
      let is_int_expr = EdgeExp.is_int normalized_cond graph_data.type_map graph_data.tenv in
      let loop_prune = is_loop_prune kind in

      let graph_data = if branch && (loop_prune || in_loop) && is_int_expr then (
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
            if not loop_prune && not is_modified then (
              (* Prune on loop path but not loop head. Norm is only potential,
              * must be confirmed by increment/decrement on this loop path *)
              { graph_data with potential_norms = EdgeExp.Set.add new_norm graph_data.potential_norms; }
            ) else (
              let init_norms = EdgeExp.Set.add new_norm graph_data.norms in
              { graph_data with norms = init_norms; }
            )
          ) 
          | None -> graph_data
        )
        | _ -> L.(die InternalError)"Unsupported PRUNE expression!"
      ) else graph_data
      in

      { graph_data with
        loop_heads = if branch then [loc] @ graph_data.loop_heads else graph_data.loop_heads;
        scope_locals = if branch then [Pvar.Set.empty] @ graph_data.scope_locals else graph_data.scope_locals;

        edge_data = { graph_data.edge_data with
          branch_info = Some (kind, branch, loc);
          conditions = EdgeExp.Set.add normalized_cond graph_data.edge_data.conditions;
        };
      }
    )
    | Sil.Store {e1=lhs; typ; e2=rhs; loc} -> (
      (* log "[STORE] (%a) | %a = %a\n" Location.pp loc Exp.pp lhs Exp.pp rhs; *)
      match lhs with
      | Exp.Lvar pvar when Pvar.is_clang_tmp pvar -> (
        log "clang_tmp\n";
        graph_data
      )
      | Exp.Lvar pvar when Pvar.is_frontend_tmp pvar -> (
        log "frontend_tmp\n";
        graph_data
      )
      | Exp.Lvar pvar when Pvar.is_ssa_frontend_tmp pvar -> (
        log "ssa_frontend_tmp\n";
        graph_data
      )
      | Exp.Lvar pvar when Pvar.is_cpp_temporary pvar -> (
        log "cpp_temporary\n";
        graph_data
      )
      | _ -> (
        let id_resolver (var : Var.t) = match var with
        | Var.LogicalVar id -> (match Ident.Map.find id graph_data.ident_map with
          | EdgeExp.Access path -> Some path
          | _ -> None
        )
        | Var.ProgramVar _ -> None
        in

        let lhs_access = Option.value_exn
          (AccessPath.of_lhs_exp ~include_array_indexes:false lhs typ ~f_resolve_id:id_resolver)
        in

        let rhs_exp = EdgeExp.of_exp rhs graph_data.ident_map graph_data.type_map in
        let rhs_exp = match rhs_exp with
        | EdgeExp.Call (_, _, _, summary) -> (
          match summary.return_bound with
          | Some ret_bound -> ret_bound
          | None -> rhs_exp
        )
        | _ -> rhs_exp
        in

        log "[STORE] (%a) | %a = %a\n" Location.pp loc AccessPath.pp lhs_access EdgeExp.pp rhs_exp;

        (* TODO: rewrite with recursion, this is nasty *)
        (* Substitute rexp based on previous assignments,
          * eg. [beg = i; end = beg;] becomes [beg = i; end = i] *)
        let rec substitute exp = match exp with
        | EdgeExp.Access access -> DCP.EdgeData.get_assignment_rhs graph_data.edge_data access
        | EdgeExp.BinOp (op, lexp, rexp) -> (
          let lexp, rexp = substitute lexp, substitute rexp in
          match lexp, rexp with
          | EdgeExp.Const Const.Cint c1, EdgeExp.Const Const.Cint c2 -> EdgeExp.eval op c1 c2
          | _ -> exp
        )
        | EdgeExp.UnOp (op, subexp, typ) -> EdgeExp.UnOp (op, substitute subexp, typ)
        | EdgeExp.Call (ret_typ, procname, args, summary) -> (
          let args = List.map args ~f:(fun (arg, typ) -> (substitute arg, typ)) in
          EdgeExp.Call (ret_typ, procname, args, summary)
        )
        | EdgeExp.Max args -> EdgeExp.Max (List.map args ~f:substitute)
        | EdgeExp.Min args -> EdgeExp.Max (List.map args ~f:substitute)
        | _ -> exp
        in
        let rhs_exp = match rhs_exp with
        | EdgeExp.BinOp (Binop.PlusA _, EdgeExp.Access rhs_access, (EdgeExp.Const (Const.Cint rhs_int) as rhs_c)) -> (
          (* [BINOP] Access + Const *)
          match (DCP.EdgeData.get_assignment_rhs graph_data.edge_data rhs_access) with
          | EdgeExp.Access _ as assignment_rhs -> EdgeExp.BinOp (Binop.PlusA None, assignment_rhs, rhs_c)
          | EdgeExp.BinOp (Binop.PlusA _, lexp, EdgeExp.Const (Const.Cint assignment_rhs_int)) -> (
            (* [BINOP] (PVAR + C1) + C2 -> PVAR + (C1 + C2) *)
            let const = EdgeExp.Const (Const.Cint (IntLit.add rhs_int assignment_rhs_int)) in
            EdgeExp.BinOp (Binop.PlusA None, lexp, const)
          )
          | assigned -> (
            (* L.(die InternalError)"Unsupported exp substitution" *)
            (* Substitute without simplifying *)
            L.internal_error "[STORE] Substitution without simplification: %a -> %a\n" 
              AccessPath.pp rhs_access EdgeExp.pp assigned;
            EdgeExp.BinOp (Binop.PlusA None, assigned, rhs_c)
          )
        )
        | EdgeExp.BinOp (op, EdgeExp.Access rhs_access1, EdgeExp.Access rhs_access2) -> (
          let rhs_subst1 = DCP.EdgeData.get_assignment_rhs graph_data.edge_data rhs_access1 in
          let rhs_subst2 = DCP.EdgeData.get_assignment_rhs graph_data.edge_data rhs_access2 in
          EdgeExp.BinOp (op, rhs_subst1, rhs_subst2)
        )
        | EdgeExp.Access rhs_access -> (
          DCP.EdgeData.get_assignment_rhs graph_data.edge_data rhs_access
        )
        | _ -> rhs_exp
        in

        let is_plus_minus_op op = match op with
        | Binop.PlusA _ | Binop.MinusA _ -> true | _ -> false
        in

        (* Check if we can add new norm to the norm set *)
        let graph_data = match rhs_exp with 
        | EdgeExp.BinOp (op, (EdgeExp.Access rhs_access as rhs_access_exp), EdgeExp.Const (Const.Cint _)) -> (
          if AccessPath.equal lhs_access rhs_access then (
            if is_plus_minus_op op && EdgeExp.Set.mem rhs_access_exp graph_data.potential_norms then (
              { graph_data with
                potential_norms = EdgeExp.Set.remove rhs_access_exp graph_data.potential_norms;
                norms = EdgeExp.Set.add rhs_access_exp graph_data.norms;
              }
            ) else (
              graph_data
            )
          ) else graph_data
        )
        | _ -> graph_data
        in
        
        let initial_norms = match lhs with
        | Exp.Lvar pvar when Pvar.is_return pvar -> EdgeExp.Set.add (EdgeExp.Access lhs_access) graph_data.norms
        | _ -> graph_data.norms
        in

        let loop_modified = match List.is_empty graph_data.loop_heads with
        | false -> AccessSet.add lhs_access graph_data.loop_modified
        | _ -> graph_data.loop_modified 
        in

        { graph_data with
          edge_data = DCP.EdgeData.add_assignment graph_data.edge_data lhs_access rhs_exp;
          norms = initial_norms;
          loop_modified = loop_modified;
        }
      )
    )
    | Sil.Load {id; e; typ; loc;} -> (
      log "[LOAD] (%a) | %a = %a\n" Location.pp loc Ident.pp id Exp.pp e;
      let map_ident exp = match exp with
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
        | _ -> graph_data.ident_map
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
      log "[CALL] (%a) | %a\n" Location.pp loc Procname.pp callee_pname;
      let ret_pvar = Pvar.mk_abduced_ret callee_pname loc in
      let graph_data = { graph_data with
        type_map = PvarMap.add ret_pvar ret_typ graph_data.type_map;
      }
      in

      match Payload.read ~caller_summary:graph_data.summary ~callee_pname:callee_pname with
      | Some new_summary -> (
        (* Replace all idents in call arguments with pvars and return these pvars as norms *)
        let args, arg_norms = List.fold args ~init:([], EdgeExp.Set.empty) ~f:(fun (args, norms) (arg, typ) ->
          let arg = EdgeExp.of_exp arg graph_data.ident_map graph_data.type_map in
          let arg_norms = EdgeExp.get_accesses arg in
          [(arg, typ)] @ args, EdgeExp.Set.union arg_norms norms
          )
        in

        log "   FormalMap: %a\n" FormalMap.pp new_summary.formal_map;
        log "   Formal Bound: %a\n" EdgeExp.pp new_summary.bound;
        let subst_bound = EdgeExp.subst new_summary.bound args new_summary.formal_map in
        let subst_ret_bound = match new_summary.return_bound with
        | Some ret_bound -> Some (EdgeExp.subst ret_bound args new_summary.formal_map)
        | None -> None
        in
        log "   Instantiated Bound: %a\n" EdgeExp.pp subst_bound;
        let new_summary = { new_summary with 
          bound = subst_bound;
          return_bound = subst_ret_bound;
        } 
        in
        let call = EdgeExp.Call (ret_typ, callee_pname, args, new_summary) in
        let edge_data = { graph_data.edge_data with 
          calls = CallSiteSet.add (call, loc) graph_data.edge_data.calls
        }
        in
        { graph_data with 
          norms = EdgeExp.Set.union graph_data.norms arg_norms;
          ident_map = Ident.Map.add ret_id call graph_data.ident_map;
          edge_data = edge_data;
        }
      )
      | None -> (
        let ret_access = EdgeExp.Access (AccessPath.of_pvar ret_pvar ret_typ) in
        { graph_data with ident_map = Ident.Map.add ret_id ret_access graph_data.ident_map }
      )
    )
    | Metadata metadata -> (match metadata with
      | VariableLifetimeBegins (pvar, _, _) -> (
        let scope_locals = match graph_data.scope_locals with
        | scope::tail -> [Pvar.Set.add pvar scope] @ tail
        | [] -> []
        in
        { graph_data with 
          locals = Pvar.Set.add pvar graph_data.locals;
          scope_locals = scope_locals;
        }
      )
      | _ -> graph_data
    )
    | instr -> (
      log "[UNKNOWN INSTRUCTION] %a\n" Sil.(pp_instr ~print_types:true Pp.text) instr;
      assert(false)
    )
end


module GraphConstructor = struct
  let exec_node node graph_data =
    let rev_instrs = IContainer.to_rev_list ~fold:Instrs.fold (Procdesc.Node.get_instrs node) in
    List.fold (List.rev rev_instrs) ~init:graph_data ~f:TransferFunctions.exec_instr

  let rec traverseCFG : Procdesc.t -> Procdesc.Node.t -> Procdesc.NodeSet.t -> GraphData.t -> (Procdesc.NodeSet.t * GraphData.t) = 
  fun proc_desc node visited graph_data -> (
    let open Domain in

    let is_loop_head = Procdesc.is_loop_head proc_desc node in
    if Procdesc.NodeSet.mem node visited 
    then (
      (* log "Visited Node %a : %s\n" Procdesc.Node.pp node (pp_nodekind (Procdesc.Node.get_kind node)); *)
      let preds = Procdesc.Node.get_preds node in
      let graph_data = if is_join_node node || List.length preds > 1 then (
        let edge_data = DCP.EdgeData.add_invariants graph_data.edge_data graph_data.locals graph_data.type_map in
        let edge_data = if is_loop_head then DCP.EdgeData.set_backedge edge_data else edge_data in
        let node = Procdesc.NodeMap.find node graph_data.node_map in
        (* log "Mapped node %a\n" DCP.Node.pp node; *)
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
      (* log "Node %a : %s\n" Procdesc.Node.pp node (pp_nodekind (Procdesc.Node.get_kind node)); *)

      let preds = Procdesc.Node.get_preds node in
      let graph_data = if List.length preds > 1 && not is_loop_head then (
        (* Join node *)
        let join_node = DCP.Node.Join (Procdesc.Node.get_loc node) in
        let edge_data = DCP.EdgeData.add_invariants graph_data.edge_data graph_data.locals graph_data.type_map in
        let new_edge = DCP.E.create graph_data.last_node edge_data join_node in
        (* log "Locals: %a\n" Pvar.Set.pp graph_data.locals;
        log "Scope locals:\n"; List.iter graph_data.scope_locals ~f:(fun scope -> log "  %a\n" Pvar.Set.pp scope; ); *)
        { graph_data with 
          nodes = DCP.NodeSet.add join_node graph_data.nodes;
          edges = DCP.EdgeSet.add new_edge graph_data.edges;
          last_node = join_node;
          edge_data = DCP.EdgeData.empty;

          locals = Pvar.Set.diff graph_data.locals (List.hd_exn graph_data.scope_locals);
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
        let if_kind = match Procdesc.Node.get_kind branch_node with
        | Procdesc.Node.Prune_node (_, kind, _) -> kind
        | _ -> assert(false)
        in
        let prune_node = DCP.Node.Prune (if_kind, loc) in
        let edge_data = DCP.EdgeData.add_invariants graph_data.edge_data graph_data.locals graph_data.type_map in
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
        let edge_data = DCP.EdgeData.add_invariants graph_data.edge_data graph_data.locals graph_data.type_map in
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
          let graph_data = { graph_data with
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


  let create_lts : Tenv.t -> Procdesc.t -> Summary.t -> GraphData.t = 
  fun tenv proc_desc summary -> (
    let proc_name = Procdesc.get_proc_name proc_desc in
    let begin_loc = Procdesc.get_loc proc_desc in
    let start_node = Procdesc.get_start_node proc_desc in
    let dcp_start_node = Domain.DCP.Node.Start (proc_name, begin_loc) in
    let graph_data = GraphData.make tenv proc_desc summary dcp_start_node in
    snd (traverseCFG proc_desc start_node Procdesc.NodeSet.empty graph_data)
  )
end
