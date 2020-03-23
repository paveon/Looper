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
    ident_map2: (Pvar.t * Typ.t) Ident.Map.t;
    field_map: Pvar.t Fieldname.Map.t;
    node_map: Domain.DCP.Node.t Procdesc.NodeMap.t;
    potential_norms: Domain.EdgeExp.Set.t;
    norms: Domain.EdgeExp.Set.t;
    loop_heads: Location.t list;
    loop_modified: Domain.PvarSet.t;
    
    scope_locals: Domain.PvarSet.t list;
    locals: Domain.PvarSet.t;
    formals: Domain.PvarSet.t;
    type_map: Typ.t Domain.PvarMap.t;
    summary: Summary.t;
  }

  let make proc_desc summary start_node = 
    let open Domain in
    let locals = Procdesc.get_locals proc_desc in
    let formals = Procdesc.get_pvar_formals proc_desc in

    let proc_name = Procdesc.get_proc_name proc_desc in
    let locals, type_map = List.fold locals ~init:(PvarSet.empty, PvarMap.empty) ~f:
    (fun (locals, type_map) (local : ProcAttributes.var_data) ->
      let pvar = Pvar.mk local.name proc_name in
      let type_map = PvarMap.add pvar local.typ type_map in
      let locals = PvarSet.add pvar locals in
      locals, type_map
    )
    in
    let formals, type_map = List.fold formals ~init:(PvarSet.empty, type_map) ~f:(fun (formals, type_map) (pvar, typ) ->
      let type_map = PvarMap.add pvar typ type_map in
      let formals = PvarSet.add pvar formals in
      formals, type_map
    )
    in
    log "Locals: %a\n" PvarSet.pp locals;
    {
    last_node = start_node;
    nodes = Domain.DCP.NodeSet.singleton start_node;
    edges = Domain.DCP.EdgeSet.empty;
    edge_data = Domain.DCP.EdgeData.empty;
    ident_map = Ident.Map.empty;
    ident_map2 = Ident.Map.empty;
    field_map = Fieldname.Map.empty;
    node_map = Procdesc.NodeMap.empty;
    potential_norms = Domain.EdgeExp.Set.empty;
    norms = Domain.EdgeExp.Set.empty;
    loop_heads = [];
    loop_modified = Domain.PvarSet.empty;

    (* locals = locals; *)
    scope_locals = [Domain.PvarSet.empty];
    locals = PvarSet.empty;
    formals = formals;
    type_map = type_map;
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
  let exec_instr : Procdesc.t -> Procdesc.Node.t -> GraphData.t -> Sil.instr -> GraphData.t =
  fun proc_desc node graph_data instr ->

    let open Domain in

    match instr with
    | Sil.Prune (cond, loc, branch, kind) -> (
      log "[PRUNE (%s)] (%a) | %a\n" (Sil.if_kind_to_string kind) Location.pp loc Exp.pp cond;
      let pvar_condition = EdgeExp.replace_idents cond graph_data.ident_map in
      log "[PRUNE (%s)] (%a) | %a\n" (Sil.if_kind_to_string kind) Location.pp loc EdgeExp.pp pvar_condition;

      let normalized_cond = EdgeExp.normalize_condition pvar_condition in

      let in_loop = not (List.is_empty graph_data.loop_heads) in
      let is_int_expr = EdgeExp.is_int normalized_cond graph_data.type_map in
      let loop_prune = is_loop_prune kind in

      let graph_data = if branch && (loop_prune || in_loop) && is_int_expr then (
        (* Derive norm from prune condition.
        * [x > y] -> [x - y] > 0
        * [x >= y] -> [x - y + 1] > 0 *)
        match normalized_cond with
        | EdgeExp.BinOp (op, lexp, rexp) -> (
          let process_gt lhs rhs =
            let lhs_is_zero = EdgeExp.is_zero lhs in
            let rhs_is_zero = EdgeExp.is_zero rhs in
            if lhs_is_zero && rhs_is_zero then EdgeExp.zero
            else if lhs_is_zero then EdgeExp.UnOp (Unop.Neg, rhs, None)
            else if rhs_is_zero then lhs
            else EdgeExp.BinOp (Binop.MinusA None, lhs, rhs)
          in

          let process_op op = match op with
            | Binop.Gt -> Some (process_gt lexp rexp)
            | Binop.Ge -> Some (EdgeExp.BinOp (Binop.PlusA None, (process_gt lexp rexp), EdgeExp.one))
            | _ -> None
          in
          match process_op op with
          | Some new_norm -> (
            let is_modified = match new_norm with
            | EdgeExp.Var pvar -> PvarSet.mem pvar graph_data.loop_modified
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
        scope_locals = if branch then [PvarSet.empty] @ graph_data.scope_locals else graph_data.scope_locals;

        edge_data = { graph_data.edge_data with
          branch_info = Some (kind, branch, loc);
          conditions = EdgeExp.Set.add normalized_cond graph_data.edge_data.conditions;
        };
      }
    )
    | Sil.Store {e1=lhs; typ; e2=rhs; loc} -> (
      log "Store: %a = %a\n" Exp.pp lhs Exp.pp rhs;
      let pvar_rexp = EdgeExp.replace_idents rhs graph_data.ident_map in
      let pvar_rexp = match pvar_rexp with
      | EdgeExp.Call (_, _, _, summary) -> (
        match summary.return_bound with
        | Some ret_bound -> ret_bound
        | None -> pvar_rexp
      )
      | _ -> pvar_rexp
      in
      let id_resolver (var : Var.t) = match var with
      | Var.LogicalVar id -> (
        let pvar, typ = Ident.Map.find id graph_data.ident_map2 in
        log "Resolving: %a\n" Var.pp var;
        Some (AccessPath.of_pvar pvar typ)
      )
      | Var.ProgramVar _ -> None
      in

      let path = AccessPath.of_lhs_exp ~include_array_indexes:false lhs typ ~f_resolve_id:id_resolver in
      (* Option.value_exn *)
      log "LHS PATH: %a\n" AccessPath.pp (Option.value_exn path);

      let rec extract_assigned_pvar lexp = match lexp with
      | Exp.Lvar pvar -> pvar
      | Exp.Lfield (field, name, typ) -> (
        let proc_name = Procdesc.get_proc_name proc_desc in
        let pvar = Pvar.mk (Mangled.from_string (Fieldname.to_string name)) proc_name in
        log "SUB EXP: %a\n" Exp.pp field;
        extract_assigned_pvar field
      )
      | Exp.Var id -> L.(die InternalError)"Unsupported assignment LHS: %a" Ident.pp id
      | Exp.UnOp (op, sub_exp, typ) -> L.(die InternalError)"Unsupported assignment LHS: UnOp"
      | Exp.BinOp (op, lhs, rhs) -> L.(die InternalError)"Unsupported assignment LHS: BinOp"
      | Exp.Const const -> L.(die InternalError)"Unsupported assignment LHS: Const"
      | Exp.Cast (typ, sub_exp) -> L.(die InternalError)"Unsupported assignment LHS: Cast"
      | Exp.Lindex (array_exp, index_exp) -> L.(die InternalError)"Unsupported assignment LHS: Lindex"
      | _ -> L.(die InternalError)"Unsupported assignment LHS"
      in

      let assigned_pvar = extract_assigned_pvar lhs in

      log "[STORE] (%a) | %a = %a\n" Location.pp loc Pvar.pp_value assigned_pvar EdgeExp.pp pvar_rexp;

      (* Substitute rexp based on previous assignments,
        * eg. [beg = i; end = beg;] becomes [beg = i; end = i] *)
      let pvar_rexp = match pvar_rexp with
      | EdgeExp.BinOp (Binop.PlusA _, EdgeExp.Var lexp, EdgeExp.Const (Const.Cint c1)) -> (
        (* [BINOP] PVAR + CONST *)
        match (DCP.EdgeData.get_assignment_rhs graph_data.edge_data lexp) with
        | EdgeExp.Var pvar -> (
          let const = EdgeExp.Const (Const.Cint c1) in
          EdgeExp.BinOp (Binop.PlusA None, EdgeExp.Var pvar, const)
        )
        | EdgeExp.BinOp (Binop.PlusA _, lexp, EdgeExp.Const (Const.Cint c2)) -> (
          (* [BINOP] (PVAR + C1) + C2 -> PVAR + (C1 + C2) *)
          let const = EdgeExp.Const (Const.Cint (IntLit.add c1 c2)) in
          EdgeExp.BinOp (Binop.PlusA None, lexp, const)
        )
        | _ -> (
          L.(die InternalError)"Unsupported exp substitution"
          (* pvar_rexp *)
        )
      )
      | EdgeExp.Var rhs_pvar -> (
        DCP.EdgeData.get_assignment_rhs graph_data.edge_data rhs_pvar
      )
      | _ -> pvar_rexp
      in

      let is_plus_minus_op op = match op with
      | Binop.PlusA _ | Binop.MinusA _ -> true | _ -> false
      in

      let graph_data = match pvar_rexp with 
      | EdgeExp.BinOp (op, EdgeExp.Var pvar, EdgeExp.Const (Const.Cint _)) when Pvar.equal assigned_pvar pvar -> (
        let assigned_exp = EdgeExp.Var assigned_pvar in
        if is_plus_minus_op op && EdgeExp.Set.mem assigned_exp graph_data.potential_norms then (
          { graph_data with
            potential_norms = EdgeExp.Set.remove assigned_exp graph_data.potential_norms;
            norms = EdgeExp.Set.add assigned_exp graph_data.norms;
          }
        ) else (
          graph_data
        )
      )
      | _ -> graph_data
      in

      let edge_data = DCP.EdgeData.add_assignment graph_data.edge_data assigned_pvar pvar_rexp in
      let initial_norms = if Pvar.is_return assigned_pvar then (
        edge_data.exit_edge <- true;
        EdgeExp.Set.add (EdgeExp.Var assigned_pvar) graph_data.norms
      ) else graph_data.norms
      in

      let loop_modified = if not (List.is_empty graph_data.loop_heads) then (
        PvarSet.add assigned_pvar graph_data.loop_modified
      ) else graph_data.loop_modified 
      in

      { graph_data with
        edge_data = edge_data;
        norms = initial_norms;
        loop_modified = loop_modified;
      }

    )
    | Sil.Load {id; e; typ; loc;} -> (
      log "[LOAD] (%a) | %a = %a\n" Location.pp loc Ident.pp id Exp.pp e;
      let rec map_ident exp = match exp with
      | Exp.Lfield (field_exp, name, typ) -> map_ident field_exp
      | Exp.Lvar pvar -> (
        let map1 = Ident.Map.add id (EdgeExp.Var pvar) graph_data.ident_map in
        let map2 = Ident.Map.add id (pvar, typ) graph_data.ident_map2 in
        map1, map2
      )
      | Exp.Var id -> (
        let pvar, typ = Ident.Map.find id graph_data.ident_map2 in
        let pvar_exp = Ident.Map.find id graph_data.ident_map in
        let map1 = Ident.Map.add id pvar_exp graph_data.ident_map in
        let map2 = Ident.Map.add id (pvar, typ) graph_data.ident_map2 in
        map1, map2
      )
      | _ -> L.(die InternalError)"Unsupported LOAD lhs-expression type!"
      in

      let map1, map2 = map_ident e in

      { graph_data with ident_map = map1; ident_map2 = map2; }
    )
    | Call ((ret_id, ret_type), Exp.Const (Const.Cfun callee_pname), args, loc, _) -> (
      log "[CALL] (%a) | %a\n" Location.pp loc Procname.pp callee_pname;
      match Payload.read ~caller_summary:graph_data.summary ~callee_pname:callee_pname with
      | Some new_summary -> (
        (* Replace all idents in call arguments with pvars and return these pvars as norms *)
        let args, arg_norms = List.fold args ~init:([], EdgeExp.Set.empty) ~f:(fun (args, norms) (arg, typ) ->
          let arg = EdgeExp.replace_idents arg graph_data.ident_map in
          let arg_norms = EdgeExp.get_exp_vars arg in
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
        let call = EdgeExp.Call (ret_type, callee_pname, args, new_summary) in
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
        (* L.(die InternalError)"Missing summary!" *)
        (* TODO: figure out how to do this, maybe models? Builtins cause problems *)
        log "Ret_id: %a\n" Ident.pp ret_id;
        let ret_pvar = Pvar.mk_abduced_ret callee_pname loc in
        { graph_data with 
          ident_map = Ident.Map.add ret_id (EdgeExp.Var ret_pvar) graph_data.ident_map;
          ident_map2 = Ident.Map.add ret_id (ret_pvar, ret_type) graph_data.ident_map2;
        }
      )
    )
    | Metadata metadata -> (match metadata with
      | VariableLifetimeBegins (pvar, typ, loc) -> (
        let scope_locals = match graph_data.scope_locals with
        | scope::tail -> [PvarSet.add pvar scope] @ tail
        | [] -> []
        in
        { graph_data with 
          locals = PvarSet.add pvar graph_data.locals;
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
  let exec_node proc_data node graph_data =
    let rev_instrs = IContainer.to_rev_list ~fold:Instrs.fold (Procdesc.Node.get_instrs node) in
    List.fold (List.rev rev_instrs) ~init:graph_data ~f:(fun graph_data instr -> 
      TransferFunctions.exec_instr proc_data node graph_data instr
    )

  let rec traverseCFG : Procdesc.t -> Procdesc.Node.t -> Procdesc.NodeSet.t -> GraphData.t -> (Procdesc.NodeSet.t * GraphData.t) = 
  fun proc_desc node visited graph_data -> (
    let open Domain in

    let is_loop_head = Procdesc.is_loop_head proc_desc node in
    if Procdesc.NodeSet.mem node visited 
    then (
      (* log "Visited Node %a : %s\n" Procdesc.Node.pp node (pp_nodekind (Procdesc.Node.get_kind node)); *)
      let preds = Procdesc.Node.get_preds node in
      let graph_data = if is_join_node node || List.length preds > 1 then (
        let edge_data = DCP.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
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
        let edge_data = DCP.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
        let new_edge = DCP.E.create graph_data.last_node edge_data join_node in
        (* log "Locals: %a\n" PvarSet.pp graph_data.locals;
        log "Scope locals:\n"; List.iter graph_data.scope_locals ~f:(fun scope -> log "  %a\n" PvarSet.pp scope; ); *)
        { graph_data with 
          nodes = DCP.NodeSet.add join_node graph_data.nodes;
          edges = DCP.EdgeSet.add new_edge graph_data.edges;
          last_node = join_node;
          edge_data = DCP.EdgeData.empty;

          locals = PvarSet.diff graph_data.locals (List.hd_exn graph_data.scope_locals);
          scope_locals = List.tl_exn graph_data.scope_locals;
          node_map = Procdesc.NodeMap.add node join_node graph_data.node_map
        }
      ) else graph_data
      in


      (* Execute node instructions *)
      let graph_data = exec_node proc_desc node graph_data in

      let successors = Procdesc.Node.get_succs node in
      let graph_data = if List.length successors > 1 then (
        (* Split node, create new DCP prune node *)
        let pred_node = List.hd_exn preds in
        let branch_node = List.hd_exn successors in
        let loc = Procdesc.Node.get_loc branch_node in
        let if_kind = match Procdesc.Node.get_kind branch_node with
        | Procdesc.Node.Prune_node (_, kind, _) -> kind
        | _ -> assert(false)
        in
        let prune_node = DCP.Node.Prune (if_kind, loc) in
        let edge_data = DCP.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
        let new_edge = DCP.E.create graph_data.last_node edge_data prune_node in
        { graph_data with 
          nodes = DCP.NodeSet.add prune_node graph_data.nodes;
          edges = DCP.EdgeSet.add new_edge graph_data.edges;
          last_node = prune_node;
          edge_data = DCP.EdgeData.empty;

          node_map = if Procdesc.is_loop_head proc_desc pred_node
          then Procdesc.NodeMap.add pred_node prune_node graph_data.node_map 
          else graph_data.node_map
        }
      ) 
      else graph_data
      in

      if is_exit_node node then (
        let exit_node = DCP.Node.Exit in
        let edge_data = DCP.EdgeData.add_invariants graph_data.edge_data graph_data.locals in
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


  let create_lts : Procdesc.t -> Summary.t -> GraphData.t = 
  fun proc_desc summary -> (
    let begin_loc = Procdesc.get_loc proc_desc in
    let start_node = Procdesc.get_start_node proc_desc in
    let dcp_start_node = Domain.DCP.Node.Start begin_loc in
    let graph_data = GraphData.make proc_desc summary dcp_start_node in
    snd (traverseCFG proc_desc start_node Procdesc.NodeSet.empty graph_data)
  )
end
