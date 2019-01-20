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


module Formula = struct
  type operator = 
    | Binop of Binop.t
    | Assignment
  [@@deriving compare]

  type t = (Exp.t * operator * Exp.t)
  [@@deriving compare]

  let operator_text = function
  | Binop op -> Binop.str Pp.text op
  | Assignment -> "="

  let to_string (lexp, op, rexp) =
    let rec exp_to_str exp = match exp with
    | Exp.BinOp (op, lexp, rexp) -> (
      let lexp = exp_to_str lexp in
      let rexp = exp_to_str rexp in
      let op = Binop.str Pp.text op in
      F.sprintf "(%s %s %s)" lexp op rexp
    )
    | Exp.Lvar _ -> String.slice (Exp.to_string exp) 1 0
    | _ -> Exp.to_string exp
    in
    let lexp_str = exp_to_str lexp in
    let rexp_str = exp_to_str rexp in
    F.asprintf "%s %s %s" lexp_str (operator_text op) rexp_str
    

  let pp fmt formula = 
    F.fprintf fmt "%s" (to_string formula)
end

module FormulaSet = Caml.Set.Make(Formula)


type prune_info = (Sil.if_kind * bool * Location.t)
[@@deriving compare]

let pp_prune_info fmt (kind, branch, _) = 
  let kind = Sil.if_kind_to_string kind in
  F.fprintf fmt "%s(%B)" kind branch


module LTSLocation = struct
  type t = 
    | PruneLoc of (Sil.if_kind * Location.t)
    | Start of Location.t
    | Join of IntSet.t
    | Exit
    | Dummy
  [@@deriving compare]

  let add_join_id : t -> int -> t = fun loc id -> (
    match loc with
    | Join id_set -> Join (IntSet.add id id_set)
    | _ -> loc
  )

  let is_join_loc : t -> bool = fun loc -> 
    match loc with
    | Join _ -> true
    | _ -> false

  let to_string loc = match loc with
    | PruneLoc (kind, loc) -> F.sprintf "%s [%s]" (Sil.if_kind_to_string kind) (Location.to_string loc)
    | Start loc -> F.sprintf "Begin [%s]" (Location.to_string loc)
    | Join id_set -> (
      let str = IntSet.fold (fun id acc ->
        acc ^ Int.to_string id ^ " + "
      ) id_set "Join ("
      in
      (String.slice str 0 (String.length str - 3)) ^ ")"
    )
    | Exit -> F.sprintf "Exit"
    | Dummy -> F.sprintf "Dummy"

  let pp fmt loc = F.fprintf fmt "%s" (to_string loc)

  let equal = [%compare.equal: t]
end

module GraphEdge = struct
  type t = {
    formulas: FormulaSet.t;

    (* Last element of common path prefix *)
    path_prefix_end: prune_info option; 
  }
  [@@deriving compare]
  let equal = [%compare.equal: t]
  let empty = { formulas = FormulaSet.empty; path_prefix_end = None; }
  let default = empty

  let make : FormulaSet.t -> prune_info option -> t = fun formulas prefix_end -> 
    { formulas = formulas; path_prefix_end = prefix_end; }

  let add_formula : t -> Formula.t -> t = fun edge formula -> (
    { edge with formulas = FormulaSet.add formula edge.formulas }
  )
  
end

module GraphNode = struct
  type t = {
    id: int;
    location: LTSLocation.t;
  } [@@deriving compare]

  module IdMap = Caml.Map.Make(LTSLocation)

  let is_join_node : t -> bool = fun node -> LTSLocation.is_join_loc node.location

  let idCnt = ref 0
  let idMap : (int IdMap.t) ref = ref IdMap.empty

  let hash = Hashtbl.hash
  let equal = [%compare.equal: t]

  let add_join_id : t -> int -> t = fun node id -> (
    { node with location = LTSLocation.add_join_id node.location id }
  )

  let make : LTSLocation.t -> t = fun loc -> (
    let found = IdMap.mem loc !idMap in
    let node_id = if found then (
      (* L.stdout "EQUAL: %a - %a" LTSLocation.pp *)
      IdMap.find loc !idMap
    ) else (
      idCnt := !idCnt + 1;
      idMap := IdMap.add loc !idCnt !idMap;
      !idCnt
    ) 
    in
    {
      id = node_id;
      location = loc;
    }
  )
end

module JoinLocations = Caml.Map.Make(struct
  type t = (LTSLocation.t * LTSLocation.t)
  [@@deriving compare]
end)


module PruneLocations = Caml.Map.Make(LTSLocation)


(* Labeled Transition System *)
module LTS = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(GraphNode)(GraphEdge)
(* module LTS = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(GraphNode)(GraphEdge) *)

module DotConfig = struct
  include LTS

  let edge_attributes : LTS.E.t -> 'a list = fun (_src, edge, _dst) -> (
    let label = match edge.path_prefix_end with
    | Some prune_info -> F.asprintf "%a\n" pp_prune_info prune_info
    | None -> "\n"
    in
    let label = FormulaSet.fold (fun exp acc -> 
      acc ^ (Formula.to_string exp) ^ "\n"
    ) edge.formulas label
    in
    (* let len = String.length label in
    let label = if not (FormulaSet.is_empty edge.formulas) then (
      String.slice label 0 (len - 3)
    ) else label 
    in *)
    [`Label label; `Color 4711]
  )
  
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let vertex_attributes : GraphNode.t -> 'a list = fun node -> (
    (* let label = match node.location with
    | LTSLocation.Start loc -> F.sprintf "%s\n%s" node.label (Location.to_string loc)
    | _ -> node.label
    in *)
    [ `Shape `Box; `Label (LTSLocation.to_string node.location) ]
  )

  let vertex_name : GraphNode.t -> string = fun vertex -> (
    string_of_int vertex.id
  )
    
  let default_vertex_attributes _ = []
  let graph_attributes _ = []
end

module Dot = Graph.Graphviz.Dot(DotConfig)

module Edge = struct
  type t = {
    loc_begin: LTSLocation.t;
    loc_end: LTSLocation.t;
    is_backedge: bool;
    modified_vars: PvarSet.t
  } [@@deriving compare]

  let empty = {
    loc_begin = Dummy;
    loc_end = Dummy;
    is_backedge = false;
    modified_vars = PvarSet.empty;
  }

  let initial : LTSLocation.t -> t = fun loc_begin -> {
    loc_begin = loc_begin;
    loc_end = Dummy;
    is_backedge = false;
    modified_vars = PvarSet.empty;
  }

  let add_modified : t -> Pvar.t Sequence.t -> t = fun edge modified -> (
    let newPvars = PvarSet.of_list (Sequence.to_list modified) in
    {edge with modified_vars = PvarSet.union newPvars edge.modified_vars}
  )

  let set_end : t -> LTSLocation.t -> t = fun edge loc -> { edge with loc_end = loc; }

  let set_backedge : t -> t = fun edge -> { edge with is_backedge = true; }

  let pp fmt edge =
    F.fprintf fmt "(%a) -->  (%a) [%a]" 
    LTSLocation.pp edge.loc_begin 
    LTSLocation.pp edge.loc_end 
    PvarSet.pp edge.modified_vars

  let modified_to_string edge = PvarSet.to_string edge.modified_vars
    
end

module EdgeSet = Caml.Set.Make(Edge)

module LTSNodeSet = Caml.Set.Make(LTS.V)
module LTSEdgeSet = Caml.Set.Make(LTS.E)


module AggregateJoin = struct
  type t = {
    join_nodes: IntSet.t;
    rhs: LTSLocation.t;
    lhs: LTSLocation.t;
    edges: LTSEdgeSet.t;
  } [@@deriving compare]

  let initial : t = {
    join_nodes = IntSet.empty;
    lhs = LTSLocation.Dummy;
    rhs = LTSLocation.Dummy;
    edges = LTSEdgeSet.empty;
  }

  let add_node_id : t -> int -> t = fun aggregate join_id ->
    { aggregate with join_nodes = IntSet.add join_id aggregate.join_nodes }

  let add_edge : t -> LTS.E.t -> t = fun info edge -> 
    { info with edges = LTSEdgeSet.add edge info.edges } 

  let make : int -> LTSLocation.t -> LTSLocation.t -> t = fun join_id rhs lhs ->
    { join_nodes = IntSet.add join_id IntSet.empty; lhs = lhs; rhs = rhs; edges = LTSEdgeSet.empty; }
end


type astate = {
  lastNode: GraphNode.t;
  branchingPath: prune_info list;
  branchLocs: LocSet.t;
  lastLoc: LTSLocation.t;
  edges: EdgeSet.t;
  current_edge: Edge.t;
  branch: bool;
  pvars: PvarSet.t;
  joinLocs: int JoinLocations.t;
  pruneLocs: GraphNode.t PruneLocations.t;

  locals: PvarSet.t;
  ident_map: Pvar.t Ident.Map.t;
  modified_pvars: PvarSet.t;
  edge_formulas: FormulaSet.t;
  graph_nodes: LTSNodeSet.t;
  graph_edges: LTSEdgeSet.t;
  aggregate_join: AggregateJoin.t;
}

let initial : LTSLocation.t -> PvarSet.t -> astate = fun beginLoc locals -> (
  let entryPoint = GraphNode.make beginLoc in
  {
    lastNode = entryPoint;
    branchingPath = [];
    branchLocs = LocSet.empty;
    lastLoc = beginLoc;
    edges = EdgeSet.empty;
    current_edge = Edge.initial beginLoc;
    branch = false;
    pvars = PvarSet.empty;
    joinLocs = JoinLocations.empty;
    pruneLocs = PruneLocations.empty;

    locals = locals;
    ident_map = Ident.Map.empty;
    modified_pvars = PvarSet.empty;
    edge_formulas = FormulaSet.empty;
    graph_nodes = LTSNodeSet.add entryPoint LTSNodeSet.empty;
    graph_edges = LTSEdgeSet.empty;
    aggregate_join = AggregateJoin.initial;
  }
)

let generate_missing_formulas astate =
  let unmodified_pvars = PvarSet.diff astate.locals astate.modified_pvars in
  PvarSet.fold (fun pvar acc ->
    let pvar_exp = Exp.Lvar pvar in
    let formula = (pvar_exp, Formula.Assignment, pvar_exp) in
    FormulaSet.add formula acc
  ) unmodified_pvars FormulaSet.empty

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
  (* L.stdout "[Partial order <= ]\n"; *)
  (* L.stdout "  [LHS]\n"; *)
  EdgeSet.equal lhs.edges rhs.edges || (EdgeSet.cardinal lhs.edges < EdgeSet.cardinal rhs.edges)


let join_cnt = ref 0


let join : astate -> astate -> astate = fun lhs rhs ->
  L.stdout "\n[JOIN] %a | %a\n" LTSLocation.pp lhs.lastNode.location LTSLocation.pp rhs.lastNode.location;

  (* Creates common path prefix of provided paths *)
  let rec common_path_prefix = fun (prefix, _) pathA pathB ->
    match (pathA, pathB) with
    | headA :: tailA, headB :: tailB when Int.equal (compare_prune_info headA headB) 0 -> 
      common_path_prefix (headA :: prefix, false) tailA tailB
    | _ :: _, [] | [], _ :: _ -> 
      (prefix, true)
    | _, _ ->
      (prefix, false)
  in

  let lhs_path = lhs.branchingPath in
  let rhs_path = rhs.branchingPath in
  let (path_prefix_rev, loop_left) = common_path_prefix ([], false) lhs.branchingPath rhs.branchingPath in

  (* Last element of common path prefix represents current nesting level *)
  let prefix_end = List.hd path_prefix_rev in
  let prefix_end_loc = match prefix_end with 
  | Some (kind, _, loc) -> LTSLocation.PruneLoc (kind, loc)
  | _ -> LTSLocation.Dummy
  in
  let path_prefix = List.rev path_prefix_rev in
  L.stdout "  [NEW] Path prefix: %a\n" pp_path path_prefix;

  let join_locs = JoinLocations.union (fun _key a b -> 
    if not (phys_equal a b) then L.(die InternalError)"Join location is not unique!" else Some a
  ) lhs.joinLocs rhs.joinLocs 
  in

  (* Check if join location already exist and create new with higher ID if it doesn't *)
  let key = (lhs.current_edge.loc_begin, rhs.current_edge.loc_begin) in
  let join_id, join_locs = if JoinLocations.mem key join_locs then (
    JoinLocations.find key join_locs, join_locs
  ) else (
    join_cnt := !join_cnt + 1;
    !join_cnt, JoinLocations.add key !join_cnt join_locs
  )
  in

  let graph_nodes = LTSNodeSet.union lhs.graph_nodes rhs.graph_nodes in
  let graph_edges = LTSEdgeSet.union lhs.graph_edges rhs.graph_edges in

  let join_location = LTSLocation.Join (IntSet.add join_id IntSet.empty) in
  let is_consecutive_join = GraphNode.is_join_node lhs.lastNode || GraphNode.is_join_node rhs.lastNode in

  let join_node, aggregate_join = if is_consecutive_join then (
    (* Consecutive join, merge join nodes and possibly add new edge to aggregated join node *)
    let other_state, join_state = if GraphNode.is_join_node lhs.lastNode then rhs, lhs else lhs, rhs in
    let aggregate_join = match other_state.lastNode.location with
    | LTSLocation.Start _ -> (
      (* Don't add new edge if it's from the beginning location *)
      join_state.aggregate_join
    )
    | _ -> (
      if loop_left then (
        (* Heuristic: ignore edge from previous location if this is a "backedge" join which 
         * joins state from inside of the loop with outside state denoted by prune location before loop prune *)
        join_state.aggregate_join
      ) else (
        (* Add edge from non-join node to current set of edges pointing to aggregated join node *)
        let formulas = FormulaSet.union other_state.edge_formulas (generate_missing_formulas other_state) in
        let edge_data = GraphEdge.make formulas (List.last other_state.branchingPath) in
        let lts_edge = LTS.E.create other_state.lastNode edge_data join_state.lastNode in
        let aggregate_join = AggregateJoin.add_edge join_state.aggregate_join lts_edge in
        aggregate_join
      )
    )
    in
    join_state.lastNode, AggregateJoin.add_node_id aggregate_join join_id
  ) else (
    (* First join in a row, create new join node and join info *)
    let join_node = GraphNode.make join_location in
    let lhs_formulas = FormulaSet.union lhs.edge_formulas (generate_missing_formulas lhs) in
    let rhs_formulas = FormulaSet.union rhs.edge_formulas (generate_missing_formulas rhs) in
    let lhs_edge_data = GraphEdge.make lhs_formulas (List.last lhs_path) in
    let rhs_edge_data = GraphEdge.make rhs_formulas (List.last rhs_path) in
    let lhs_lts_edge = LTS.E.create lhs.lastNode lhs_edge_data join_node in
    let rhs_lts_edge = LTS.E.create rhs.lastNode rhs_edge_data join_node in
    let aggregate_join =  AggregateJoin.make join_id lhs.lastLoc rhs.lastLoc in
    let aggregate_join = AggregateJoin.add_edge aggregate_join lhs_lts_edge in
    let aggregate_join = AggregateJoin.add_edge aggregate_join rhs_lts_edge in
    join_node, aggregate_join
  )
  in

  let lhsEdge = Edge.set_end lhs.current_edge join_location in
  let rhsEdge = Edge.set_end rhs.current_edge join_location in
  let edgeSet = EdgeSet.union lhs.edges rhs.edges in
  let edgeSet = EdgeSet.add lhsEdge edgeSet in
  let edgeSet = EdgeSet.add rhsEdge edgeSet in

  let ident_map = Ident.Map.union (fun _key a b ->
    if not (Pvar.equal a b) then 
      L.(die InternalError)"One SIL identificator maps to multiple Pvars!" 
    else 
      Some a
  ) lhs.ident_map rhs.ident_map 
  in
  { 
    branchingPath = path_prefix;
    branchLocs = LocSet.union lhs.branchLocs rhs.branchLocs;
    lastLoc = prefix_end_loc;
    edges = edgeSet;
    current_edge = Edge.initial join_location;
    branch = lhs.branch || rhs.branch;
    pvars = PvarSet.union lhs.pvars rhs.pvars;
    joinLocs = join_locs;
    pruneLocs = lhs.pruneLocs;

    locals = lhs.locals;
    modified_pvars = PvarSet.empty;
    ident_map = ident_map;
    edge_formulas = FormulaSet.empty;
    lastNode = join_node;
    graph_nodes = LTSNodeSet.add join_node graph_nodes;
    graph_edges = graph_edges;
    aggregate_join = aggregate_join;
  }

let widen ~prev ~next ~num_iters:_ = 
  (* L.stdout "\n[WIDEN]\n"; *)
  {next with edges = EdgeSet.union prev.edges next.edges;}

let pp fmt astate =
  (* PvarSet.iter (Pvar.pp_value fmt) astate.pvars *)
  EdgeSet.iter (fun edge -> 
    F.fprintf fmt "%a\n" Edge.pp edge
  ) astate.edges

let pp_summary : F.formatter -> astate -> unit =
  fun fmt _astate ->
    F.fprintf fmt "loopus summary placeholder\n";
