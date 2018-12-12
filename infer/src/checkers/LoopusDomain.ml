open! IStd
module F = Format
module L = Logging

(* module PvarSet = Caml.Set.Make(Pvar) *)
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


module LTSLocation = struct
  type t = 
    | PruneLoc of Location.t 
    | Start of Location.t
    | Join of int
    | Exit
    | Dummy
  [@@deriving compare]

  let is_join_loc : t -> bool = fun loc -> 
    match loc with
    | Join _ -> true
    | _ -> false

  let pp fmt loc = match loc with
    | PruneLoc loc | Start loc -> Location.pp fmt loc
    | Join id -> F.fprintf fmt "JOIN %d" id
    | Exit -> F.fprintf fmt "EXIT"
    | Dummy -> F.fprintf fmt "DUMMY"

  let equal = [%compare.equal: t]
end


module GraphEdge = struct
  type t = string 
  [@@deriving compare]
  let equal = String.equal
  let default = ""
  let empty = ""
end


module GraphNode = struct
  type t = {
    id: int;
    location: LTSLocation.t;
    label: string;
  } [@@deriving compare]

  module IdMap = Caml.Map.Make(LTSLocation)

  let is_join_node : t -> bool = fun node -> LTSLocation.is_join_loc node.location

  let idCnt = ref 0
  let idMap : (int IdMap.t) ref = ref IdMap.empty

  let hash = Hashtbl.hash
  let equal : t -> t -> bool = fun a b -> 
    (String.equal a.label b.label) && 
    (LTSLocation.equal a.location b.location) && 
    (Int.equal a.id b.id)

  let make : LTSLocation.t -> string -> t = fun loc label -> (
    let found = IdMap.mem loc !idMap in
    let node_id = if found then (
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
      label = label;
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

  let edge_attributes (a, e, b) = [`Label e; `Color 4711]
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let vertex_attributes (vertex: GraphNode.t) = [`Shape `Box; `Label vertex.label]

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

  let add_modified : t -> Pvar.t -> t = fun edge pvar -> {
    edge with modified_vars = (PvarSet.add pvar edge.modified_vars)
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

module NodeSet = Caml.Set.Make(GraphNode)
module GEdgeSet = Caml.Set.Make(LTS.E)


module AggregateJoin = struct
  type t = {
    rhs: LTSLocation.t;
    lhs: LTSLocation.t;
    edges: GEdgeSet.t;
  } [@@deriving compare]

  let initial : t = {
    lhs = LTSLocation.Dummy;
    rhs = LTSLocation.Dummy;
    edges = GEdgeSet.empty;
  }

  let add_edge : t -> LTS.E.t -> t = fun info edge -> 
    { info with edges = GEdgeSet.add edge info.edges } 

  let make : LTSLocation.t -> LTSLocation.t -> t = fun rhs lhs ->
    { lhs = lhs; rhs = rhs; edges = GEdgeSet.empty; }
end

type pathItem = (Sil.if_kind * bool * Location.t)

type astate = {
  lastNode: GraphNode.t;
  branchingPath: pathItem list;
  branchLocs: LocSet.t;
  lastLoc: LTSLocation.t;
  edges: EdgeSet.t;
  current_edge: Edge.t;
  branch: bool;
  pvars: PvarSet.t;
  joinLocs: int JoinLocations.t;
  pruneLocs: GraphNode.t PruneLocations.t;

  graphNodes: NodeSet.t;
  graphEdges: GEdgeSet.t;
  aggregateJoin: AggregateJoin.t;
}

let initial : LTSLocation.t -> astate = fun beginLoc -> (
  let entryPoint = GraphNode.make beginLoc "Begin" in
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

    graphNodes = NodeSet.add entryPoint NodeSet.empty;
    graphEdges = GEdgeSet.empty;
    aggregateJoin = AggregateJoin.initial;
  }
)

let pp_path fmt path =
  List.iter path ~f:(fun (kind, branch, _) ->
    let kind = Sil.if_kind_to_string kind in
    F.fprintf fmt "-> %s(%B) " kind branch
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
  (* L.stdout "  [LHS]\n";
  EdgeSet.iter (fun edge -> 
    L.stdout "    %a\n" Edge.pp edge
  ) lhs.edges;
  L.stdout "  [RHS]\n";
  EdgeSet.iter (fun edge -> 
    L.stdout "    %a\n" Edge.pp edge
  ) rhs.edges; *)
  EdgeSet.equal lhs.edges rhs.edges || (EdgeSet.cardinal lhs.edges < EdgeSet.cardinal rhs.edges)


let join_cnt = ref 0

let join : astate -> astate -> astate = fun lhs rhs ->
  L.stdout "\n[JOIN] %a | %a\n" LTSLocation.pp lhs.lastNode.location LTSLocation.pp rhs.lastNode.location;
  (* L.stdout "  [LHS]\n";
  L.stdout "    Path %a\n" pp_path lhs.branchingPath;
  L.stdout "    Edges:\n";
  EdgeSet.iter (fun edge -> 
    L.stdout "      %a\n" Edge.pp edge
  ) lhs.edges;

  L.stdout "  [RHS]\n";
  L.stdout "    Path %a\n" pp_path rhs.branchingPath;
  L.stdout "    Edges:\n";
  EdgeSet.iter (fun edge -> 
    L.stdout "      %a\n" Edge.pp edge
  ) rhs.edges; *)

  let lhsPath = path_to_string lhs.branchingPath in
  let rhsPath = path_to_string rhs.branchingPath in

  let rec aux : pathItem list -> pathItem list -> pathItem list -> pathItem list = fun acc a b ->
    match (a, b) with
    | x :: xs, y :: ys when phys_equal x y ->
        aux (x :: acc) xs ys
    | _, _ ->
        acc
  in
  let pathPrefix = List.rev (aux [] lhs.branchingPath rhs.branchingPath) in
  let lastLoc = match List.hd (List.rev pathPrefix) with 
  | Some (_, _, loc) -> LTSLocation.PruneLoc loc 
  | _ -> LTSLocation.Dummy
  in
  L.stdout "  Path prefix: %a\n" pp_path pathPrefix;

  let join_locs = JoinLocations.union (fun key a b -> 
    if not (phys_equal a b) then L.(die InternalError)"Join location is not unique!" else Some a
  ) lhs.joinLocs rhs.joinLocs 
  in
  let key = (lhs.current_edge.loc_begin, rhs.current_edge.loc_begin) in
  let join_id, join_locs = if JoinLocations.mem key join_locs then (
    JoinLocations.find key join_locs, join_locs
  ) else (
    join_cnt := !join_cnt + 1;
    !join_cnt, JoinLocations.add key !join_cnt join_locs
  )
  in

  let graph_nodes = NodeSet.union lhs.graphNodes rhs.graphNodes in
  let graph_edges = GEdgeSet.union lhs.graphEdges rhs.graphEdges in

  let join_location = LTSLocation.Join join_id in
  let is_consecutive_join = GraphNode.is_join_node lhs.lastNode || GraphNode.is_join_node rhs.lastNode in

  let join_node, aggregate_join = if is_consecutive_join then (
    let other_state, join_state = if GraphNode.is_join_node lhs.lastNode then rhs, lhs else lhs, rhs in
    let aggregate_join = match other_state.lastNode.location with
    | LTSLocation.Start _ -> (
      (* Don't add new edge if it's from the beginning location *)
      join_state.aggregateJoin
    )
    | _ -> (
      (* Add edge from non-join node to current set of edges pointing to aggregated join node *)
      let edge_vars = Edge.modified_to_string other_state.current_edge in
      let edge_label = F.sprintf "%s\n%s" (get_edge_label other_state.branchingPath) edge_vars in
      let edge = LTS.E.create other_state.lastNode edge_label join_state.lastNode in
      let aggregate_join = AggregateJoin.add_edge join_state.aggregateJoin edge in
      aggregate_join
    )
    in
    join_state.lastNode, aggregate_join
  ) else (
    (* First join in a row, create new join node and join info *)
    let node_label = F.sprintf "JOIN (%d)" join_id in
    let join_node = GraphNode.make join_location node_label in
    let lhs_modified = Edge.modified_to_string lhs.current_edge in
    let rhs_modified = Edge.modified_to_string rhs.current_edge in
    let lhs_edge_label = F.sprintf "%s\n%s" (get_edge_label lhs.branchingPath) lhs_modified in
    let rhs_edge_label = F.sprintf "%s\n%s" (get_edge_label rhs.branchingPath) rhs_modified in
    let lhs_edge = LTS.E.create lhs.lastNode lhs_edge_label join_node in
    let rhs_edge = LTS.E.create rhs.lastNode rhs_edge_label join_node in
    (* let graph_edges = GEdgeSet.add lhs_edge graph_edges in
    let graph_edges = GEdgeSet.add rhs_edge graph_edges in *)
    let aggregate_join =  AggregateJoin.make lhs.lastLoc rhs.lastLoc in
    let aggregate_join = AggregateJoin.add_edge aggregate_join lhs_edge in
    let aggregate_join = AggregateJoin.add_edge aggregate_join rhs_edge in
    join_node, aggregate_join
  )
  in

  (* let graph_nodes = if NodeSet.mem join_node graph_nodes then (
    graph_nodes
  ) else (
    NodeSet.add join_node graph_nodes
  )
  in *)

  let lhsEdge = Edge.set_end lhs.current_edge join_location in
  let rhsEdge = Edge.set_end rhs.current_edge join_location in
  let edgeSet = EdgeSet.union lhs.edges rhs.edges in
  let edgeSet = EdgeSet.add lhsEdge edgeSet in
  let edgeSet = EdgeSet.add rhsEdge edgeSet in
  { 
    branchingPath = pathPrefix;
    branchLocs = LocSet.union lhs.branchLocs rhs.branchLocs;
    lastLoc = lastLoc;
    edges = edgeSet;
    current_edge = Edge.initial (LTSLocation.Join join_id);
    branch = lhs.branch || rhs.branch;
    pvars = PvarSet.union lhs.pvars rhs.pvars;

    joinLocs = join_locs;
    pruneLocs = lhs.pruneLocs;

    lastNode = join_node;
    graphNodes = NodeSet.add join_node graph_nodes;
    graphEdges = graph_edges;
    aggregateJoin = aggregate_join;
  }

let widen ~prev ~next ~num_iters:_ = 
  (* L.stdout "\n[WIDEN]\n";
  L.stdout "  [PREV]\n";
  EdgeSet.iter (fun edge -> 
    L.stdout "    %a\n" Edge.pp edge
  ) prev.edges;
  L.stdout "  [NEXT]\n";
  EdgeSet.iter (fun edge -> 
    L.stdout "    %a\n" Edge.pp edge
  ) next.edges; *)
  (* join prev next *)
  {next with edges = EdgeSet.union prev.edges next.edges;}

let pp fmt astate =
  (* PvarSet.iter (Pvar.pp_value fmt) astate.pvars *)
  EdgeSet.iter (fun edge -> 
    F.fprintf fmt "%a\n" Edge.pp edge
  ) astate.edges

let pp_summary : F.formatter -> astate -> unit =
  fun fmt _astate ->
    F.fprintf fmt "loopus summary placeholder\n";
