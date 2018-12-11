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

  let idCnt = ref 0
  let idMap : (int IdMap.t) ref = ref IdMap.empty

  let hash = Hashtbl.hash
  let equal : t -> t -> bool = fun a b -> 
    (String.equal a.label b.label) && 
    (LTSLocation.equal a.location b.location) && 
    (Int.equal a.id b.id)

  let make : LTSLocation.t -> string -> t = fun loc label -> (
    IdMap.iter (fun loc id -> 
      L.stdout "%a = %d\n" LTSLocation.pp loc id;
    ) !idMap;

    let found = IdMap.mem loc !idMap in
    L.stdout "%a: %B\n" LTSLocation.pp loc found;
    (* let found = IdMap.find_first_opt (fun existing_loc -> 
      let equal = LTSLocation.equal existing_loc loc in
      L.stdout "%a, %a, %B\n" LTSLocation.pp existing_loc LTSLocation.pp loc equal;
      equal
    ) !idMap 
    in
    let node_id = match found with
    | Some (_, id) -> id
    | None -> (
      idMap := IdMap.add loc !idCnt !idMap;
      idCnt := !idCnt + 1;
      !idCnt
    ) *)
    let node_id = if found then (
      let id = IdMap.find loc !idMap in
      L.stdout "Found id: %d\n" id;
      id
    ) else (
      idCnt := !idCnt + 1;
      idMap := IdMap.add loc !idCnt !idMap;
      !idCnt
    ) 
    in
    IdMap.iter (fun loc id -> 
      L.stdout "%a = %d\n" LTSLocation.pp loc id;
    ) !idMap;
    {
      id = node_id;
      location = loc;
      label = label;
    }
  )

  (* let get_last() = match !last_node with
    | Some node -> node
    | None -> { id = -1; location = Location.dummy; label = "invalid"; }

  let get_id() = !id_counter *)
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

type pathItem = (Sil.if_kind * bool * Location.t)

type astate = {
  (* mutable lts: LTS.t; *)
  lastNode: GraphNode.t;
  (* lastNodeRef: GraphNode.t ref; *)

  branchingPath: pathItem list;
  branchLocs: LocSet.t;
  lastLoc: LTSLocation.t;
  edges: EdgeSet.t;
  current_edge: Edge.t;
  branch: bool;
  pvars: PvarSet.t;
  afterJoin: bool;
  joinLocs: int JoinLocations.t;
  pruneLocs: GraphNode.t PruneLocations.t;

  graphNodes: NodeSet.t;
  graphEdges: GEdgeSet.t;
}

let initial : LTSLocation.t -> astate = fun beginLoc -> (
  (* let graph = LTS.create() in *)
  let entryPoint = GraphNode.make beginLoc "Begin" in
  let astate = {
    (* lts = graph; *)
    lastNode = entryPoint;
    (* lastNodeRef = ref entryPoint; *)

    branchingPath = [];
    branchLocs = LocSet.empty;
    lastLoc = beginLoc;
    edges = EdgeSet.empty;
    current_edge = Edge.initial beginLoc;
    branch = false;
    pvars = PvarSet.empty;
    afterJoin = false;
    joinLocs = JoinLocations.empty;
    pruneLocs = PruneLocations.empty;

    graphNodes = NodeSet.add entryPoint NodeSet.empty;
    graphEdges = GEdgeSet.empty;
  }
  in
  (* LTS.add_vertex graph entryPoint; *)
  astate
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
  | None -> "unknown"

(* let find_edge : EdgeSet.t -> Edge.t -> Edge.t = fun set edge -> (
    let loc_cmp loc_a loc_b = match loc_a, loc_b with
      | LTSLocation.Join _, LTSLocation.Join _ -> true
      | _, _ -> Int.equal (LTSLocation.compare loc_a loc_b) 0
    in
    let found = EdgeSet.find_first_opt (fun existing_edge -> 
      (PvarSet.equal existing_edge.modified_vars edge.modified_vars) &&
      (loc_cmp existing_edge.loc_begin edge.loc_begin) && 
      (loc_cmp existing_edge.loc_end edge.loc_end) &&
      (phys_equal existing_edge.is_backedge edge.is_backedge)
    ) set
    in
    match found with
    | Some found -> L.stdout "FOUND EXISTING EDGE"; found
    | None -> edge
  ) *)

let ( <= ) ~lhs ~rhs =
  L.stdout "[Partial order <= ]\n";
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
  L.stdout "\n[JOIN]\n";
  L.stdout "  [LHS]\n";
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
  ) rhs.edges;

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
  L.stdout "  [NEW]\n";
  L.stdout "    Path %a\n" pp_path pathPrefix;

  (* let state = if (List.length lhs.branchingPath) > (List.length rhs.branchingPath) 
  then lhs else rhs in

  let backedge = if (List.length state.branchingPath) > 0 then (
    match List.last_exn state.branchingPath with
    | Sil.Ik_while, true, _ -> true
    | _ -> false 
  ) else false
  in

  let astate = if backedge then (
    let modified = Edge.modified_to_string state.current_edge in
    let backedge = LTS.E.create state.lastNode ("Backedge\n" ^ modified) state.lastNode in
    LTS.add_edge_e state.lts backedge;
    rhs
  )
  else (
    let nodeLabel = "JOIN\n" ^ lhsPath ^ "\n" ^ rhsPath in
    let newNode = GraphNode.make Location.dummy nodeLabel in
    let lhs_modified = Edge.modified_to_string lhs.current_edge in
    let rhs_modified = Edge.modified_to_string rhs.current_edge in
    let lhs_edge_label = F.sprintf "%s\n%s" (get_edge_label lhs.branchingPath) lhs_modified in
    let rhs_edge_label = F.sprintf "%s\n%s" (get_edge_label rhs.branchingPath) rhs_modified in
    let lhs_edge = LTS.E.create lhs.lastNode lhs_edge_label newNode in
    let rhs_edge = LTS.E.create rhs.lastNode rhs_edge_label newNode in
    LTS.add_vertex rhs.lts newNode;
    LTS.add_edge_e rhs.lts lhs_edge;
    LTS.add_edge_e rhs.lts rhs_edge;
    {rhs with lastNode = newNode; lastNodeRef = ref newNode; }
  ) 
  in *)
  (* let filename = F.sprintf "%s.dot" (string_of_int newNode.id) in
  let file = Out_channel.create filename in
  let () = Dot.output_graph file rhs.lts in
  Out_channel.close file; *)
  (* let prune_locs = PruneLocations.union (fun key (a : GraphNode.t) (b : GraphNode.t) ->
    if not (GraphNode.equal a b) then (
      L.stdout "%a, %d, %s\n" LTSLocation.pp a.location a.id a.label;
      L.stdout "%a, %d, %s\n" LTSLocation.pp b.location b.id b.label;
      L.(die InternalError)"Prune location is not unique!"
    ) else Some a
  ) lhs.pruneLocs rhs.pruneLocs
  in *)
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
  let location = LTSLocation.Join join_id in


  let label = F.sprintf "JOIN (%d)" join_id in
  let join_node = GraphNode.make location label in
  let lhs_modified = Edge.modified_to_string lhs.current_edge in
  let rhs_modified = Edge.modified_to_string rhs.current_edge in
  let lhs_edge_label = F.sprintf "%s\n%s" (get_edge_label lhs.branchingPath) lhs_modified in
  let rhs_edge_label = F.sprintf "%s\n%s" (get_edge_label rhs.branchingPath) rhs_modified in
  let lhs_edge = LTS.E.create lhs.lastNode lhs_edge_label join_node in
  let rhs_edge = LTS.E.create rhs.lastNode rhs_edge_label join_node in
  let graph_edges = GEdgeSet.union lhs.graphEdges rhs.graphEdges in
  let graph_edges = GEdgeSet.add lhs_edge graph_edges in
  let graph_edges = GEdgeSet.add rhs_edge graph_edges in

  let lhsEdge = Edge.set_end lhs.current_edge location in
  let rhsEdge = Edge.set_end rhs.current_edge location in
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
    (* TODO: try to find a better way *)
    afterJoin = true;

    lastNode = join_node;
    graphNodes = NodeSet.add join_node (NodeSet.union lhs.graphNodes rhs.graphNodes);
    graphEdges = graph_edges;
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
