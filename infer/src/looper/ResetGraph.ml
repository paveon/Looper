(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
open LooperUtils
module F = Format
module LTS = LabeledTransitionSystem
module DC = DifferenceConstraint
module DCP = DifferenceConstraintProgram

(* Reset graph *)
module Node = struct
  type t = EdgeExp.T.t * bool [@@deriving equal, compare]

  let hash x = Hashtbl.hash_param 100 100 x

  let equal = equal
end

module Edge = struct
  type t = {dcp_edge: DCP.E.t option; const_part: DC.rhs_const} [@@deriving compare]

  let hash = Hashtbl.hash

  let equal = [%compare.equal: t]

  let default = {dcp_edge= None; const_part= (Binop.PlusA None, IntLit.zero)}

  let dcp_edge edge = match edge.dcp_edge with Some dcp_edge -> dcp_edge | None -> assert false

  let make dcp_edge const = {dcp_edge= Some dcp_edge; const_part= const}
end

include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Node) (Edge)

type graph = t

let edge_attributes : E.t -> 'a list =
 fun (_, edge, _) ->
  let label =
    match edge.dcp_edge with
    | Some (src, _, dst) ->
        F.asprintf "%a -- %a\n%a" LTS.Node.pp src LTS.Node.pp dst DC.pp_const_part edge.const_part
    | None ->
        ""
  in
  [`Label label; `Color 4711]


let default_edge_attributes _ = []

let get_subgraph _ = None

let vertex_attributes : V.t -> 'a list =
 fun (norm, formal) ->
  let color : int = if formal then 0xFF0000 else 0x00FF00 in
  [`Shape `Box; `Label (EdgeExp.to_string norm); `Fillcolor color; `Style `Filled]


let vertex_name : V.t -> string = fun node -> string_of_int (Node.hash node)

let default_vertex_attributes _ = []

let graph_attributes _ = []

module Chain = struct
  type t = {data: E.t list; mutable norms: (EdgeExp.Set.t * EdgeExp.Set.t) option}
  [@@deriving compare]

  let empty = {data= []; norms= None}

  let origin chain = E.src (List.hd_exn chain.data)

  let value chain =
    List.fold chain.data
      ~f:(fun acc (_, (data : Edge.t), _) ->
        let op, const = data.const_part in
        match op with
        | Binop.PlusA _ ->
            IntLit.add acc const
        | _ ->
            (* TODO: currently unsound due to ignored shifts and other operators *)
            acc )
      ~init:IntLit.zero


  let transitions chain =
    List.fold chain.data ~init:DCP.EdgeSet.empty ~f:(fun acc (_, edge_data, _) ->
        DCP.EdgeSet.add (Edge.dcp_edge edge_data) acc )


  let norms chain reset_graph =
    match chain.norms with
    | Some cache ->
        cache
    | None ->
        let _, _, path_end = List.last_exn chain.data in
        let rec find_paths origin visited counter =
          if Node.equal origin path_end then counter + 1
          else
            let next = succ_e reset_graph origin in
            if List.is_empty next then counter
            else
              let visited = EdgeExp.Set.add (fst origin) visited in
              List.fold next ~init:counter ~f:(fun counter (_, _, dst) ->
                  let dst_norm = fst dst in
                  if EdgeExp.Set.mem dst_norm visited then counter
                  else find_paths dst visited counter )
        in
        let norms =
          List.fold chain.data
            ~f:(fun (norms_1, norms_2) (_, _, (dst : Node.t)) ->
              let path_count = find_paths dst EdgeExp.Set.empty 0 in
              let dst_norm = fst dst in
              if path_count < 2 then (EdgeExp.Set.add dst_norm norms_1, norms_2)
              else (norms_1, EdgeExp.Set.add dst_norm norms_2) )
            ~init:(EdgeExp.Set.empty, EdgeExp.Set.empty)
        in
        chain.norms <- Some norms ;
        norms


  let pp fmt chain =
    List.iter chain.data ~f:(fun ((src : Node.t), _, _) ->
        F.fprintf fmt "%a --> " EdgeExp.pp (fst src) ) ;
    let _, _, (dst : Node.t) = List.last_exn chain.data in
    F.fprintf fmt "%a" EdgeExp.pp (fst dst)


  module Set = Caml.Set.Make (struct
    type nonrec t = t

    let compare = compare
  end)
end

(* Finds all reset chains leading to the norm through reset graph *)
let get_reset_chains origin reset_graph dcp =
  let open Base.Continue_or_stop in
  let rec traverse_reset_graph node (chain : Chain.t) =
    let preds = pred_e reset_graph node in
    if List.is_empty preds then Chain.Set.singleton chain
    else
      List.fold preds ~init:Chain.Set.empty ~f:(fun chains (src, edge_data, dst) ->
          let current_chain = {chain with data= chain.data @ [(src, edge_data, dst)]} in
          let new_chains = traverse_reset_graph src current_chain in
          Chain.Set.union chains new_chains )
  in
  let reset_chains = traverse_reset_graph origin Chain.empty in
  Chain.Set.iter (fun chain -> debug_log "[Chain] %a@," Chain.pp chain) reset_chains ;
  (* Shorten the chain until it's optimal, i.e., maximal while remaining sound *)
  Chain.Set.map
    (fun chain ->
      let src, edge_data, dst = List.hd_exn chain.data in
      let path_origin =
        match edge_data.dcp_edge with Some (_, _, dcp_dst) -> dcp_dst | None -> assert false
      in
      let optimize_chain optimal_chain (src, (edge_data : Edge.t), dst) =
        match edge_data.dcp_edge with
        | Some (_, _, path_end) -> (
            (* Find all paths from origin to end and check if they reset the end norm *)
            let current_norm = fst dst in
            let rec checkPaths origin current visited_nodes norm_reset =
              if LTS.Node.equal current path_end && not (LTS.NodeSet.is_empty visited_nodes) then
                (* Found path, return info if norm was reset along the path *)
                match norm_reset with Some _ -> norm_reset | None -> Some false
              else
                let next = DCP.succ_e dcp current in
                if List.is_empty next then (* Not a path *)
                  None
                else
                  let visited_nodes =
                    if LTS.Node.equal origin current then visited_nodes
                    else LTS.NodeSet.add current visited_nodes
                  in
                  List.fold_until next ~init:norm_reset
                    ~f:(fun norm_reset (dcp_edge : DCP.E.t) ->
                      let dcp_src, dcp_data, dcp_dst = dcp_edge in
                      if LTS.NodeSet.mem dcp_dst visited_nodes || LTS.Node.equal dcp_src dcp_dst
                      then Continue norm_reset
                      else
                        let norm_reset =
                          match norm_reset with
                          | Some _ ->
                              norm_reset
                          | None ->
                              if DCP.EdgeData.is_reset dcp_data current_norm then Some true
                              else None
                        in
                        match checkPaths origin dcp_dst visited_nodes norm_reset with
                        | Some already_reset ->
                            if already_reset then Continue (Some true) else Stop None
                        | None ->
                            Continue norm_reset )
                    ~finish:(fun acc -> acc)
            in
            let all_paths_reset = checkPaths path_origin path_origin LTS.NodeSet.empty None in
            match all_paths_reset with
            | Some _ ->
                Continue ([(src, edge_data, dst)] @ optimal_chain)
            | None ->
                Stop optimal_chain )
        | None ->
            assert false
      in
      let chain_data =
        List.fold_until (List.tl_exn chain.data)
          ~init:[(src, edge_data, dst)]
          ~f:optimize_chain
          ~finish:(fun acc -> acc)
      in
      let chain = {chain with data= chain_data} in
      chain )
    reset_chains
