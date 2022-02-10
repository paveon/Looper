(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
open LooperUtils

module F = Format
module DC = DifferenceConstraint
module LTS = LabeledTransitionSystem


let debug_log : ('a, Format.formatter, unit) format -> 'a = 
  fun fmt -> F.fprintf (List.hd_exn !debug_fmt) fmt


(* Difference Constraint Program *)
type edge_output_type = | GuardedDCP | DCP [@@deriving compare]


module EdgeData = struct
  type t = {
    backedge: bool;
    branch_info: (Sil.if_kind * bool * Location.t) option;

    mutable calls: EdgeExp.CallPairSet.t;
    mutable constraints: DC.t list;
    mutable guards: EdgeExp.Set.t;
    mutable bound: EdgeExp.T.t option;
    mutable bound_norm: EdgeExp.T.t option;
    mutable computing_bound: bool;

    mutable edge_type: edge_output_type;
  }
  [@@deriving compare]

  let equal = [%compare.equal: t]

  let from_lts_edge (lts_edge_data : LTS.EdgeData.t) = {
    backedge = lts_edge_data.backedge;
    branch_info = lts_edge_data.branch_info;
    calls = lts_edge_data.calls;

    constraints = [];
    guards = EdgeExp.Set.empty;
    bound = None;
    bound_norm = None;
    computing_bound = false;

    edge_type = DCP
  }

  let get_dc key constraints =
    let constraint_opt = List.find constraints ~f:(fun (lhs, _) ->
      EdgeExp.equal key lhs
    )
    in
    match constraint_opt with
    | Some dc -> Some dc
    | None -> None

  let add_dc dc_lhs ((rhs_norm, _, rhs_const) as dc_rhs) constraints =
    if EdgeExp.equal dc_lhs rhs_norm && IntLit.iszero rhs_const then (
      (* Check if set already contains some constraint with this left hand side *)
      match get_dc dc_lhs constraints with
      | Some _  -> (
        (* Do not replace [e <= expr] *)
        constraints
      ) 
      | None -> constraints @ [(dc_lhs, dc_rhs)]
    ) 
    else (
      (* Replace constant dc [e <= e] with [e <= expr] *)
      constraints @ [(dc_lhs, dc_rhs)]
    )

  let is_reset edge norm = match get_dc norm edge.constraints with
    | Some dc -> not (DC.same_norms dc)
    | None -> false

  let get_reset edge norm = match get_dc norm edge.constraints with
    | Some ((_, dc_rhs) as dc) when not (DC.same_norms dc) -> (
      match dc_rhs with
      | DC.Value (rhs_norm, op, lit) -> (
        Some (EdgeExp.Value (EdgeExp.merge rhs_norm (Some (op, lit))))
      )
      | DC.Pair ((lb_norm, lb_op, lb_lit), (ub_norm, ub_op, ub_lit)) -> (
        Some (EdgeExp.Pair (EdgeExp.merge lb_norm (Some (lb_op, lb_lit)),
              EdgeExp.merge ub_norm (Some (ub_op, ub_lit))))
      )
    )
    | _ -> None

  let is_backedge edge = edge.backedge

  let active_guards edge = EdgeExp.Set.fold (fun guard acc ->
    match get_dc guard edge.constraints with
    | Some dc -> (
      if DC.is_decreasing dc && DC.same_norms dc then acc
      else EdgeExp.Set.add guard acc
    )
    | _ -> EdgeExp.Set.add guard acc
  ) edge.guards EdgeExp.Set.empty

  (* Required by Graph module interface *)
  let default = {
    backedge = false;
    branch_info = None;
    edge_type = DCP;
    constraints = [];
    calls = EdgeExp.CallPairSet.empty;
    guards = EdgeExp.Set.empty;
    bound = None;
    bound_norm = None;
    computing_bound = false;
  }

  let set_edge_output_type edge output_type = edge.edge_type <- output_type

  let branch_type edge = match edge.branch_info with
    | Some (_, branch, _) -> branch
    | _ -> false

  let add_guards edge guards = edge.guards <- guards

  let add_constraint edge dc =
    (* debug_log "[DC derivation] Adding new DC: %a\n" DC.pp dc; *)
    edge.constraints <- edge.constraints @ [dc]
end


include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(LTS.Node)(EdgeData)
module EdgeSet = Caml.Set.Make(E)
module EdgeMap = Caml.Map.Make(E)

include DefaultDot


let pp_element fmt (kind, branch, loc) = 
  F.fprintf fmt "%a[%s](%B)" Sil.pp_if_kind kind (Location.to_string loc) branch

let edge_label : EdgeData.t -> string = fun edge_data ->
  match edge_data.branch_info with
  | Some prune_info -> F.asprintf "%a\n" pp_element prune_info
  | None -> ""

let vertex_attributes node = [ `Shape `Box; `Label (LTS.Node.to_string node) ]
let vertex_name vertex = string_of_int (LTS.Node.hash vertex)

let edge_attributes : E.t -> 'a list = fun (_, edge_data, _) -> (
  let label = edge_label edge_data in
  let label = if edge_data.backedge then label ^ "[backedge]\n" else label in
  let call_list = List.map (EdgeExp.CallPairSet.elements edge_data.calls) 
  ~f:(fun call_assignment ->
    match call_assignment with
    | EdgeExp.CallValue ((_, _, _, loc) as call) -> (
      F.asprintf "%s : %a" (EdgeExp.call_to_string call) Location.pp loc
    )
    | EdgeExp.CallPair (((_, _, _, loc1) as lb_call), ub_call) -> (
      F.asprintf "[%s; %s] : %a"
        (EdgeExp.call_to_string lb_call)
        (EdgeExp.call_to_string ub_call) Location.pp loc1
    )
  ) 
  in
  let calls_str = String.concat ~sep:"\n" call_list in

  (* Perform replacement to escape all harmful characters which corrupt dot file *)
  let label = String.substr_replace_all label ~pattern:"\"" ~with_:"\\\"" |>
    (* Remove newlines from string arguments of function calls and such to make it more readable *)
    String.substr_replace_all ~pattern:"\\n" ~with_:""
  in

  let label = match edge_data.edge_type with
  | GuardedDCP -> (
    let guards = List.map (EdgeExp.Set.elements edge_data.guards) 
      ~f:(fun guard -> F.asprintf "[GUARD] %s > 0" (EdgeExp.to_string guard))
    in

    let constraints = List.map edge_data.constraints 
      ~f:(fun dc -> (DC.to_string dc))
    in
    F.asprintf "%s\n%s\n%s\n%s" label 
    (String.concat ~sep:"\n" guards) 
    (String.concat ~sep:"\n" constraints) calls_str
  )
  | DCP -> (
    let constraints = List.map edge_data.constraints 
      ~f:(fun dc -> (DC.to_string dc))
    in
    F.asprintf "%s\n%s\n%s" label (String.concat ~sep:"\n" constraints) calls_str
  )
  in

  (* Perform replacement to escape all harmful characters which corrupt dot file *)
  let label = String.substr_replace_all label ~pattern:"\"" ~with_:"\\\"" |>
    (* Remove newlines from string arguments of function calls and such to make it more readable *)
    String.substr_replace_all ~pattern:"\\n" ~with_:""
  in
  [`Label label; `Color 4711]
)