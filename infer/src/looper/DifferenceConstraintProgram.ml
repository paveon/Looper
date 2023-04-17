(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
open LooperUtils
module F = Format
module DC = DifferenceConstraint
module LTS = LabeledTransitionSystem

let debug_log : ('a, Format.formatter, unit) format -> 'a =
 fun fmt -> F.fprintf (List.hd_exn !debug_fmt) fmt


(* Difference Constraint Program *)
type edge_output_type = GuardedDCP | DCP [@@deriving compare]

module EdgeData = struct
  type t =
    { backedge: bool
    ; branch_info: (Sil.if_kind * bool * Location.t) option
    ; mutable calls: EdgeExp.CallPair.Set.t
    ; mutable constraints: DC.t list
    ; mutable guards: EdgeExp.Set.t
    ; mutable condition_norms: EdgeExp.Set.t list
    ; mutable bound: EdgeExp.T.t option
    ; mutable bound_norm: EdgeExp.T.t option
    ; mutable computing_bound: bool
    ; mutable edge_type: edge_output_type }
  [@@deriving compare]

  let equal = [%compare.equal: t]

  let from_lts_edge (lts_edge_data : LTS.EdgeData.t) =
    { backedge= lts_edge_data.backedge
    ; branch_info= lts_edge_data.branch_info
    ; calls= lts_edge_data.calls
    ; constraints= []
    ; guards= EdgeExp.Set.empty
    ; condition_norms= lts_edge_data.condition_norms
    ; bound= None
    ; bound_norm= None
    ; computing_bound= false
    ; edge_type= DCP }


  let get_dc key constraints =
    let constraint_opt = List.find constraints ~f:(fun (lhs, _) -> EdgeExp.equal key lhs) in
    match constraint_opt with Some dc -> Some dc | None -> None


  let add_dc dc_lhs ((rhs_norm, _, rhs_const) as dc_rhs) constraints =
    if EdgeExp.equal dc_lhs rhs_norm && IntLit.iszero rhs_const then
      (* Check if set already contains some constraint with this left hand side *)
      match get_dc dc_lhs constraints with
      | Some _ ->
          (* Do not replace [e <= expr] *)
          constraints
      | None ->
          constraints @ [(dc_lhs, dc_rhs)]
    else (* Replace constant dc [e <= e] with [e <= expr] *)
      constraints @ [(dc_lhs, dc_rhs)]


  let is_reset edge norm =
    match get_dc norm edge.constraints with Some dc -> not (DC.same_norms dc) | None -> false


  let get_reset edge norm =
    match get_dc norm edge.constraints with
    | Some ((_, dc_rhs) as dc) when not (DC.same_norms dc) -> (
      match dc_rhs with
      | DC.Value (rhs_norm, op, lit) ->
          Some (EdgeExp.ValuePair.V (EdgeExp.merge rhs_norm (Some (op, lit))))
      | DC.Pair ((lb_norm, lb_op, lb_lit), (ub_norm, ub_op, ub_lit)) ->
          Some
            (EdgeExp.ValuePair.P
               ( EdgeExp.merge lb_norm (Some (lb_op, lb_lit))
               , EdgeExp.merge ub_norm (Some (ub_op, ub_lit)) ) ) )
    | _ ->
        None


  let is_backedge edge = edge.backedge

  let active_guards edge =
    EdgeExp.Set.fold
      (fun guard acc ->
        match get_dc guard edge.constraints with
        | Some dc ->
            if DC.is_decreasing dc && DC.same_norms dc then acc else EdgeExp.Set.add guard acc
        | _ ->
            EdgeExp.Set.add guard acc )
      edge.guards EdgeExp.Set.empty


  (* Required by Graph module interface *)
  let default =
    { backedge= false
    ; branch_info= None
    ; edge_type= DCP
    ; constraints= []
    ; calls= EdgeExp.CallPair.Set.empty
    ; guards= EdgeExp.Set.empty
    ; condition_norms= []
    ; bound= None
    ; bound_norm= None
    ; computing_bound= false }


  let set_edge_output_type edge output_type = edge.edge_type <- output_type

  let branch_type edge = match edge.branch_info with Some (_, branch, _) -> branch | _ -> false

  let add_guards edge guards = edge.guards <- guards

  let add_constraint edge dc =
    (* debug_log "[DC derivation] Adding new DC: %a\n" DC.pp dc; *)
    edge.constraints <- edge.constraints @ [dc]
end

include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (LTS.Node) (EdgeData)
module EdgeSet = Caml.Set.Make (E)
module EdgeMap = Caml.Map.Make (E)
include DefaultDot

let pp_element fmt (kind, branch, loc) =
  F.fprintf fmt "%a[%s](%B)" Sil.pp_if_kind kind (Location.to_string loc) branch


let edge_label : EdgeData.t -> string option =
 fun edge_data ->
  match edge_data.branch_info with
  | Some prune_info ->
      Some (F.asprintf "%a" pp_element prune_info)
  | None ->
      None


let vertex_attributes node =
  [`Shape `Box; `Label (LTS.Node.to_string node) (* `Fontname "monospace" *)]


let vertex_name vertex = string_of_int (LTS.Node.hash vertex)

let edge_attributes : E.t -> 'a list =
 fun (_, edge_data, _) ->
  let backedge_label = if edge_data.backedge then Some "[backedge]" else None in
  let calls_str =
    if EdgeExp.CallPair.Set.is_empty edge_data.calls then None
    else
      let call_list =
        List.map (EdgeExp.CallPair.Set.elements edge_data.calls) ~f:(fun call_assignment ->
            match call_assignment with
            | EdgeExp.CallPair.V ((_, _, _, loc) as call) ->
                F.asprintf "%s : %a" (EdgeExp.call_to_string call) Location.pp loc
            | EdgeExp.CallPair.P (((_, _, _, loc1) as lb_call), ub_call) ->
                F.asprintf "[%s; %s] : %a" (EdgeExp.call_to_string lb_call)
                  (EdgeExp.call_to_string ub_call) Location.pp loc1
            | _ ->
                assert false )
      in
      Some (String.concat ~sep:"\n" call_list)
  in
  let local_bound_label, edge_color =
    match edge_data.bound_norm with
    | Some norm ->
        ( Some (F.asprintf "[LB] %a" EdgeExp.pp norm)
        , if EdgeExp.equal norm EdgeExp.one then 0x006400 else 0xFF0000 )
    | None ->
        (None, 4711)
  in
  let condition_norms =
    if List.is_empty edge_data.condition_norms then None
    else
      Some
        ( "[CONDITIONS] "
        ^ ( List.map edge_data.condition_norms ~f:(fun and_terms ->
                List.map (EdgeExp.Set.elements and_terms) ~f:EdgeExp.to_string
                |> String.concat ~sep:" &&" )
          |> String.concat ~sep:" || " ) )
  in
  let label_parts =
    [edge_label edge_data; backedge_label; local_bound_label; calls_str; condition_norms]
  in
  let label_parts =
    match edge_data.edge_type with
    | GuardedDCP ->
        let guards =
          Some
            ( List.map (EdgeExp.Set.elements edge_data.guards) ~f:(fun guard ->
                  F.asprintf "[GUARD] %s > 0" (EdgeExp.to_string guard) )
            |> String.concat ~sep:"\n" )
        in
        label_parts @ [guards]
    | DCP ->
        label_parts
  in
  let constraints =
    Some (List.map edge_data.constraints ~f:(fun dc -> DC.to_string dc) |> String.concat ~sep:"\n")
  in
  let label_parts = label_parts @ [constraints] in
  let label =
    List.fold label_parts ~init:"" ~f:(fun label_acc part_opt ->
        match part_opt with Some part -> label_acc ^ F.asprintf "\n%s" part | None -> label_acc )
  in
  (* Perform replacement to escape all harmful characters which corrupt dot file *)
  let label =
    String.substr_replace_all label ~pattern:"\"" ~with_:"\\\""
    |> (* Remove newlines from string arguments of function calls and such to make it more readable *)
    String.substr_replace_all ~pattern:"\\n" ~with_:""
  in
  [`Label label; `Color edge_color (* `Fontname "monospace" *)]
