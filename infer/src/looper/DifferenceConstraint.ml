(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)


open! IStd
module F = Format
module L = Logging


(* Difference Constraint of form "x <= y + c"
 * Example: "(len - i) <= (len - i) + 1" *)
type norm = EdgeExp.t [@@deriving compare]
type rhs_const = Binop.t * IntLit.t [@@deriving compare]
type rhs = norm * Binop.t * IntLit.t [@@deriving compare]

type t = (norm * rhs) [@@deriving compare]


let make ?(const_part = Binop.PlusA None, IntLit.zero) lhs_norm rhs_norm = 
  let op, rhs_const = const_part in
  match op with
  | Binop.PlusA _ | Binop.Shiftrt -> lhs_norm, (rhs_norm, op, rhs_const)
  | _ -> assert(false)


let make_rhs ?(const_part = Binop.PlusA None, IntLit.zero) rhs_norm = 
  let op, rhs_const = const_part in
  match op with
  | Binop.PlusA _ | Binop.Shiftrt -> rhs_norm, op, rhs_const
  | _ -> assert(false)


let is_constant (lhs_norm, (rhs_norm, op, const)) = match op with
  | Binop.PlusA _ -> EdgeExp.equal lhs_norm rhs_norm && IntLit.iszero const
  | _ -> assert(false)


let same_norms (lhs_norm, (rhs_norm, _, _)) = EdgeExp.equal lhs_norm rhs_norm


let is_reset dc = not (same_norms dc)


let is_decreasing (_, (_, op, const)) = match op with
  | Binop.PlusA _ -> IntLit.isnegative const
  | _ -> false


let is_increasing (_, (_, op, const)) = match op with
  | Binop.PlusA _ -> not (IntLit.isnegative const) && not (IntLit.iszero const)
  | _ -> false


let to_string (lhs, (rhs_norm, op, rhs_const)) =
  let rhs_str = if EdgeExp.is_zero rhs_norm then (
    match op with
    | Binop.PlusA _ -> (
      if IntLit.iszero rhs_const then "0"
      else if IntLit.isnegative rhs_const then "-" ^ IntLit.to_string (IntLit.neg rhs_const)
      else IntLit.to_string rhs_const
    )
    | Binop.Shiftrt -> "0"
    | _ -> L.(die InternalError)"TODO: unsupported op: %s %a" (Binop.str Pp.text op) IntLit.pp rhs_const
  ) 
  else (
    match op with
    | Binop.PlusA _ -> (
      if IntLit.iszero rhs_const then EdgeExp.to_string rhs_norm
      else if IntLit.isnegative rhs_const then F.asprintf "%a - %a" EdgeExp.pp rhs_norm IntLit.pp (IntLit.neg rhs_const)
      else F.asprintf "%a + %a" EdgeExp.pp rhs_norm IntLit.pp rhs_const
    )
    | Binop.Shiftrt -> (
      if IntLit.iszero rhs_const then EdgeExp.to_string rhs_norm
      else F.asprintf "%a >> %a" EdgeExp.pp rhs_norm IntLit.pp rhs_const
    )
    | _ -> L.(die InternalError)"TODO: unsupported op: %s %a" (Binop.str Pp.text op) IntLit.pp rhs_const
  )
  in
  F.asprintf "%a' <= %s" EdgeExp.pp lhs rhs_str


let pp fmt dc = 
  F.fprintf fmt "%s" (to_string dc)


module Map = struct
  type dc = t

  include EdgeExp.Map

  let get_dc key map =
    match find_opt key map with
    | Some (rhs_norm, op, rhs_const) -> Some (key, (rhs_norm, op, rhs_const))
    | None -> None

  let add_dc dc_lhs dc_rhs map =
    let rhs_norm, _, rhs_const = dc_rhs in
    if EdgeExp.equal dc_lhs rhs_norm && IntLit.iszero rhs_const then (
      (* Check if set already contains some constraint with this left hand side *)
      if mem dc_lhs map then (
        (* Do not replace [e <= expr] *)
        map
      ) 
      else add dc_lhs dc_rhs map
    ) 
    else (
      (* Replace constant dc [e <= e] with [e <= expr] *)
      add dc_lhs dc_rhs map
    )

  let to_string map =
    let tmp = fold (fun lhs_norm dc_rhs acc ->
      acc ^ (to_string (lhs_norm, dc_rhs)) ^ " "
    ) map ""
    in
    "[" ^ (String.rstrip tmp) ^ "]"
end