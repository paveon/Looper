(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open! IStd
module F = Format
module L = Logging

(* Difference Constraint of form "x <= y + c"
 * Example: "(len - i) <= (len - i) + 1" *)
type norm = EdgeExp.T.t [@@deriving compare]

type rhs_const = Binop.t * IntLit.t [@@deriving compare]

type value_rhs = norm * Binop.t * IntLit.t [@@deriving compare]

type rhs = Value of value_rhs | Pair of (value_rhs * value_rhs) [@@deriving compare]

type t = norm * rhs [@@deriving compare]

let make ?(const_part = (Binop.PlusA None, IntLit.zero)) lhs_norm rhs_norm =
  let op, rhs_const = const_part in
  match op with
  | Binop.PlusA _ | Binop.Shiftrt ->
      (lhs_norm, Value (rhs_norm, op, rhs_const))
  | _ ->
      assert false


let make_value_rhs ?(const_part = (Binop.PlusA None, IntLit.zero)) rhs_norm =
  let op, rhs_const = const_part in
  match op with Binop.PlusA _ | Binop.Shiftrt -> (rhs_norm, op, rhs_const) | _ -> assert false


let rec is_constant (lhs_norm, rhs) =
  match rhs with
  | Value (rhs_norm, op, const) -> (
    match op with
    | Binop.PlusA _ ->
        EdgeExp.equal lhs_norm rhs_norm && IntLit.iszero const
    | _ ->
        assert false )
  | Pair (lower_rhs, upper_rhs) ->
      is_constant (lhs_norm, Value lower_rhs) && is_constant (lhs_norm, Value upper_rhs)


let rec same_norms (lhs_norm, rhs) =
  match rhs with
  | Value (rhs_norm, _, _) ->
      EdgeExp.equal lhs_norm rhs_norm
  | Pair (lower_rhs, upper_rhs) ->
      same_norms (lhs_norm, Value lower_rhs) && same_norms (lhs_norm, Value upper_rhs)


let is_reset dc = not (same_norms dc)

let rec is_decreasing (lhs_norm, rhs) =
  match rhs with
  | Value (_, op, const) -> (
    match op with
    | Binop.PlusA _ ->
        IntLit.isnegative const
    | Binop.Shiftrt ->
        not (IntLit.isnegative const || IntLit.iszero const)
    | _ ->
        false )
  | Pair (lower_rhs, upper_rhs) ->
      is_decreasing (lhs_norm, Value lower_rhs) && is_decreasing (lhs_norm, Value upper_rhs)


let rec is_increasing (lhs_norm, rhs) =
  match rhs with
  | Value (_, op, const) -> (
    match op with
    | Binop.PlusA _ ->
        (not (IntLit.isnegative const)) && not (IntLit.iszero const)
    | _ ->
        false )
  | Pair (lower_rhs, upper_rhs) ->
      is_increasing (lhs_norm, Value lower_rhs) && is_increasing (lhs_norm, Value upper_rhs)


let to_string_const_part (op, rhs_const) = F.asprintf "%a %a" Binop.pp op IntLit.pp rhs_const

let rec to_string (lhs, rhs) =
  let value_rhs_to_str (rhs_norm, op, rhs_const) =
    if EdgeExp.is_zero rhs_norm then
      match op with
      | Binop.PlusA _ ->
          if IntLit.iszero rhs_const then "0"
          else if IntLit.isnegative rhs_const then "-" ^ IntLit.to_string (IntLit.neg rhs_const)
          else IntLit.to_string rhs_const
      | Binop.Shiftrt ->
          "0"
      | _ ->
          L.(die InternalError)
            "TODO: unsupported op: %s %a" (Binop.str Pp.text op) IntLit.pp rhs_const
    else
      match op with
      | Binop.PlusA _ ->
          if IntLit.iszero rhs_const then EdgeExp.to_string rhs_norm
          else if IntLit.isnegative rhs_const then
            F.asprintf "%a - %a" EdgeExp.pp rhs_norm IntLit.pp (IntLit.neg rhs_const)
          else F.asprintf "%a + %a" EdgeExp.pp rhs_norm IntLit.pp rhs_const
      | Binop.Shiftrt ->
          if IntLit.iszero rhs_const then EdgeExp.to_string rhs_norm
          else F.asprintf "%a >> %a" EdgeExp.pp rhs_norm IntLit.pp rhs_const
      | _ ->
          L.(die InternalError)
            "TODO: unsupported op: %s %a" (Binop.str Pp.text op) IntLit.pp rhs_const
  in
  match rhs with
  | Value value_rhs ->
      F.asprintf "%a' <= %s" EdgeExp.pp lhs (value_rhs_to_str value_rhs)
  | Pair (lower_rhs, upper_rhs) ->
      F.asprintf "%a' <= [%s; %s]" EdgeExp.pp lhs (value_rhs_to_str lower_rhs)
        (value_rhs_to_str upper_rhs)


let pp_const_part fmt rhs_const = F.fprintf fmt "%s" (to_string_const_part rhs_const)

let pp fmt dc = F.fprintf fmt "%s" (to_string dc)

let get_dc norm dc_list = List.find dc_list ~f:(fun (lhs_norm, _) -> EdgeExp.equal norm lhs_norm)
