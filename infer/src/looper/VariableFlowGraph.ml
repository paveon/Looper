(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)


open! IStd
open LooperUtils
module DCP = DifferenceConstraintProgram


(* Variable flow graph *)
module Node = struct
  type t = EdgeExp.t * DCP.Node.t [@@deriving compare]
  let hash x = Hashtbl.hash_param 100 100 x
  let equal = [%compare.equal: t]
end

module Edge = struct
  type t = unit [@@deriving compare]
  let hash = Hashtbl.hash
  let equal = [%compare.equal : t]
  let default = ()
  end
include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node)(Edge)
module NodeSet = Caml.Set.Make(V)
module EdgeSet = Caml.Set.Make(E)

include DefaultDot

let edge_attributes : E.t -> 'a list = fun _ -> [`Label ""; `Color 4711]
let vertex_attributes : V.t -> 'a list = fun (norm, dcp_node) -> (
  let label = F.asprintf "%a, %a" EdgeExp.pp norm DCP.Node.pp dcp_node in
  [ `Shape `Box; `Label label ]
)
let vertex_name : V.t -> string = fun vertex -> string_of_int (Node.hash vertex)

module Map = Caml.Map.Make(Node)