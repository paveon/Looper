(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)


open! IStd
module F = Format


val debug_fmt : (F.formatter list) ref


module PvarMap : sig
  include module type of Caml.Map.Make(Pvar)

  val pp : F.formatter -> 'a t -> unit

  val to_string : 'a t -> string
end


module StringMap : Caml.Map.S with type key = string


type prover_data = {
  name: string;
  prover_conf: Why3.Whyconf.config_prover;
  driver: Why3.Driver.driver;
  theory: Why3.Theory.theory;
  mutable idents: Why3.Ident.preid StringMap.t;
  mutable vars: Why3.Term.vsymbol StringMap.t;
}


type prover =
  | Z3
  | CVC4
  | Vampire
  [@@deriving compare]

type prover_cfg = {
  prover_type: prover;
  name: string;
  driver_path: string;
  command: string;
  command_steps: string option
}

val looper_src_dir : string

val supported_provers : prover_cfg list


module ProverMap : Caml.Map.S with type key = prover

module AccessSet : Caml.Set.S with type elt = AccessPath.t

module AccessPathMap : Caml.Map.S with type key = AccessPath.t

module VariableMonotony : sig
   type t =
   | NonDecreasing
   | NonIncreasing
   | NotMonotonic
   [@@deriving compare]
end


val access_of_exp : include_array_indexes:bool -> Exp.t -> Typ.t -> f_resolve_id:(Var.t -> AccessPath.t option) -> AccessPath.t list

val access_of_lhs_exp : include_array_indexes:bool -> Exp.t -> Typ.t -> f_resolve_id:(Var.t -> AccessPath.t option) -> AccessPath.t option


module DefaultDot : sig
   val default_edge_attributes : 'a -> 'b list
   val get_subgraph : 'a -> 'b option
   val default_vertex_attributes : 'a -> 'b list
   val graph_attributes : 'a -> 'b list
end


val output_graph : string -> 'a ->(Out_channel.t -> 'a -> unit) -> unit