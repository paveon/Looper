module F = Format
module L = Logging

type theory_data =
  { theory: Why3.Theory.theory
  ; theory_extras: Why3.Theory.theory list
  ; symbols: Why3.Term.lsymbol LooperUtils.StringMap.t
  ; var_typ: Why3.Ty.ty
  ; mk_const: Why3.BigInt.t -> Why3.Term.term
  ; get_op: string -> Why3.Term.lsymbol
  ; zero: Why3.Term.term
  ; one: Why3.Term.term }

type prover_data =
  { name: string
  ; prover_conf: Why3.Whyconf.config_prover
  ; driver: Why3.Driver.driver
  ; main: Why3.Whyconf.main
  ; real_data: theory_data
  ; int_data: theory_data
  ; mutable idents: Why3.Ident.preid LooperUtils.StringMap.t
  ; mutable vars: Why3.Term.vsymbol LooperUtils.StringMap.t }

type prover = Z3 | CVC4 | Vampire

val compare_prover : prover -> prover -> int

type prover_cfg =
  { prover_type: prover
  ; name: string
  ; driver_path: string
  ; extras_path: string list
  ; command: string
  ; command_steps: string option }

module ProverMap : sig
  type key = prover

  type +!'a t

  val empty : 'a t

  val is_empty : 'a t -> bool

  val mem : key -> 'a t -> bool

  val add : key -> 'a -> 'a t -> 'a t

  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t

  val singleton : key -> 'a -> 'a t

  val remove : key -> 'a t -> 'a t

  val merge : (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t

  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t

  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  val iter : (key -> 'a -> unit) -> 'a t -> unit

  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val for_all : (key -> 'a -> bool) -> 'a t -> bool

  val exists : (key -> 'a -> bool) -> 'a t -> bool

  val filter : (key -> 'a -> bool) -> 'a t -> 'a t

  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t

  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t

  val cardinal : 'a t -> int

  val bindings : 'a t -> (key * 'a) list

  val min_binding : 'a t -> key * 'a

  val min_binding_opt : 'a t -> (key * 'a) option

  val max_binding : 'a t -> key * 'a

  val max_binding_opt : 'a t -> (key * 'a) option

  val choose : 'a t -> key * 'a

  val choose_opt : 'a t -> (key * 'a) option

  val split : key -> 'a t -> 'a t * 'a option * 'a t

  val find : key -> 'a t -> 'a

  val find_opt : key -> 'a t -> 'a option

  val find_first : (key -> bool) -> 'a t -> key * 'a

  val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option

  val find_last : (key -> bool) -> 'a t -> key * 'a

  val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option

  val map : ('a -> 'b) -> 'a t -> 'b t

  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t

  val to_seq : 'a t -> (key * 'a) Seq.t

  val to_rev_seq : 'a t -> (key * 'a) Seq.t

  val to_seq_from : key -> 'a t -> (key * 'a) Seq.t

  val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t

  val of_seq : (key * 'a) Seq.t -> 'a t
end

val looper_src_dir : string

val supported_provers : prover_cfg list

val console_log : ('a, F.formatter, unit) IStd.format -> 'a

val why3_data : prover_data ProverMap.t ref

val get_prover_map : 'a InterproceduralAnalysis.t -> prover_data ProverMap.t
