(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)

open LooperUtils
module F = Format
module L = Logging

type prover_data =
  { name: string
  ; prover_conf: Why3.Whyconf.config_prover
  ; driver: Why3.Driver.driver
  ; main: Why3.Whyconf.main
  ; theory: Why3.Theory.theory
  ; mutable idents: Why3.Ident.preid StringMap.t
  ; mutable vars: Why3.Term.vsymbol StringMap.t }

type prover = Z3 | CVC4 | Vampire [@@deriving compare]

type prover_cfg =
  { prover_type: prover
  ; name: string
  ; driver_path: string
  ; command: string
  ; command_steps: string option }

module ProverMap = Caml.Map.Make (struct
  type nonrec t = prover

  let compare = compare_prover
end)

let looper_src_dir = Config.bin_dir ^/ Filename.parent_dir_name ^/ "src" ^/ "looper"

let supported_provers : prover_cfg list =
  [ { prover_type= Z3
    ; name= "Z3"
    ; driver_path= looper_src_dir ^/ "z3_custom.drv"
    ; command=
        "z3 -smt2 -t:%t000 sat.random_seed=42 model.compact=false nlsat.randomize=false \
         smt.random_seed=42 -st %f"
    ; command_steps=
        Some
          "%e -smt2 sat.random_seed=42 model.compact=false nlsat.randomize=false \
           smt.random_seed=42 memory_max_alloc_count=%S -st %f" }
  ; { prover_type= CVC4
    ; name= "CVC4"
    ; driver_path= looper_src_dir ^/ "cvc4_16_custom.drv"
    ; command= "cvc4 --stats --tlimit-per=%t000 --lang=smt2 %f"
    ; command_steps= Some "%e --stats --rlimit=%S --lang=smt2 %f" } ]


let console_log : ('a, F.formatter, unit) format -> 'a = fun fmt -> F.printf fmt

let why3_data = ref ProverMap.empty

let get_prover_map {InterproceduralAnalysis.proc_desc; err_log} : prover_data ProverMap.t =
  if ProverMap.is_empty !why3_data then (
    L.progress "@\n[LOOPER] Initializing Why3@\n" ;
    (* console_log "=========== Initializing Why3 ===========\n" ; *)
    let config : Why3.Whyconf.config = Why3.Whyconf.init_config None in
    let main : Why3.Whyconf.main = Why3.Whyconf.get_main config in
    let env : Why3.Env.env = Why3.Env.create_env (Why3.Whyconf.loadpath main) in
    let real_theory : Why3.Theory.theory = Why3.Env.read_theory env ["real"] "Real" in
    let prover_map =
      List.fold supported_provers ~init:ProverMap.empty ~f:(fun acc prover_cfg ->
          let filter = Why3.Whyconf.parse_filter_prover prover_cfg.name in
          let provers = Why3.Whyconf.filter_provers config filter in
          if Why3.Whyconf.Mprover.is_empty provers then (
            L.progress "@\n[LOOPER] Prover '%s' is not installed or configured.@\n" prover_cfg.name ;
            acc )
          else
            let why3_prover_cfg = snd (Why3.Whyconf.Mprover.max_binding provers) in
            let driver : Why3.Driver.driver =
              try Why3.Driver.load_driver_file_and_extras main env prover_cfg.driver_path []
              with e ->
                L.die InternalError "[Looper] Failed to load driver for %s: %a@." prover_cfg.name
                  Why3.Exn_printer.exn_printer e
            in
            ProverMap.add prover_cfg.prover_type
              { name= prover_cfg.name
              ; driver
              ; main
              ; theory= real_theory
              ; idents= StringMap.empty
              ; vars= StringMap.empty
              ; prover_conf=
                  { why3_prover_cfg with
                    command= prover_cfg.command
                  ; command_steps= prover_cfg.command_steps } }
              acc )
    in
    if ProverMap.is_empty prover_map then
      L.(die UserError)
        "[Looper] No suitable Why3 prover was found.\n\
         Please consult the following Why3 page on how\n\
         to install external provers: 'http://why3.lri.fr/doc/install.html'.\n\
         The list of external provers currently supported by Looper contains Z3 and CVC4.\n\
         The Z3 prover is recommended for best results." ;
    why3_data := prover_map ;
    !why3_data )
  else !why3_data
