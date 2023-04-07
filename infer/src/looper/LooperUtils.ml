(* Author: Ondrej Pavela <xpavel34@stud.fit.vutbr.cz> *)


open! IStd
module F = Format


let debug_fmt = ref [F.std_formatter]


module PvarMap = struct
  include Caml.Map.Make(Pvar)

  let to_string map =
    F.asprintf "[%s]" (String.concat ~sep:" " (List.map (bindings map) ~f:(fun (pvar, _) -> Pvar.to_string pvar)))

  let pp fmt map = F.fprintf fmt "%s" (to_string map)
end


module StringMap = Caml.Map.Make(struct
    type nonrec t = string
    let compare = compare_string
  end)


type prover_data = {
  name: string;
  prover_conf: Why3.Whyconf.config_prover;
  driver: Why3.Driver.driver;
  main : Why3.Whyconf.main;
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


let looper_src_dir = Config.bin_dir ^/ Filename.parent_dir_name ^/ "src" ^/ "looper"

let supported_provers = [
    {
      prover_type = Z3;
      name = "Z3";
      driver_path = looper_src_dir ^/ "z3_custom.drv";
      command = "z3 -smt2 -t:%t000 sat.random_seed=42 model.compact=false nlsat.randomize=false smt.random_seed=42 -st %f";
      command_steps = Some "%e -smt2 sat.random_seed=42 model.compact=false nlsat.randomize=false smt.random_seed=42 memory_max_alloc_count=%S -st %f"
    };
    {
      prover_type = CVC4;
      name = "CVC4";
      driver_path = looper_src_dir ^/ "cvc4_16_custom.drv";
      command = "cvc4 --stats --tlimit-per=%t000 --lang=smt2 %f";
      command_steps = Some "%e --stats --rlimit=%S --lang=smt2 %f"
    }
  ]


module ProverMap = Caml.Map.Make(struct
  type nonrec t = prover
  let compare = compare_prover
end)

module AccessSet = Caml.Set.Make(struct
  type nonrec t = AccessPath.t
  let compare = AccessPath.compare
end)

module AccessPathMap = Caml.Map.Make(struct
  type nonrec t = AccessPath.t
  let compare = AccessPath.compare
end)

module AccessExpressionSet = Caml.Set.Make(struct
  type nonrec t = HilExp.access_expression
  let compare = HilExp.compare_access_expression
end)

module AccessExpressionMap = Caml.Map.Make(struct
  type nonrec t = HilExp.access_expression
  let compare = HilExp.compare_access_expression
end)

module Monotonicity = struct
  type t =
    | NonDecreasing
    | NonIncreasing
    | NotMonotonic
  [@@deriving compare]
end

module BoundType = struct
  type t = 
    | Upper 
    | Lower
  [@@deriving compare]
end

let base_of_id id typ = (Var.of_id id, typ)

let access_of_exp ~include_array_indexes exp0 typ0 ~(f_resolve_id : Var.t -> AccessPath.t option) =
  (* [typ] is the type of the last element of the access path (e.g., typeof(g) for x.f.g) *)
  let rec of_exp_ exp typ accesses acc =
    match exp with
    | Exp.Var id -> (
        match f_resolve_id (Var.of_id id) with
        | Some (base, base_accesses) ->
          (base, base_accesses @ accesses) :: acc
        | None ->
          (base_of_id id typ, accesses) :: acc )
    | Exp.Lvar pvar when Pvar.is_ssa_frontend_tmp pvar -> (
        match f_resolve_id (Var.of_pvar pvar) with
        | Some (base, base_accesses) ->
          (base, base_accesses @ accesses) :: acc
        | None ->
          (AccessPath.base_of_pvar pvar typ, accesses) :: acc )
    | Exp.Lvar pvar ->
      (AccessPath.base_of_pvar pvar typ, accesses) :: acc
    | Exp.Lfield (root_exp, fld, root_exp_typ) ->
      let field_access = AccessPath.FieldAccess fld in
      of_exp_ root_exp root_exp_typ (field_access :: accesses) acc
    | Exp.Lindex (root_exp, index_exp) ->
      let index_access_paths =
        if include_array_indexes then of_exp_ index_exp typ [] [] else []
      in
      let array_access = AccessPath.ArrayAccess (typ, index_access_paths) in
      let array_typ = Typ.mk_array typ in
      of_exp_ root_exp array_typ (array_access :: accesses) acc
    | Exp.Cast (cast_typ, cast_exp) ->
      of_exp_ cast_exp cast_typ [] acc
    | Exp.UnOp (_, unop_exp, _) ->
      of_exp_ unop_exp typ [] acc
    | Exp.Exn exn_exp ->
      of_exp_ exn_exp typ [] acc
    | Exp.BinOp (_, exp1, exp2) ->
      of_exp_ exp1 typ [] acc |> of_exp_ exp2 typ []
    | Exp.Const _ | Closure _ | Sizeof _ ->
      (* trying to make access path from an invalid expression *)
      acc
  in
  of_exp_ exp0 typ0 [] []

let access_of_lhs_exp ~include_array_indexes lhs_exp typ ~(f_resolve_id : Var.t -> AccessPath.t option) =
  match access_of_exp ~include_array_indexes lhs_exp typ ~f_resolve_id with
  | [lhs_ap] -> Some lhs_ap
  | _ -> None


module DefaultDot = struct
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let default_vertex_attributes _ = []
  let graph_attributes _ = []
end


let output_graph filepath graph output_fun =
  let out_c = Utils.out_channel_create_with_dir filepath in
  output_fun out_c graph;
  Out_channel.close out_c