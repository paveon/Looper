(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open LooperUtils
module F = Format
module L = Logging
(*
module BasicCostWithReason = CostDomain.BasicCostWithReason *)
(* open BufferOverrunUtils.ModelEnv
 *)
(* module BasicCost = Costlib.CostDomain.BasicCost *)
(* module BoSummary = BO.BufferOverrunAnalysisSummary *)
(* open ProcnameDispatcher.Call.FuncArg *)
(* open CostUtils.CostModelEnv *)

module LooperModelEnv = struct
  type t =
    { pname: Procname.t
    ; node_hash: int
    ; location: Location.t
    ; tenv: Tenv.t
    ; integer_type_widths: Typ.IntegerWidths.t
    ; get_summary: Procname.t -> LooperSummary.t option }

  let mk_model_env pname ~node_hash location tenv integer_type_widths get_summary =
    {pname; node_hash; location; tenv; integer_type_widths; get_summary}
end

(* let unit_cost_model _model_env ~ret:_ _inferbo_mem = BasicCost.one () *)

(* let cost_of_exp:
   Exp.t ->
   degree_kind:Polynomials.DegreeKind.t ->
   of_function:string ->
   LooperModelEnv.t ->
   ret:'a ->
   EdgeExp.T.t =
   fun exp ~degree_kind ~of_function {integer_type_widths; location} ~ret:_ -> (
     (* TODO: Figure out what to do here, return 1 for now *)
     debug_log "[COST_OF_EXP]: %a@," Exp.pp exp;
     EdgeExp.one
   ) *)

(* let linear = cost_of_exp ~degree_kind:Polynomials.DegreeKind.Linear

   let log = cost_of_exp ~degree_kind:Polynomials.DegreeKind.Log *)

module type ContainerSignature = sig
  val length : Exp.t -> BufferOverrunDomain.Mem.t -> BufferOverrunDomain.Val.t
end

module CString : ContainerSignature = struct
  let length exp inferbo_mem = BufferOverrunSemantics.eval_string_len exp inferbo_mem
end
(*
   module BoundsOf (Container : ContainerSignature) = struct
     let of_length :
            EdgeExp.ValuePair.t list
         -> of_function:string
         -> complexity:EdgeExp.ComplexityDegree.t
         -> LooperSummary.Model.t =
      fun args ~of_function ~complexity ->
       (* TODO: How should we deal with more arguments?? *)
       assert (Int.equal (List.length args) 1) ;
       LooperUtils.debug_log "[BoundsOf.of_length] via: %s@," of_function ;
       let complexity =
         match List.hd_exn args with
         | EdgeExp.ValuePair.V arg ->
             EdgeExp.ValuePair.V (EdgeExp.T.Symbolic (complexity, arg))
         | EdgeExp.ValuePair.P (lb, ub) ->
             if EdgeExp.equal lb ub then EdgeExp.ValuePair.V (EdgeExp.T.Symbolic (complexity, lb))
             else
               EdgeExp.ValuePair.P
                 (EdgeExp.T.Symbolic (complexity, lb), EdgeExp.T.Symbolic (complexity, ub))
       in
       let model : LooperSummary.Model.t =
         { name= of_function
         ; complexity
         ; return_bound= Some complexity
         ; side_effects= EdgeExp.Map.empty
         ; monotonicity_map= IntMap.empty }
       in
       model


     (* TODO *)
     (* let itv = Container.length exp mem |> BufferOverrunDomain.Val.get_itv in
        CostUtils.of_itv ~itv ~degree_kind ~of_function location *)

     let linear_length = of_length ~complexity:EdgeExp.ComplexityDegree.Linear

     let logarithmic_length = of_length ~complexity:EdgeExp.ComplexityDegree.Log

     let n_log_n_length = of_length ~complexity:EdgeExp.ComplexityDegree.Linearithmic
   end

   module BoundsOfContainer = BoundsOf (CostUtils.Container)
   module BoundsOfArray = BoundsOf (CostUtils.Array)
   module BoundsOfCString = BoundsOf (CString) *)

let std_container_ord _ str =
  List.exists ~f:(String.equal str) ["map"; "multimap"; "multiset"; "set"]


let std_container_unord _ str =
  List.exists ~f:(String.equal str)
    ["unordered_map"; "unordered_multimap"; "unordered_multiset"; "unordered_set"]


let get_strlen_model ~of_function arg_pairs _ =
  let model : LooperSummary.Model.t =
    let compute_complexity (args : (EdgeExp.T.t * Typ.t) list) cache ~variable_bound =
      (* variable_bound:(bound_type:BoundType.t -> EdgeExp.T.t -> cache -> EdgeExp.T.t * cache) *)
      assert (Int.equal (List.length args) 1) ;
      let strlen_arg, _ = List.hd_exn args in
      let complexity =
        match strlen_arg with
        | EdgeExp.T.Access arg ->
            EdgeExp.T.Strlen arg
        | _ ->
            L.die InternalError "[model: %s] Unexpected argument type: %a" of_function EdgeExp.pp
              strlen_arg
      in
      (complexity, cache)
    in
    assert (Int.equal (List.length arg_pairs) 1) ;
    let strlen_arg = List.hd_exn arg_pairs in
    let return_bound =
      match strlen_arg with
      | EdgeExp.ValuePair.V (EdgeExp.T.Access arg) ->
          EdgeExp.ValuePair.V (EdgeExp.T.Strlen arg)
      | EdgeExp.ValuePair.P (EdgeExp.T.Access lb, EdgeExp.T.Access ub) ->
          if HilExp.AccessExpression.equal lb ub then EdgeExp.ValuePair.V (EdgeExp.T.Strlen lb)
          else EdgeExp.ValuePair.P (EdgeExp.T.Strlen lb, EdgeExp.T.Strlen ub)
      | _ ->
          L.die InternalError "[model: %s] Unexpected argument type: %a" of_function
            EdgeExp.ValuePair.pp strlen_arg
    in
    let monotonicity_map = IntMap.singleton 0 Monotonicity.NonDecreasing in
    { name= of_function
    ; compute_complexity
    ; return_bound= Some return_bound
    ; side_effects= EdgeExp.Map.empty
    ; monotonicity_map }
  in
  model


let get_strtoul_model ~of_function arg_pairs widths =
  let model : LooperSummary.Model.t =
    assert (Int.equal (List.length arg_pairs) 5) ;
    (* let input_str = List.nth_exn arg_pairs 0 in
       let complexity =
         match input_str with
         | EdgeExp.ValuePair.V (EdgeExp.T.Access arg) ->
             EdgeExp.ValuePair.V (EdgeExp.T.Strlen arg)
         | EdgeExp.ValuePair.P (EdgeExp.T.Access lb, EdgeExp.T.Access ub) ->
             if HilExp.AccessExpression.equal lb ub then EdgeExp.ValuePair.V (EdgeExp.T.Strlen lb)
             else EdgeExp.ValuePair.P (EdgeExp.T.Strlen lb, EdgeExp.T.Strlen ub)
         | _ ->
             L.die InternalError "[model: %s] Unexpected argument type: %a" of_function
               EdgeExp.ValuePair.pp input_str
       in *)
    let compute_complexity (args : (EdgeExp.T.t * Typ.t) list) cache ~variable_bound =
      (* variable_bound:(bound_type:BoundType.t -> EdgeExp.T.t -> cache -> EdgeExp.T.t * cache) *)
      assert (Int.equal (List.length args) 5) ;
      let input_str, _ = List.nth_exn args 0 in
      let complexity =
        match input_str with
        | EdgeExp.T.Access arg ->
            EdgeExp.T.Strlen arg
        | _ ->
            L.die InternalError "[model: %s] Unexpected argument type: %a" of_function EdgeExp.pp
              input_str
      in
      (complexity, cache)
    in
    let ret_lb, ret_ub = Typ.range_of_ikind widths Typ.IULong in
    let output_bound =
      ( EdgeExp.T.Const (Const.Cint (IntLit.of_big_int ret_lb))
      , EdgeExp.T.Const (Const.Cint (IntLit.of_big_int ret_ub)) )
    in
    let output_arg_pair = List.nth_exn arg_pairs 3 in
    let side_effects =
      match output_arg_pair with
      | EdgeExp.ValuePair.V output_arg ->
          EdgeExp.Map.singleton output_arg output_bound
      | _ ->
          debug_log "[get_strtoul_model: %s] Output argument is not a single value: %a" of_function
            EdgeExp.ValuePair.pp output_arg_pair ;
          EdgeExp.Map.empty
    in
    let monotonicity_map = IntMap.singleton 0 Monotonicity.NonDecreasing in
    {name= of_function; compute_complexity; return_bound= None; side_effects; monotonicity_map}
  in
  model


let get_memcmp_model ~of_function arg_pairs _ =
  let model : LooperSummary.Model.t =
    let compute_complexity (args : (EdgeExp.T.t * Typ.t) list) cache
        ~(variable_bound :
              bound_type:BoundType.t
           -> EdgeExp.T.t
           -> LooperSummary.cache
           -> EdgeExp.T.t * LooperSummary.cache ) =
      assert (Int.equal (List.length args) 3) ;
      let norm, _ = List.nth_exn args 2 in
      let complexity, cache = variable_bound norm cache ~bound_type:BoundType.Upper in
      (complexity, cache)
    in
    assert (Int.equal (List.length arg_pairs) 3) ;
    (* let complexity = List.nth_exn arg_pairs 2 in *)
    let return_bound = Some (EdgeExp.ValuePair.V (EdgeExp.T.Const (Const.Cint IntLit.zero))) in
    let monotonicity_map = IntMap.singleton 2 Monotonicity.NonDecreasing in
    { name= of_function
    ; compute_complexity
    ; return_bound
    ; side_effects= EdgeExp.Map.empty
    ; monotonicity_map }
  in
  model


(* memcasecmp *)

type get_model_summary = LooperModelEnv.t -> ret:Ident.t * Typ.t -> LooperSummary.Model.t

module Call = struct
  let models =
    [ ("strlen", get_strlen_model)
    ; ("xstrtoumax", get_strtoul_model)
    ; ("memcmp", get_memcmp_model)
    ; ("memcasecmp", get_memcmp_model) ]


  let get_model :
      Procname.t -> EdgeExp.ValuePair.t list -> Exe_env.t -> LooperSummary.Model.t option =
   fun proc_name args exe_env ->
    let widths = Exe_env.get_integer_type_widths exe_env proc_name in
    let proc_name_str = Procname.to_string proc_name in
    List.find_map models ~f:(fun (model_name, get_model) ->
        if equal_string model_name proc_name_str then
          Some (get_model ~of_function:model_name args widths)
        else None )
  (* let dispatch : (Tenv.t, get_model_summary, unit) ProcnameDispatcher.Call.dispatcher =
     let open ProcnameDispatcher.Call in
     (* let int_typ = Typ.mk (Typ.Tint Typ.IInt) in *)
     let dispatcher =
       make_dispatcher
         [ -"strlen" <>$ capt_exp
           $--> BoundsOfCString.linear_length ~of_function:"strlen"
           (* C++ Cost Models *)
         ; -"std" &::+ std_container_ord &:: "find" $ capt_exp
           $+...$--> BoundsOfContainer.logarithmic_length ~of_function:"Container.find"
         ; -"std" &::+ std_container_unord &:: "find" $ capt_exp
           $+...$--> BoundsOfContainer.linear_length ~of_function:"Container.find"
         ; -"std" &::+ std_container_ord &:: "count" $ capt_exp
           $+...$--> BoundsOfContainer.logarithmic_length ~of_function:"Container.count"
         ; -"std" &::+ std_container_unord &:: "count" $ capt_exp
           $+...$--> BoundsOfContainer.linear_length ~of_function:"Container.count"]
     in
     merge_dispatchers dispatcher FbCostModels.Call.dispatch *)
end
