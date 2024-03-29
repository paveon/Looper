(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module L = Logging

let skip_big_cfg checker ({InterproceduralAnalysis.proc_desc} as analysis_data) arg =
  let proc_size = Procdesc.size proc_desc in
  let too_big =
    Option.exists ~f:(fun limit -> proc_size > limit) Config.simple_lineage_max_cfg_size
  in
  if too_big then (
    L.user_warning "Skipped large (%d) procedure (%a)@." proc_size Procname.pp
      (Procdesc.get_proc_name proc_desc) ;
    None )
  else checker analysis_data arg


let skip_synthetic checker ({InterproceduralAnalysis.proc_desc} as analysis_data) arg =
  let is_synthetic =
    (* Ignore bodies synthesized by frontend for spec-only functions. *)
    (Procdesc.get_attributes proc_desc).ProcAttributes.is_synthetic_method
  in
  if is_synthetic then None else checker analysis_data arg


let skip_unwanted checker analysis_data arg =
  (skip_synthetic @@ skip_big_cfg @@ checker) analysis_data arg
