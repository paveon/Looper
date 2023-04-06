(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
open! IStd
module L = Logging
module F = Format

let rec traverse ~root acc target_path =
  let target_path = if Filename.is_absolute target_path then target_path else root ^/ target_path in
  match Sys.is_directory target_path with
  | `Yes when ISys.file_exists (ResultsDirEntryName.get_path ~results_dir:target_path CaptureDB) ->
      (* we found a capture DB so add this as a target line *)
      Printf.sprintf "dummy\t-\t%s" target_path :: acc
  | `Yes ->
      (* recurse into non-infer-out directory *)
      Sys.readdir target_path
      |> Array.fold ~init:acc ~f:(fun acc entry ->
             traverse ~root acc (Filename.concat target_path entry) )
  | _ ->
      acc


let run_capture buck2_build_cmd =
  L.debug Capture Quiet "Processed buck2 bxl command '%a'@\n" (Pp.seq F.pp_print_string)
    buck2_build_cmd ;
  let infer_deps_lines =
    Buck.wrap_buck_call ~extend_env:[] V2 ~label:"build" ("buck2" :: buck2_build_cmd)
    |> List.fold ~init:[] ~f:(traverse ~root:Config.buck2_root)
    |> List.dedup_and_sort ~compare:String.compare
  in
  let infer_deps = ResultsDir.get_path CaptureDependencies in
  Utils.with_file_out infer_deps ~f:(fun out_channel ->
      Out_channel.output_lines out_channel infer_deps_lines )


let capture build_cmd =
  let bxl_target =
    match Config.buck2_bxl_target with
    | None ->
        L.die UserError "A BXL script must be provided when capturing with buck2/clang.@\n"
    | Some target ->
        target
  in
  let _prog, buck2_args = (List.hd_exn build_cmd, List.tl_exn build_cmd) in
  let _command, rev_not_targets, targets = Buck.parse_command_and_targets Clang V2 buck2_args in
  if List.is_empty targets then L.user_warning "No targets found to capture.@\n"
  else
    let targets_with_arg =
      List.fold targets ~init:[] ~f:(fun acc target -> "--target" :: target :: acc)
    in
    let args_to_store =
      ["--"]
      @ Option.value_map Config.buck_dependency_depth ~default:[] ~f:(fun depth ->
            ["--depth"; Int.to_string depth] )
      @ targets_with_arg
    in
    let buck2_build_cmd =
      ["bxl"; bxl_target] @ List.rev rev_not_targets @ Config.buck2_build_args_no_inline
      @ Buck.store_args_in_file ~identifier:"clang_buck2_bxl" args_to_store
    in
    run_capture buck2_build_cmd


let abs_buck2_root = Utils.realpath Config.buck2_root

let file_capture () =
  let bxl_target =
    match Config.buck2_bxl_target with
    | None ->
        L.die UserError "A BXL script must be provided when using file capture with bxl/clang.@\n"
    | Some target ->
        target
  in
  let file_set_to_capture =
    match SourceFile.read_config_changed_files () with
    | None ->
        L.die UserError "File capture requires supplying a --changed-files-index argument.@\n"
    | Some files ->
        files
  in
  let existing_absolute_paths =
    SourceFile.Set.fold
      (fun file acc ->
        let abs_file_path = SourceFile.to_abs_path file in
        match Sys.file_exists abs_file_path with `Yes -> abs_file_path :: acc | _ -> acc )
      file_set_to_capture []
  in
  if List.is_empty existing_absolute_paths then
    L.user_warning "File capture found no existing paths.@\n" ;
  let buck2_root_relative_paths =
    List.fold existing_absolute_paths ~init:[] ~f:(fun acc abs_file_path ->
        Utils.filename_to_relative ~root:abs_buck2_root abs_file_path
        |> Option.fold ~init:acc ~f:(fun acc path_rel_to_buck2_root ->
               path_rel_to_buck2_root :: acc ) )
  in
  if List.is_empty buck2_root_relative_paths then
    L.user_warning "No files found to capture relative to buck2 root.@\n"
  else
    let files_with_arg =
      List.fold buck2_root_relative_paths ~init:[] ~f:(fun acc path -> "--file" :: path :: acc)
    in
    let args_to_store =
      ["--"]
      @ Option.value_map Config.buck_dependency_depth ~default:[] ~f:(fun depth ->
            ["--depth"; Int.to_string depth] )
      @ files_with_arg
    in
    let buck2_build_cmd =
      ["bxl"; bxl_target] @ Config.buck2_build_args_no_inline
      @ Buck.store_args_in_file ~identifier:"clang_buck2_bxl_file" args_to_store
    in
    run_capture buck2_build_cmd
