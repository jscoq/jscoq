(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Helpers for the Coq JavaScript Toplevel. Based in the coq source
   code and js_of_ocaml toplevel.

   By Emilio J. Gallego Arias, Mines ParisTech, Paris.
*)

(* FIXME: Add LWT support to the STM. *)

open Pp
open Errors
open Util
open Names
open Names
open Feedback
open Pcoq

let print_toplevel_error (e, info) =
  Errors.iprint (e, info)

let pr_open_cur_subgoals () =
  try Printer.pr_open_subgoals ()
  with Proof_global.NoCurrentProof -> str ""

(* TODO:

- Get subgoals:

*)

let cs = ref (Stm.get_current_state ())

(* We call STM.add and wait. *)
(* let execute printval ?pp_code pp_answer s = *)
let execute s =
  (* Printf.eprintf "Sending %s to Coq!\n%!" s; *)
  try
    let cs',_ = Stm.add ~ontop:!cs true 0 s in (* Le zéro : à remplacer par un uid négatif *)
    Stm.finish ();
    cs := cs';
    msg_notice (pr_open_cur_subgoals ());
    flush stdout;
    flush stderr;
    flush_all ()
  with
  | any ->
     (* We need to revert the add *)
     let _ = Stm.edit_at !cs in
     (* cs := (Stm.get_current_state ()); *)
     let any = Errors.push any in
     Format.set_formatter_out_channel stdout;
     let msg = print_toplevel_error any ++ fnl () in
     pp_with ~pp_tag:Ppstyle.pp_tag !Pp_control.std_ft msg;
     pp_flush ()

(* We have no support for library paths for now, unfortunately, due to
   Coq running in the browser we may want to rewrite a big chunck of
   it. *)
let add_load_path pkg pkg_path =
  let coq_path = DirPath.make @@ List.rev @@ List.map Id.of_string pkg in
  Loadpath.add_load_path ("./" ^ pkg_path) coq_path ~implicit:false;
  Mltop.add_ml_dir pkg_path

(* JsCoq init process:
 *
 *)
let dyn_comp = true

let init ml_load =

  (* We hook library loading to avoid dynamic bytecode-to-js
     compilation *)
  let jstop : Mltop.toplevel = {
    load_obj = ml_load;
    (* We ignore all the other operations below *)
    use_file = (fun s  -> Printf.eprintf "[jstop] use_file \"%s\" called\n%!" s);
    add_dir  = (fun s  -> Printf.eprintf "[jstop] add_dir \"%s\" called\n%!" s);
    ml_loop  = (fun () -> Printf.eprintf "[jstop] ml_loop not supported\n%!");
  } in

  if not dyn_comp then
    Mltop.set_top jstop;

  (* Basic Coq init *)
  Lib.init();

  (* Local libraries: I'm not sure what I'm doing here *)
  (* XXX: What is going on there????, what to do with implicit *)
  let coq_default_path = DirPath.make [] in
  Loadpath.add_load_path "." coq_default_path ~implicit:true;
  Loadpath.add_load_path "." Nameops.default_root_prefix ~implicit:false;

  (* We need to declare a toplevel module name. Not sure what will
     happen in document mode *)
  let jsname = DirPath.make [Id.of_string "JsTop"] in
  Declaremods.start_library jsname;

  (* Initialize the STM. *)
  Stm.init();
  cs := Stm.get_current_state ()


let version =
  Coq_config.version, Coq_config.date, Coq_config.compile_date, Coq_config.caml_version

(* What coqtop.ml does:

  init_gc ();
  Sys.catch_break false; (* Ctrl-C is fatal during the initialisation *)
  Lib.init();
  (* Default Proofb Mode starts with an alternative default. *)
  Goptions.set_string_option_value ["Default";"Proof";"Mode"] "Classic";
  begin
    try
      let extras = parse_args arglist in
      (* If we have been spawned by the Spawn module, this has to be done
       * early since the master waits us to connect back *)
      Spawned.init_channels ();
      Envars.set_coqlib Errors.error;
      if !print_where then (print_endline(Envars.coqlib ()); exit(exitcode ()));
      if !print_config then (Usage.print_config (); exit (exitcode ()));
      if !print_tags then (print_style_tags (); exit (exitcode ()));
      if !filter_opts then (print_string (String.concat "\n" extras); exit 0);
      init_load_path ();
      Option.iter Mltop.load_ml_object_raw !toploop;
      let extras = !toploop_init extras in
      if not (List.is_empty extras) then begin
        prerr_endline ("Don't know what to do with "^String.concat " " extras);
        prerr_endline "See -help for the list of supported options";
        exit 1
      end;
      if_verbose print_header ();
      inputstate ();
      Mltop.init_known_plugins ();
      set_vm_opt ();
      engage ();
      set_hierarchy ();
      (* Be careful to set these variables after the inputstate *)
      Syntax_def.set_verbose_compat_notations !verb_compat_ntn;
      Syntax_def.set_compat_notations (not !no_compat_ntn);
      if (not !batch_mode || List.is_empty !compile_list)
         && Global.env_is_initial ()
      then Option.iter Declaremods.start_library !toplevel_name;
      init_library_roots ();
      load_vernac_obj ();
      require ();
      Stm.init ();
      load_rcfile();
      load_vernacular ();
      compile_files ();
      schedule_vio_checking ();
      schedule_vio_compilation ();
      check_vio_tasks ();
      outputstate ()
    with any ->
      let any = Errors.push any in
      flush_all();
      let msg =
        if !batch_mode then mt ()
        else str "Error during initialization:" ++ fnl ()
      in
      fatal_error (msg ++ Coqloop.print_toplevel_error any) (Errors.is_anomaly (fst any))
  end;
*)
  (* Enable backtraces for now. *)
  (* Printexc.record_backtrace true; *)
  (* try *)
  (* Dynlink.init (); *)
  (* with *)
  (* | exn -> *)
  (*    begin *)
  (*      Printexc.print_backtrace stderr; *)
  (*      raise exn *)
  (*    end; *)
  (* XXX: Add support for loading base plugins and libraries *)
