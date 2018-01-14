(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Coq Interface to be used by JavaScript Ocaml code. Parts based in
   the coq source code.

   By Emilio J. Gallego Arias, Mines ParisTech, Paris.
*)

(* open Errors *)
(* open Pcoq *)

open Feedback
open Names
open Pp
open Util

(* Init options for coq *)
type init_opts = {

  (* callback to load cma/cmo files *)
  ml_load    : string -> unit;

  (* callback to handle async feedback *)
  fb_handler : feedback -> unit;

}

let gdoc : Stm.doc ref = ref (Obj.magic 0)

(* The order of some of the steps is not 100% guaranteed to be correct
   for now... *)
let init opts =

  (* We may hook library loading to avoid dynamic bytecode-to-js
   * compilation.
   *)
  let open Mltop in
  let jstop : Mltop.toplevel = {
    load_obj = opts.ml_load;
    (* We ignore all the other operations for now *)
    use_file = (fun s  -> Printf.eprintf "[jstop] use_file \"%s\" called\n%!" s);
    add_dir  = (fun _s -> ());
               (* Printf.eprintf "[jstop] add_dir \"%s\" called\n%!" s); *)
    ml_loop  = (fun () -> Printf.eprintf "[jstop] ml_loop not supported\n%!");
  } in

  Mltop.set_top jstop;

  (* Internal Coq initialization *)
  (* Lib.init (); *)

  Global.set_engagement Declarations.PredicativeSet;

  (* Local libraries: *)
  let iload_path = Mltop.[{
      path_spec = VoPath { unix_path = ".";
                           coq_path = Libnames.default_root_prefix;
                           implicit = false;
                           has_ml = AddNoML;
                         };
      recursive = false;
    }] in
  ignore(Feedback.add_feeder opts.fb_handler);

  (* Initialize the STM. *)
  Stm.init_core ();

  (* We need to define a toplevel module name. *)
  let jscoq_dp = DirPath.make [Id.of_string "JsTop"] in

  (* System's directory cache is CRAP *)
  System.trust_file_cache := false;

  (* Return the initial state of the STM *)
  let ndoc = { Stm.doc_type = Stm.Interactive jscoq_dp; require_libs = [];
               iload_path; stm_options = Stm.AsyncOpts.default_opts } in
  let ndoc, nsid = Stm.new_doc ndoc in
  gdoc := ndoc;
  nsid

let version =
  Coq_config.version, Coq_config.date, Coq_config.compile_date, Coq_config.caml_version

(* Add a load path *)
let add_load_path pkg pkg_path has_ml =
  let coq_path = DirPath.make @@ List.rev @@ List.map Id.of_string pkg in
  Loadpath.add_load_path ("./" ^ pkg_path) coq_path ~implicit:false;
  if has_ml then Mltop.(add_coq_path { path_spec = MlPath pkg_path; recursive = false; })

let add_to_doc sid s =
  let pa = Pcoq.Gram.parsable (Stream.of_string s) in
  let doc = !gdoc in
  let ast = Stm.parse_sentence ~doc sid pa in
  let ndoc, nsid, _ = Stm.add ~doc ~ontop:sid false ast in
  gdoc := ndoc;
  nsid

let edit_doc   sid   =
  let doc = !gdoc in
  let ndoc, _ = Stm.edit_at ~doc sid in
  gdoc := ndoc;
  ()

let commit_doc sid =
  let doc = !gdoc in
  let ndoc = Stm.observe ~doc sid in
  gdoc := ndoc;
  ()

let query sid cmd =
  let pa = Pcoq.Gram.parsable (Stream.of_string cmd) in
  let doc = !gdoc in
  Stm.query ~doc ~route:0 ~at:sid pa

let string_of_goals () =
  let pp_goals =
    try
      let proof = Proof_global.give_me_the_proof () in
      Printer.pr_open_subgoals ~proof
    with Proof_global.NoCurrentProof -> str ""
  in
  string_of_ppcmds pp_goals

(** [set_debug t] enables/disables debug mode  *)
let set_debug debug =
  Backtrace.record_backtrace debug;
  Flags.debug := debug

module Options : sig
  type 'a t

  (* Printing depth *)
  val print_width  : int  t

  (** [set_bool_option opt val] Sets bool option to val. *)
  val set_bool_option : bool t -> bool -> unit

  (** [set_int_option opt val] Sets integer option to val. *)
  val set_int_option : int t -> int -> unit

end = struct

  open Goptions

  type 'a t = option_name

  let print_width  = ["Printing"; "Width"]

  (** [set_bool_option opt v] Sets bool option [opt] to [v] globally. *)
  let set_bool_option opt v =
    match opt with
    | _ ->
      Goptions.set_bool_option_value_gen opt v

  (** [set_int_option opt v] Sets integer optiont [opt] to [v] globally. *)
  let set_int_option opt v =
    Goptions.set_int_option_value_gen opt (Some v)

end
