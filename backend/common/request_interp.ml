(* Coq JavaScript API.
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2022 Shachar Itzhaky, Technion
 * Copyright (C) 2019-2022 Emilio J. Gallego Arias, INRIA
 * LICENSE: GPLv3+
 *
 * Interpreter for the Coq communication protocol
 *)

(* Move to coq-lsp *)
open Jscoq_proto.Proto

module LI = Fleche.Info

(* XXX: This belongs in Coq *)
let pr_extref gr =
  match gr with
  | Globnames.TrueGlobal gr -> Printer.pr_global gr
  | Globnames.Abbrev kn -> Names.KerName.print kn

let do_request ~doc point (r : Method.t) =
  match r with
  | Method.Mode -> Answer.Void
  | Method.Goals ->
    let approx = LI.PickPrev in
    let goals = LI.O.goals ~doc ~point approx in
    Answer.Goals goals
  | Method.Search _ -> Answer.Void
  | Method.TypeAtPoint -> Answer.Void
  | Method.TypeOfId _ -> Answer.Void
  | Method.Inspect _ -> Answer.Void
  | Method.Completion prefix ->
    (* XXX Use LI.O.completion *)
    (* XXX This should set the proper state! For now it will run in
       the state resultin from checking the full document. *)
    let candidates = Nametab.completion_canditates (Libnames.qualid_of_string prefix) in
    Answer.Completion (List.map (fun x -> Pp.string_of_ppcmds (pr_extref x)) candidates)
