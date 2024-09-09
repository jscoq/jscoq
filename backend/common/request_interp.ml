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

let mk_message (range, level, text) =
  let level = Lang.Diagnostic.Severity.to_int level in
  Lsp.JFleche.Message.{ range; level; text }

let mk_messages node =
  Option.map Fleche.Doc.Node.messages node
  |> Option.cata (List.map mk_message) []

let mk_error node =
  let open Fleche in
  let open Lang in
  match
    List.filter Lang.Diagnostic.is_error node.Doc.Node.diags
  with
  | [] -> None
  | e :: _ -> Some e.Diagnostic.message

let from_execution (res : _ Coq.Protect.E.t) =
  match res with
  | { r = Coq.Protect.R.Completed (Ok goals); feedback = _ } -> goals
  | { r = Coq.Protect.R.Completed (Error _); feedback = _ } -> None
  | { r = Coq.Protect.R.Interrupted; feedback = _ } -> None

let do_request ~token ~doc point (r : Method.t) =
  match r with
  | Method.Mode -> Answer.Void
  | Method.Goals ->
    let uri, version = doc.Fleche.Doc.uri, doc.version in
    let textDocument = Lsp.Doc.VersionedTextDocumentIdentifier.{ uri; version } in
    let position = Lang.Point.{ line = -1; character = -1; offset = point } in
    let goals_mode = LI.Prev in
    let goals =
      LI.O.node ~doc ~point goals_mode |> Option.map (fun (node : Fleche.Doc.Node.t) ->
          LI.Goals.goals ~token ~st:node.state) in
    let goals = Option.bind goals from_execution in
    let program =
      LI.O.node ~doc ~point goals_mode |> Option.map (fun (node : Fleche.Doc.Node.t) ->
          LI.Goals.program ~st:node.state) in
    let node = LI.O.node ~doc ~point Exact in
    let messages = mk_messages node in
    let error = Option.bind node mk_error in
    let goals = Lsp.JFleche.GoalsAnswer.{ textDocument; position; goals; program; messages; error } in
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
