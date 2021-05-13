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

let mk_message (range, level, text) = Lsp.JFleche.Message.{ range; level; text }

let mk_messages node =
  Option.map Fleche.Doc.Node.messages node
  |> Option.cata (List.map mk_message) []

let mk_error node =
  let open Fleche in
  let open Lang in
  match
    List.filter (fun d -> d.Diagnostic.severity < 2) node.Doc.Node.diags
  with
  | [] -> None
  | e :: _ -> Some e.Diagnostic.message

let do_request ~doc point (r : Method.t) =
  match r with
  | Method.Mode -> Answer.Void
  (* Fix this to use lsp *)
  | Method.Goals _pp ->
    let uri, version = doc.Fleche.Doc.uri, doc.version in
    let textDocument = Lsp.Doc.VersionedTextDocumentIdentifier.{ uri; version } in
    let position = Lang.Point.{ line = -1; character = -1; offset = point } in
    let goals_mode = LI.Prev in
    let goals = LI.O.goals ~doc ~point goals_mode in
    let program = LI.O.program ~doc ~point goals_mode in
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

(* to put in Flèche
let _pp_of_goals =
   let ppx env sigma x = Jscoq_util.pp_opt (Printer.pr_ltype_env env sigma x) in
   Serapi.Serapi_goals.get_goals_gen ppx
 
+let set_flag flag value f =
+  let v = !flag in
+  flag := value;
+  try
+    let res = f () in
+    flag := v;
+    res
+  with exn ->
+    flag := v;
+    raise exn
+
+let layout_term env sigma t =
+  (* Coq stores goals in kernel-format, we need to recover the AST
+     back before calling the layout engine; this is called
+     "externalization" in Coq jargon *)
+  let t = Constrextern.extern_type env sigma (EConstr.of_constr t) in
+  let html = Tprinter.(Term.layout env sigma t |> BoxModel.Render.to_html) in
+  Format.asprintf "@[%a@]" (Tyxml.Html.pp_elt ()) html
+
+let layout_term env sigma t =
+  set_flag
+    (* Notations = no *)
+    (* Constrextern.print_no_symbol true *)
+    (* Notations = yes *)
+    Constrextern.print_no_symbol false
+    (fun () ->
+       layout_term env sigma t)
+
+let html_of_goals =
+  let ppx env sigma x = layout_term env sigma x in
+  Serapi.Serapi_goals.get_goals_gen ppx
*)
