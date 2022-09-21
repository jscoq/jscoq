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

let do_request ~doc point (r : Method.t) =
  match r with
  | Method.Mode -> Answer.Void
  | Method.Goals ->
    let approx = Controller.Lsp_interp.PickPrev in
    let goals = Controller.Lsp_interp.get_goals_point ~doc ~point ~approx in
    Answer.Goals goals
  | Method.Search _ -> Answer.Void
  | Method.TypeAtPoint -> Answer.Void
  | Method.TypeOfId _ -> Answer.Void
  | Method.Inspect _ -> Answer.Void
  | Method.Completion _ -> Answer.Void
