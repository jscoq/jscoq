(* Coq JavaScript API. Based in the coq source code and js_of_ocaml.
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2019 Shachar Itzhaky, Technion, Haifa.
 * LICENSE: GPLv3+
 *
 *)

module Stateid  = Serlib.Ser_stateid
module Loc      = Serlib.Ser_loc
module Pp       = Serlib.Ser_pp
module Feedback = Serlib.Ser_feedback
module Names    = Serlib.Ser_names
module Evar     = Serlib.Ser_evar
module Goptions = Serlib.Ser_goptions
module Libnames = Serlib.Ser_libnames
module Vernacexpr = Serlib.Ser_vernacexpr

module Seq = struct
  type 'a t = 'a Seq.t
  let to_yojson f s = `List (Seq.fold_left (fun l x -> f x :: l) [] s |> List.rev)
end

(* XXX: This is already done in coq-lsp lsp library *)
type 'a hyp =
  [%import: 'a Coq.Goals.Reified_goal.hyp]
  [@@deriving to_yojson]

type info =
  [%import: Coq.Goals.Reified_goal.info]
  [@@deriving to_yojson]

type 'a reified_goal =
  [%import: 'a Coq.Goals.Reified_goal.t]
  [@@deriving to_yojson]

type ('a, 'pp) goals =
  [%import: ('a, 'pp) Coq.Goals.t]
  [@@deriving to_yojson]

module Proto = struct

module Lang = struct
module Point = struct
  type t = [%import: Lang.Point.t]
  [@@deriving yojson]
end

module Range = struct
  type t = [%import: Lang.Range.t [@with Lang.Point.t := Point.t]]
  [@@deriving yojson]
end

module LUri = struct
  type _kv = (string * string list) list

  type _query =
    | KV of _kv
    | Raw of string option * _kv Lazy.t

  type _t = {
    scheme: string option;
    userinfo: (string * string option) option;
    host: string option;
    port: int option;
    path: string list;
    query: _query;
    fragment: string option
  }

  module File = struct
    type t = Lang.LUri.File.t

    type nonrec _t =
      { uri : _t
      ; file : string
      }

    (* let to_yojson uri = `String (Lang.LUri.File.to_string_uri uri) *)
    let to_yojson uri = `String ("file://"^(Obj.magic uri).file)
    let invalid_uri msg obj = raise (Yojson.Safe.Util.Type_error (msg, obj))

    let of_yojson uri =
      match uri with
      | `String uri as _obj -> (
          let fl = String.length "file:///" - 1 in
          let file = String.(sub uri fl (length uri - fl)) in
          let uri = { scheme = None
                    ; userinfo = None;
                      host = None;
                      port = None;
                      path = [];
                      query = KV [];
                      fragment = None }
          in
          Ok (Obj.magic { uri; file }))
        (* let uri = Lang.LUri.of_string uri in *)
        (* match Lang.LUri.File.of_uri uri with *)
        (* | Result.Ok t -> Result.Ok t *)
        (* | Result.Error msg -> invalid_uri ("failed to parse uri: " ^ msg) obj) *)
      | obj -> invalid_uri "expected uri string, got json object" obj
  end
end

module Qf = struct
  type 'a t =  [%import: 'a Lang.Qf.t]
      [@@deriving yojson]
end

module Diagnostic = struct

  module FailedRequire = struct
    type t = [%import: Lang.Diagnostic.FailedRequire.t]
      [@@deriving yojson]
  end

  module Data = struct
    type t =
      [%import: Lang.Diagnostic.Data.t [@with Lang.Range.t := Range.t; Lang.Diagnostic.FailedRequire.t := FailedRequire.t; Lang.Qf.t := Qf.t] ]
      [@@deriving yojson]
  end

  module Severity = struct
    type t = [%import: Lang.Diagnostic.Severity.t]
      [@@deriving yojson]
  end

  type t =
    [%import: Lang.Diagnostic.t [@with Lang.Range.t := Range.t; Lang.Diagnostic.Data.t := Data.t; Lang.Diagnostic.Severity.t := Serverity.t]]
    [@@deriving yojson]

  let is_error = Lang.Diagnostic.is_error
end
end

type coq_options = (string list * Goptions.option_value) list [@@deriving yojson]
type lib_path = (string list * string list) list [@@deriving yojson]

type init_options =
  { implicit_libs: bool          [@default true]
  ; coq_options: coq_options     [@default []]
  (* @todo allow to be set in NewDoc too *)
  ; debug: bool                  [@default false]
  ; lib_path: lib_path           [@default []]
  ; lib_init: string list        [@default ["Coq.Init.Prelude"]]
  } [@@deriving yojson]

type search_query =
  [%import: Code_info.Query.t]
  [@@deriving yojson]

module Method = struct

  type t =
    | Mode
    | Goals
    | Search of string
    | TypeAtPoint
    | TypeOfId of string
    | Inspect of search_query
    | Completion of string
  [@@deriving yojson]

end

module Answer = struct

  type t =
  | Goals of Pp.t Lsp.JFleche.GoalsAnswer.t
  | Completion of string list
  | Void
  [@@deriving to_yojson]

end

type opaque
let opaque_to_yojson _x = `Null
let opaque_of_yojson _x = Result.Error "opaque value"

module Request = struct

  type 'a t =
    { uri : Lang.LUri.File.t
    ; loc : int
    (* In fact, we should use Lsp.Base.point instead of int for
       location, however ProseMirror and CM6 use offsets *)
    ; v : 'a
    }
  [@@deriving yojson]

  let make ~uri ~loc v = { uri; loc; v }

  type 'a answer =
    { id : int
    ; res : 'a
    }
  [@@deriving yojson]

  let process { uri; loc; v } ~f =
    f uri loc v

end

(* Main RPC calls *)
type jscoq_cmd =
  | Init    of init_options
  | NewDoc  of { uri : Lang.LUri.File.t; version : int; raw : string }
  | Update  of { uri : Lang.LUri.File.t; version : int; raw : string }

  | Request of { id: int; method_ : Method.t Request.t [@key "method"] }

  | InfoPkg of string * string list
  | LoadPkg of string * string

  (*            filename content *)
  | Register of string
  | Put      of string * string
  | InterruptSetup of opaque
  [@@deriving yojson]

type jscoq_answer =
  | CoqInfo   of string
  | Ready     of unit
  | Notification of { uri: Lang.LUri.File.t; version: int; diagnostic: Lang.Diagnostic.t list }
  (** LSP-compatible payload for diagnostics *)
  | Response  of Answer.t Request.answer
  | Log       of Feedback.level * Pp.t
  | JsonExn   of string
  [@@deriving to_yojson]
end
