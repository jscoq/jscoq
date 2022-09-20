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

type 'a hyp =
  [%import: 'a Serapi.Serapi_goals.hyp]
  [@@deriving to_yojson]

type info =
  [%import: Serapi.Serapi_goals.info]
  [@@deriving to_yojson]

type 'a reified_goal =
  [%import: 'a Serapi.Serapi_goals.reified_goal]
  [@@deriving to_yojson]

type 'a ser_goals =
  [%import: 'a Serapi.Serapi_goals.ser_goals]
  [@@deriving to_yojson]

module Proto = struct

module Point = struct

  type t = [%import: Lsp.Base.Point.t]
  [@@deriving yojson]

end

module Range = struct
  type t = [%import: Lsp.Base.Range.t]
  [@@deriving yojson]
end
type diagnostic =
  [%import: Lsp.Base.Diagnostic.t]
  [@@deriving yojson]

type coq_options = (string list * Goptions.option_value) list [@@deriving yojson]
type lib_path = (string list * string list) list [@@deriving yojson]
type debug_config =
  { coq: bool                    [@default false]
  ; stm: bool                    [@default false]
  }
  [@@deriving yojson]

type jscoq_options =
  { implicit_libs: bool          [@default true]
  ; coq_options: coq_options     [@default []]  (* @todo this has to be set during init in 8.13 and older; in 8.14, move to doc_options *)
  ; debug: debug_config          [@default {coq=false; stm=false}]
  ; lib_path: lib_path           [@default []]
  }
  [@@deriving yojson]

type doc_options =
  { top_name: string             [@default "JsCoq"]
  ; lib_init: string list        [@default ["Coq.Init.Prelude"]]
  }
  [@@deriving yojson]

type search_query =
  [%import: Code_info.Query.t]
  [@@deriving yojson]

type query =
  | Mode
  | Goals
  | Vernac of string
  | Inspect of search_query
  [@@deriving yojson]

type opaque
let opaque_to_yojson _x = `Null
let opaque_of_yojson _x = Result.Error "opaque value"

(* Main RPC calls *)
type jscoq_cmd =
  | Init    of jscoq_options
  | NewDoc  of doc_options * string * bool
  | Update  of string * int

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
  | Notification of diagnostic list * int
  | Log       of Feedback.level * Pp.t
  | JsonExn   of string
  [@@deriving to_yojson]
end
