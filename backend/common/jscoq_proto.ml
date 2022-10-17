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
  [%import: 'a Coq.Goals.hyp]
  [@@deriving to_yojson]

type info =
  [%import: Coq.Goals.info]
  [@@deriving to_yojson]

type 'a reified_goal =
  [%import: 'a Coq.Goals.reified_goal]
  [@@deriving to_yojson]

type 'a goals =
  [%import: 'a Coq.Goals.goals]
  [@@deriving to_yojson]

module Proto = struct

module Point = struct
  type t = [%import: Fleche.Types.Point.t]
  [@@deriving yojson]
end

module Range = struct
  type t = [%import: Fleche.Types.Range.t]
  [@@deriving yojson]
end

module Diagnostic = struct

  module Extra = struct
    type t =
      [%import: Fleche.Types.Diagnostic.Extra.t]
      [@@deriving yojson]
  end

  type t =
    [%import: Fleche.Types.Diagnostic.t
    [@with range := range;]]
    [@@deriving yojson]

end

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
  | Goals of Pp.t reified_goal goals option
  | Completion of string list
  | Void
  [@@deriving to_yojson]

end

type opaque
let opaque_to_yojson _x = `Null
let opaque_of_yojson _x = Result.Error "opaque value"

module Request = struct

  type 'a t =
    { id : int
    ; loc : int
    (* In fact, we should use Lsp.Base.point instead of int for
       location, however ProseMirror and CM6 use offsets *)
    ; v : 'a
    }
  [@@deriving yojson]

  let make ~id ~loc v = { id; loc; v }

  type 'a answer =
    { id : int
    ; res : 'a
    }
  [@@deriving yojson]

  let process { id; loc; v } ~f =
    { id; res = f loc v }

end

(* Main RPC calls *)
type jscoq_cmd =
  | Init    of jscoq_options
  | NewDoc  of doc_options * string
  | Update  of string * int

  | Request of Method.t Request.t

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
  | Notification of Diagnostic.t list * int
  | Response  of Answer.t Request.answer
  | Log       of Feedback.level * Pp.t
  | JsonExn   of string
  [@@deriving to_yojson]
end
