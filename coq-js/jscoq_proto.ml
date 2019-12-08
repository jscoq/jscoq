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
  [%import: 'a Serapi_goals.hyp]
  [@@deriving to_yojson]

type info =
  [%import: Serapi_goals.info]
  [@@deriving to_yojson]

type 'a reified_goal =
  [%import: 'a Serapi_goals.reified_goal]
  [@@deriving to_yojson]

type 'a ser_goals =
  [%import: 'a Serapi_goals.ser_goals]
  [@@deriving to_yojson]

module Proto = struct

type coq_options = (string list * Goptions.option_value) list [@@deriving yojson]

type jscoq_options =
  { top_name: string      [@default "JsCoq"]
  ; implicit_libs: bool   [@default true]
  ; stm_debug: bool       [@default false]
  ; coq_options: coq_options [@default []]
  }
  [@@deriving yojson]

type search_query =
  | All
  | CurrentFile
  | ModulePrefix of Serlib.Ser_names.DirPath.t
  | Keyword of string
  | Locals
  [@@deriving yojson]

type opaque = Js_of_ocaml.Js.Unsafe.any
let opaque_to_yojson x = `Null
let opaque_of_yojson x = Result.Error "opaque value"

(* Main RPC calls *)
type jscoq_cmd =
  | InfoPkg of string * string list
  | LoadPkg of string * string

  (*           opts            initial_imports      load paths                      *)
  | Init    of jscoq_options * string list list   * (string list * string list) list

  (*           ontop       new         sentence                *)
  | Add     of Stateid.t * Stateid.t * string * bool
  | Cancel  of Stateid.t
  | Exec    of Stateid.t

  | Goals   of Stateid.t
  | Query   of Stateid.t * Feedback.route_id * string
  | Inspect of Stateid.t * Feedback.route_id * search_query
  | Ast     of Stateid.t

  (*            filename content *)
  | Register of string
  | Put      of string * string

  (* XXX: Not well founded... *)
  | GetOpt  of string list

  | InterruptSetup of opaque

  | ReassureLoadPath of (string list * string list) list
  | Load    of string
  | Compile of string
  [@@deriving yojson]

type jscoq_answer =
  | CoqInfo   of string

  | Ready     of Stateid.t

  (* Merely Informative now *)
  | Added     of Stateid.t * Loc.t option

  (* Requires pkg(s)         prefix        module names    *)
  | Pending   of Stateid.t * string list * string list list

  (* Main feedback *)
  | Cancelled of Stateid.t list

  (* Goals must be printed better *)
  | GoalInfo  of Stateid.t * Pp.t reified_goal ser_goals option

  | Ast       of Vernacexpr.vernac_control option
  | CoqOpt    of string list * Goptions.option_value
  | Log       of Feedback.level * Pp.t
  | Feedback  of Feedback.feedback

  | SearchResults of Feedback.route_id * Libnames.full_path Seq.t

  (* Low-level *)
  | CoqExn    of Loc.t option * (Stateid.t * Stateid.t) option * Pp.t
  | JsonExn   of string
  [@@deriving to_yojson]
end
