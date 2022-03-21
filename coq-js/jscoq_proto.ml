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

type top_mode =
  [%import: Icoq.top_mode]
  [@@deriving yojson]

type doc_options =
  { top_name: string             [@default "JsCoq"]
  ; lib_init: string list        [@default ["Coq.Init.Prelude"]]
  ; mode: top_mode               [@default Interactive]
  }
  [@@deriving yojson]

type in_mode = Icoq.in_mode
let in_mode_to_yojson = function Icoq.Proof -> `String "Proof" | General -> `Null

type qualified_object_prefix =
  [%import: Icoq.qualified_object_prefix](** List of new identifiers added to the context for each new goal *)
  [@@deriving yojson]
type qualified_name =
  [%import: Icoq.qualified_name]
  [@@deriving yojson]

type search_query =
  | All
  | CurrentFile
  | ModulePrefix of Serlib.Ser_names.DirPath.t
  | Keyword of string
  | Locals
  [@@deriving yojson]

type query =
  | Mode
  | Goals
  | Vernac of string
  | Inspect of search_query
  [@@deriving yojson]

type opaque = Js_of_ocaml.Js.Unsafe.any
let opaque_to_yojson _x = `Null
let opaque_of_yojson _x = Result.Error "opaque value"

(* Main RPC calls *)
type jscoq_cmd =
  | InfoPkg of string * string list
  | LoadPkg of string * string

  | Init    of jscoq_options
  | NewDoc  of doc_options

  (*           ontop       new         sentence                *)
  | Add     of Stateid.t * Stateid.t * string * bool
  | Cancel  of Stateid.t
  | Exec    of Stateid.t

  | Query   of Stateid.t * Feedback.route_id * query
  | Ast     of Stateid.t

  | TacticInfo of Stateid.t * string
  (** "Speculatively" execute a tactic and return information about how the goal changed *)

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

  (* Query responses *)
  | ModeInfo  of Stateid.t * in_mode
  | GoalInfo  of Stateid.t * Pp.t reified_goal ser_goals option

  | Ast       of Vernacexpr.vernac_control option
  | CoqOpt    of string list * Goptions.option_value
  | Log       of Feedback.level * Pp.t
  | Feedback  of Feedback.feedback

  | TacticInfo of Names.Id.t list list
  (** List of new identifiers added to the context for each new goal *)

  | SearchResults of Feedback.route_id * qualified_name Seq.t

  | Loaded    of string * Stateid.t
  | Compiled  of string

  (* Low-level *)
  | CoqExn    of { loc : Loc.t option
                 ; sid : (Stateid.t * Stateid.t) option
                 ; msg : string
                 ; pp : Pp.t
                 }
  | JsonExn   of string
  [@@deriving to_yojson]
end
