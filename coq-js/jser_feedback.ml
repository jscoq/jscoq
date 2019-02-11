(* Coq JavaScript API. Based in the coq source code and js_of_ocaml.
 *
 * Copyright (C) 2016-2017 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * LICENSE: GPLv3+
 *
 *)

module Xml_datatype = struct

  type 'a gxml =
    [%import: 'a Xml_datatype.gxml
    ]
  [@@deriving yojson]

  type xml =
    [%import: Xml_datatype.xml
    [@with
      Xml_datatype.gxml := gxml;
    ]]
    [@@deriving yojson]

end

module Pp = struct

type pp_tag =
  [%import: Pp.pp_tag]
  [@@deriving yojson]

type block_type =
  [%import: Pp.block_type]
  [@@deriving yojson]

module P = struct
  type _doc_view =
  | Pp_empty
  | Pp_string of string
  | Pp_glue of _doc_view list
  | Pp_box  of block_type * _doc_view
  | Pp_tag  of pp_tag * _doc_view
  (* Are those redundant? *)
  | Pp_print_break of int * int
  | Pp_force_newline
  | Pp_comment of string list
  [@@deriving yojson]

  open Pp

  let rec from_t (d : t) : _doc_view = match repr d with
  | Ppcmd_empty -> Pp_empty
  | Ppcmd_string s -> Pp_string s
  | Ppcmd_glue l -> Pp_glue (List.map from_t l)
  | Ppcmd_box (bt,d) -> Pp_box(bt, from_t d)
  | Ppcmd_tag (t,d) -> Pp_tag(t, from_t d)
  | Ppcmd_print_break (n,m) -> Pp_print_break(n,m)
  | Ppcmd_force_newline -> Pp_force_newline
  | Ppcmd_comment s -> Pp_comment s

  let rec to_t (d : _doc_view) : t = unrepr (match d with
  | Pp_empty -> Ppcmd_empty
  | Pp_string s -> Ppcmd_string s
  | Pp_glue l -> Ppcmd_glue (List.map to_t l)
  | Pp_box (bt,d) -> Ppcmd_box(bt, to_t d)
  | Pp_tag (t,d) -> Ppcmd_tag(t, to_t d)
  | Pp_print_break (n,m) -> Ppcmd_print_break(n,m)
  | Pp_force_newline -> Ppcmd_force_newline
  | Pp_comment s -> Ppcmd_comment s)

end

type t = Pp.t
type std_ppcmds = t
let of_yojson json =
  let open Result in
  match P._doc_view_of_yojson json with
    | Ok id   -> Ok (P.to_t id)
    | Error s -> Error s

let to_yojson d = P.(_doc_view_to_yojson (from_t d))

let std_ppcmds_of_yojson = of_yojson
let std_ppcmds_to_yojson = to_yojson

(* XXX *)
let str = Pp.str
let rec opt (d : Pp.t) = let open Pp in
  let rec flatten_glue l = match l with
    | []  -> []
    | (Ppcmd_glue g :: l) -> flatten_glue (List.map repr g @ flatten_glue l)
    | (Ppcmd_string s1 :: Ppcmd_string s2 :: l) -> flatten_glue (Ppcmd_string (s1 ^ s2) :: flatten_glue l)
    | (x :: l) -> x :: flatten_glue l
  in
  unrepr (match repr d with
      | Ppcmd_glue []   -> Ppcmd_empty
      | Ppcmd_glue [x]  -> repr (opt x)
      | Ppcmd_glue l    -> Ppcmd_glue List.(map opt (map unrepr (flatten_glue (map repr l))))
      | Ppcmd_box(bt,d) -> Ppcmd_box(bt, opt d)
      | Ppcmd_tag(t, d) -> Ppcmd_tag(t,  opt d)
      | d -> d
    )
  [@@warning "-4"]

end

module Loc = struct

  include Loc

  type _source =
    [%import: Loc.source]
    [@@deriving yojson]
    [@@ocaml.warning "-39"]

  let source_of_yojson = _source_of_yojson
  let source_to_yojson = _source_to_yojson

  type _t =
    [%import: Loc.t]
    [@@deriving yojson]
    [@@ocaml.warning "-39"]

  let of_yojson = _t_of_yojson
  let to_yojson = _t_to_yojson

end

module Stateid = struct

  include Stateid

  type _stateid = int
  [@@deriving yojson]
  [@@ocaml.warning "-39"]

  let of_yojson json =
    let open Result in
    match _stateid_of_yojson json with
    | Ok id   -> Ok (Stateid.of_int id)
    | Error s -> Error s

  let to_yojson sid  = _stateid_to_yojson (Stateid.to_int sid)

end

type state_id = Stateid.t
  [@@deriving yojson]

module Feedback = struct
  type level =
    [%import: Feedback.level]
    [@@deriving yojson]
    [@@ocaml.warning "-39"]

  type route_id =
    [%import: Feedback.route_id]
    [@@deriving yojson]

  type doc_id =
    [%import: Feedback.doc_id]
    [@@deriving yojson]

  type feedback_content =
    [%import: Feedback.feedback_content]
    [@@deriving yojson]

  type feedback =
    [%import: Feedback.feedback
    [@with
      Feedback.route_id := route_id;
    ]]
    [@@deriving yojson]

end
