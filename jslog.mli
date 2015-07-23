(* HTML log buffers
 *
 * Copyright (C) 2015 Mines ParisTech
 * Written by: Emilio J. Gallego Arias
 *
 * LICENSE: GPLv3+
 *)

(* HTML log buffers *)
type t

(* XXX: Add a filter js button to ignore events *)
type log_level =
  | Debug
  | Info
  | Warn
  | Error

val init       : Dom_html.element Js.t -> bool -> t
val init_by_id : string -> bool -> t

val add      : t -> log_level -> Dom_html.element Js.t -> unit
val add_text : t -> log_level -> string -> unit

val printf : t -> ('a, unit, string, unit) format4 -> 'a

val jscoq_log : t
