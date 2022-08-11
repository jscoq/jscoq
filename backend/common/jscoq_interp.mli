(* Coq JavaScript API.
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2021 Shachar Itzhaky, Technion
 * Copyright (C) 2019-2021 Emilio J. Gallego Arias, INRIA
 * LICENSE: GPLv3+
 *
 * Interpreter for the Coq communication protocol
 *)

module Callbacks : sig

  open Jslib.LibManager

  type t =
    { pre_init : unit -> unit
    ; post_message : (Yojson.Safe.t -> unit)
    ; post_file : (string -> string -> string -> unit)
    ; interrupt_setup : (Jscoq_proto.Proto.opaque -> unit)
    ; branding : string
    ; subsystem_version : string
    ; read_file : name:string -> string
    ; write_file : name:string -> content:string-> unit
    ; register_cma : file_path:string -> unit
    ; load_pkg : base_path:string -> pkg:string -> cb:(lib_event -> unit) -> unit
    ; info_pkg : base_path:string -> pkgs:string list -> cb:(lib_event -> unit) -> unit
    }

  val set : t -> unit

end

(** Main execution point *)
val jscoq_execute
  : Jscoq_proto.Proto.jscoq_cmd
  -> unit
