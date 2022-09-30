(* Coq JavaScript API.
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2021 Shachar Itzhaky, Technion
 * Copyright (C) 2019-2021 Emilio J. Gallego Arias, INRIA
 * LICENSE: GPLv3+
 *
 * Interpreter for the Coq communication protocol
 *)

(** XXX: Functorialize *)
module Callbacks : sig

  type t =
    { post_message : (Yojson.Safe.t -> unit)
    ; post_file : (string -> string -> string -> unit)
    ; interrupt_setup : (Jscoq_proto.Proto.opaque -> unit)
    ; system_version : string
    ; create_file : name:string -> content:string -> unit
    ; update_file : name:string -> content:string-> unit
    }

  val set : t -> unit

end

(** Main execution point *)
val jscoq_execute
    : Jscoq_doc.ser_doc ref
    -> Jscoq_proto.Proto.jscoq_cmd
    -> unit

(** utility *)
val coq_exn_info : exn -> Jscoq_proto.Proto.jscoq_answer
