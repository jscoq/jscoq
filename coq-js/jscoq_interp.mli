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
val post_message : (Yojson.Safe.t -> unit) ref
val post_file : (string -> string -> string -> unit) ref
val interrupt_setup : (Js_of_ocaml.Typed_array.int32Array Js_of_ocaml.Js.t -> unit) ref

(** Main execution point *)
val jscoq_execute
    : Jscoq_doc.ser_doc ref
    -> Jscoq_proto.Proto.jscoq_cmd
    -> unit

(** utility *)
val coq_exn_info : exn -> Jscoq_proto.Proto.jscoq_answer
