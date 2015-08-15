(* JsCoq toplevel, adapted from the Js_of_ocaml one
 * http://www.ocsigen.org/js_of_ocaml/
 * Copyright (C) 2011 Jérôme Vouillon
 * Laboratoire PPS - CNRS Université Paris Diderot
 *
 * Copyright (C) 2015 Emilio Gallego / Mines ParisTech
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, with linking exception;
 * either version 2.1 of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *)

open Lwt
open Js
open Dom

(* XXX: Global jsCoq object must be already initialized *)
(* XXX: Sad fact about sync *)

module Stateid = struct
  type t = int
end

module Jslog = struct

(* HTML log buffers *)
type t = {
  buffer : Dom_html.element Js.t;
  append : bool;
}
type log_level =
  | Debug
  | Info
  | Warn
  | Error

let init el app = {
  buffer = el;
  append = app;
}

let init_by_id id app =
  let b = Dom_html.getElementById id in
  init b app

let add lb ll el =
  if lb.append then (
    Dom.appendChild lb.buffer el;
    lb.buffer##scrollTop <- lb.buffer##scrollHeight
  ) else
    Dom.insertBefore lb.buffer el (lb.buffer##firstChild)

let text s =
  Tyxml_js.Html5.(span ~a:[a_class []] [pcdata s])

let add_text lb ll msg =
  add lb ll (Tyxml_js.To_dom.of_element (text msg))

let printf lb =
  Printf.ksprintf (add_text lb Info)

let jscoq_log : t =
  init_by_id "jscoq-log-area" false

end

class type jsCoq = object
  method init        : Stateid.t meth
  method add         : Stateid.t -> int -> js_string t -> Stateid.t meth
  method edit        : Stateid.t -> unit meth
  method commit      : Stateid.t -> unit meth
  method onLog       : ('self t, js_string t -> unit) meth_callback writeonly_prop
  method onError     : ('self t, Stateid.t   -> unit) meth_callback writeonly_prop
end

let jsCoq : #jsCoq Js.t = Js.Unsafe.global##jsCoq

let by_id s           = Dom_html.getElementById s
let by_id_coerce s f  = Js.Opt.get (f (Dom_html.getElementById s)) (fun () -> raise Not_found)
let do_by_id s f      = try f (Dom_html.getElementById s) with Not_found -> ()

let resize ~container ~textbox ()  =
  Lwt.pause () >>= fun () ->
  textbox##style##height <- Js.string "auto";
  textbox##style##height <- Js.string (Printf.sprintf "%dpx" (max 18 textbox##scrollHeight));
  container##scrollTop   <- container##scrollHeight;
  Lwt.return ()

let text s = Tyxml_js.Html5.(span ~a:[a_class []] [pcdata s])

let append output s  = Dom.appendChild output (Tyxml_js.To_dom.of_element (text s))
let current_position = ref 0

module History = struct
  let data = ref [|""|]
  let idx = ref 0
  let get_storage () =
    match Js.Optdef.to_option Dom_html.window##localStorage with
    | None -> raise Not_found
    | Some t -> t

  let setup () =
    try
      let s = get_storage () in
      match Js.Opt.to_option (s##getItem(Js.string "history")) with
      | None -> raise Not_found
      | Some s -> let a = Json.unsafe_input s in
		  data:=a; idx:=Array.length a - 1
    with _ -> ()

  let push text =
    let l = Array.length !data in
    let n = Array.make (l + 1) "" in
    Array.set  !data (l - 1) text;
    Array.blit !data 0 n 0 l;
    data := n; idx := l;
    try
      let s = get_storage () in
      let str = Json.output !data in
      s##setItem(Js.string "history", str)
    with Not_found -> ()

  let current text = !data.(!idx) <- text

  let previous textbox =
    if !idx > 0
    then begin decr idx; textbox##value <- Js.string (!data.(!idx)) end

  let next textbox =
    if !idx < Array.length !data - 1
    then begin incr idx; textbox##value <- Js.string (!data.(!idx)) end
end

let run _ =
  let csid = ref 0                           in
  let osid = ref 0                           in
  let eid  = ref (-1)                        in
  let container = by_id "toplevel-container" in
  let output    = by_id "output" in
  let textbox : 'a Js.t = by_id_coerce "userinput" Dom_html.CoerceTo.textarea in

  let execute () =
    let execute_com content =
      current_position := output##childNodes##length;
      append output ("# " ^ content ^ "\n");
      History.push content;
      Jslog.printf Jslog.jscoq_log "sending to %d\n" !csid;
      osid := !csid; decr eid;
      csid := jsCoq##add(!csid, !eid, string content);
      jsCoq##commit(!csid);
      resize ~container ~textbox ()                                     >>= fun () ->
      container##scrollTop <- container##scrollHeight;
      textbox##focus();
      Lwt.return_unit
    in
    (* Split by dots with hack *)
    let input = (Js.to_string (textbox##value##trim())) ^ " "           in
    let commands = Regexp.split (Regexp.regexp "\\.\\s+") input         in
    let commands = List.filter (fun s -> String.length s <> 0) commands in
    (* Other Hack: re-add dots *)
    let commands = List.map (fun s -> s ^ ".") commands                 in
    textbox##value <- Js.string "";
    Lwt_list.iter_s execute_com commands
  in

  let history_down e =
    let txt = Js.to_string textbox##value in
    let pos = (Obj.magic textbox)##selectionStart in
    try
      (if String.length txt = pos  then raise Not_found);
      let _ = String.index_from txt pos '\n' in
      Js._true
    with Not_found ->
      History.current txt;
      History.next textbox;
      Js._false
  in
  let history_up   e =
    let txt = Js.to_string textbox##value in
    let pos = (Obj.magic textbox)##selectionStart - 1  in
    try
      (if pos < 0  then raise Not_found);
      let _ = String.rindex_from txt pos '\n' in
      Js._true
    with Not_found ->
      History.current txt;
      History.previous textbox;
      Js._false
  in

  let meta e =
    let b = Js.to_bool in
    b e##ctrlKey || b e##shiftKey || b e##altKey || b e##metaKey in

  let setup_printers () =
    let open Jslog  in
    let proof_msg   = init_by_id "goal-info-area"  true in
    let query_msg   = init_by_id "query-info-area" true in
    (* How to create a channel *)
    (* let _sharp_chan = open_out "/dev/null0" in *)
    (* let _sharp_ppf = Format.formatter_of_out_channel _sharp_chan in *)
    Sys_js.set_channel_flusher stdout (add_text proof_msg Info);
    Sys_js.set_channel_flusher stderr (add_text query_msg Info)
  in

  begin (* setup handlers *)
    textbox##onkeyup   <- Dom_html.handler (fun _ -> Lwt.async (resize ~container ~textbox); Js._true);
    textbox##onchange  <- Dom_html.handler (fun _ -> Lwt.async (resize ~container ~textbox); Js._true);
    textbox##onkeydown <- Dom_html.handler (fun e ->
        match e##keyCode with
        | 13 when not (meta e) -> Lwt.async execute; Js._false
        | 13 -> Lwt.async (resize ~container ~textbox); Js._true
        (* | 76 when meta e -> output##innerHTML <- Js.string ""; Js._true *)
        (* | 75 when meta e -> setup_toplevel (); Js._false *)
        | 38 -> history_up e
        | 40 -> history_down e
        | _ -> Js._true
      );
  end;

  (* Add exception handler *)
  Lwt.async_exception_hook:=(fun exc ->
    Format.eprintf "exc during Lwt.async: %s@." (Printexc.to_string exc);
    match exc with
    | Js.Error e -> Firebug.console##log(e##stack)
    | _ -> ());

  (* Focus on the input box *)
  Lwt.async (fun () ->
    resize ~container ~textbox () >>= fun () ->
    textbox##focus ();
    Lwt.return_unit);

  setup_printers  ();
  History.setup   ();
  jsCoq##onLog   <- Js.wrap_callback
                    (function s -> Jslog.printf Jslog.jscoq_log "log %s!" (Js.to_string s));
  jsCoq##onError <- Js.wrap_callback
                      (function se ->
                                Jslog.printf Jslog.jscoq_log "error on se %d, setting from %d to %d!" se !csid !osid;
                                csid := !osid;
                                jsCoq##edit(!csid)
                      );
  csid := jsCoq##init ();
  jsCoq##commit(!csid);

  (* Setup an initial value. *)
  Lwt.async (fun () ->
    textbox##value <- Js.string "Require Import Coq.Init.Prelude.";
    Lwt.return_unit);
  ()

let _ = Dom_html.window##onload <- Dom_html.handler (fun _ -> run (); Js._false)
