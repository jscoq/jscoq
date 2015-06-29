(* JsCoq toplevel, adapted from the Js_of_ocaml one
 * http://www.ocsigen.org/js_of_ocaml/
 * Copyright (C) 2011 Jérôme Vouillon
 * Laboratoire PPS - CNRS Université Paris Diderot
 *
 * Copyright (C) 2015 Emilio Gallego
 * Mines ParisTech
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

let by_id s = Dom_html.getElementById s
let by_id_coerce s f  = Js.Opt.get (f (Dom_html.getElementById s)) (fun () -> raise Not_found)
let do_by_id s f = try f (Dom_html.getElementById s) with Not_found -> ()

(* load file using a synchronous XMLHttpRequest *)
let load_resource_aux url =
  (* p @@ Printf.eprintf "load_resource_aux %s\n%!" (Js.to_string url); *)
  try
    let xml = XmlHttpRequest.create () in
    xml##_open(Js.string "GET", url, Js._false);
    xml##send(Js.null);
    (* Forbidden in sync requests:
       xml##responseType <- (Js.string "arraybuffer");
    *)
    (* Printf.eprintf "synchronous request sent, got status: %d\n%!" xml##status; *)
    (* File case *)
    if xml##status = 200 || xml##status = 0 then
      (* Convert to an arraybuffer *)
      begin
        let module JU = Js.Unsafe               in
        let r   = xml##responseText             in
        let rl  = r##length                     in
        (* Printf.eprintf "Length of the response: %d\n%!" rl; *)
        let bin_arr = Js.Unsafe.global##atob r  in
        let bl      = bin_arr##length           in
        (* Printf.eprintf "Length of the decoded string: %d\n%!" bl; *)
        let s = String.create bl in
        for i = 0 to bl - 1 do
          begin
            try
              (* [meth_call o m a] calls the Javascript method [m] of object [o] *)
              s.[i] <- Char.chr @@ JU.meth_call bin_arr "charCodeAt" [| JU.inject i|]
              (* s.[i] <- Char.chr @@ Js.Unsafe.bin_arr##charCodeAt i *)
            with
              _ -> Printf.eprintf "Wrong char %d at %d \n%!" (bin_arr##charCodeAt i) i;
          end
        done;
(*
        Printf.eprintf "Length of the CAML string: %d\n%!" (String.length s);
        Printf.eprintf "MD5: %s\n%!" (Digest.to_hex @@ Digest.string @@ s);
        Printf.eprintf "First: %!";
        for i = 0 to 11 do
          Printf.eprintf "%d%!" (int_of_char (String.get s i));
        done;
        Printf.eprintf "\n%!";
 *)
        Some (bin_arr)
        (* let b   = jsnew Typed_array.arrayBuffer(2*rl) in *)
        (* let b16 = jsnew Typed_array.int16Array_fromBuffer(b) in *)
        (* for i = 0 to rl - 1 do *)
        (*   Typed_array.set b16 i (int_of_float r##charCodeAt(i)) *)
        (* done; *)
        (* let s   = string_of_buffer b        in *)
        (* Printf.eprintf "MD5: %s\n%!" (Digest.to_hex @@ Digest.string @@ s); *)
        (* Some (xml##responseText) *)
      end
        (* let s = Js.to_bytestring xml##responseText in *)
        (* (Printf.eprintf "MD5: %s\n%!" (Digest.to_hex @@ Digest.string @@ s)); *)
        (* Some (xml##responseText) *)
    else
      None
      (* (Printf.eprintf "None?\n%!"; *)
      (*  None) *)
  with exc ->
    None
    (* (Format.eprintf "exc during load resource: %s\n%!" (Printexc.to_string exc); *)
    (*  None) *)

let load_resource scheme (_,suffix) =
  let url = (Js.string scheme)##concat(suffix) in
  load_resource_aux url

let setup_pseudo_fs () =
  Sys_js.register_autoload' "/dev/"   (fun s -> Some (Js.string ""));
  Sys_js.register_autoload' "/http/"  (fun s -> load_resource "http://" s);
  Sys_js.register_autoload' "/https/" (fun s -> load_resource "https://" s);
  Sys_js.register_autoload' "/ftp/"   (fun s -> load_resource "ftp://" s);
  Sys_js.register_autoload' "/"       (fun (_,s) -> load_resource_aux ((Js.string "filesys/")##concat(s)))

(* let exec' s = *)
(*   let res : bool = JsooTop.use Format.std_formatter s in *)
(*   if not res then Format.eprintf "error while evaluating %s@." s *)

let setup_toplevel () =
  Jscoq.init ();
  Sys.interactive := false;
  let _header1 = Printf.sprintf "JsCoqTop alpha\n" in
  let _header2 = Printf.sprintf
      "     Compiled with Js_of_ocaml version %s" Sys_js.js_of_ocaml_version in
  Sys.interactive := true;
  ()

let resize ~container ~textbox ()  =
  Lwt.pause () >>= fun () ->
  textbox##style##height <- Js.string "auto";
  textbox##style##height <- Js.string (Printf.sprintf "%dpx" (max 18 textbox##scrollHeight));
  container##scrollTop <- container##scrollHeight;
  Lwt.return ()

(* we need to compute the hash form href to avoid different encoding behavior
     across browser. see Url.get_fragment *)
let parse_hash () =
  let frag = Url.Current.get_fragment () in
  Url.decode_arguments frag

let rec iter_on_sharp ~f x =
  Js.Opt.iter (Dom_html.CoerceTo.element x)
	      (fun e -> if Js.to_bool (e##classList##contains(Js.string "sharp")) then f e);
  match Js.Opt.to_option x##nextSibling with
  | None -> ()
  | Some n -> iter_on_sharp ~f n

let setup_js_preview () =
  let ph = by_id "last-js" in
  let runcode : (string -> 'a) = Js.Unsafe.global##toplevelEval in
  Js.Unsafe.global##toplevelEval <- (fun bc ->
      ph##innerHTML <- Js.string bc;
      runcode bc
    )

let text s =
  Tyxml_js.Html5.(span ~a:[a_class []] [pcdata s])

let append output s =
  Dom.appendChild output (Tyxml_js.To_dom.of_element (text s))

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

(* Hack to support dynamic linking *)
open Compiler
let split_primitives p =
  let len = String.length p in
  let rec split beg cur =
    if cur >= len then []
    else if p.[cur] = '\000' then
      String.sub p beg (cur - beg) :: split (cur + 1) (cur + 1)
    else
      split beg (cur + 1) in
  Array.of_list(split 0 0)

let setup_dynlink () =
  Hashtbl.add Toploop.directive_table "enable" (Toploop.Directive_string Option.Optim.enable);
  Hashtbl.add Toploop.directive_table "disable" (Toploop.Directive_string Option.Optim.disable);
  Hashtbl.add Toploop.directive_table "debug_on" (Toploop.Directive_string Option.Debug.enable);
  Hashtbl.add Toploop.directive_table "debug_off" (Toploop.Directive_string Option.Debug.disable);
  Hashtbl.add Toploop.directive_table "tailcall" (Toploop.Directive_string (Option.Param.set "tc"));
  Topdirs.dir_directory "/cmis";
  let initial_primitive_count =
    Array.length (split_primitives (Symtable.data_primitive_names ())) in

  let compile s =
    let prims =
      split_primitives (Symtable.data_primitive_names ()) in
    let unbound_primitive p =
      try ignore (Js.Unsafe.eval_string p); false with _ -> true in
    let stubs = ref [] in
    Array.iteri
      (fun i p ->
         if i >= initial_primitive_count && unbound_primitive p then
           stubs :=
             Format.sprintf
               "function %s(){caml_failwith(\"%s not implemented\")}" p p
             :: !stubs)
      prims;
    let output_program = Driver.from_string prims s in
    let b = Buffer.create 100 in
    output_program (Pretty_print.to_buffer b);
    Format.(pp_print_flush std_formatter ());
    Format.(pp_print_flush err_formatter ());
    flush stdout; flush stderr;
    let res = Buffer.contents b in
    let res = String.concat "" !stubs ^ res in
    Js.Unsafe.global##toplevelEval(res)
  in
  Js.Unsafe.global##toplevelCompile <- compile (*XXX HACK!*);
  Js.Unsafe.global##toplevelEval <- (fun x -> Js.Unsafe.eval_string x);
  ()

let run _ =
  let container = by_id "toplevel-container" in
  let output    = by_id "output" in
  let textbox : 'a Js.t = by_id_coerce "userinput" Dom_html.CoerceTo.textarea in

  let sharp_chan = open_out "/dev/null0" in
  let sharp_ppf = Format.formatter_of_out_channel sharp_chan in

  let caml_chan = open_out "/dev/null1" in
  let caml_ppf = Format.formatter_of_out_channel caml_chan in

  let execute () =
    (* (append output "Calling execute\n"); *)
    let content = Js.to_string (textbox##value##trim()) in
    (* let content' = *)
    (*   let len = String.length content in *)
    (*   if try content <> "" && content.[len-1] <> ';' && content.[len-2] <> ';' with _ -> true *)
    (*   then content ^ ";;" *)
    (*   else content in *)
    current_position := output##childNodes##length;
    append output ("# " ^ content ^ "\n");
    textbox##value <- Js.string "";
    History.push content;
    Jscoq.execute true ~pp_code:sharp_ppf caml_ppf content;
    resize ~container ~textbox () >>= fun () ->
    container##scrollTop <- container##scrollHeight;
    textbox##focus();
    Lwt.return_unit in

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

  begin (* setup handlers *)
    textbox##onkeyup <-   Dom_html.handler (fun _ -> Lwt.async (resize ~container ~textbox); Js._true);
    textbox##onchange <-  Dom_html.handler (fun _ -> Lwt.async (resize ~container ~textbox); Js._true);
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

  Lwt.async_exception_hook:=(fun exc ->
    Format.eprintf "exc during Lwt.async: %s@." (Printexc.to_string exc);
    match exc with
    | Js.Error e -> Firebug.console##log(e##stack)
    | _ -> ());

  Lwt.async (fun () ->
    resize ~container ~textbox () >>= fun () ->
    textbox##focus ();
    Lwt.return_unit);

  Sys_js.set_channel_flusher caml_chan  (append output);
  Sys_js.set_channel_flusher sharp_chan (append output);
  Sys_js.set_channel_flusher stdout     (append output);
  Sys_js.set_channel_flusher stderr     (append output);

  setup_pseudo_fs ();
  setup_dynlink ();
  setup_toplevel ();
  setup_js_preview ();
  History.setup ();

  (* Setup files *)

  textbox##value <- Js.string "Require Import Coq.Init.Prelude.";
  (* Jscoq.execute true ~pp_code:sharp_ppf caml_ppf "Notation \"A -> B\" := (forall _ : A, B) (at level 70)."; *)
  ()

let _ = Dom_html.window##onload <- Dom_html.handler (fun _ -> run (); Js._false)
