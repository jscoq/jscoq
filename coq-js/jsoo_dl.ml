(* Hack to support dynamic linking in jsoo *)
open Compiler
open Js

let js_cachea : (js_string t) js_array t = jsnew array_empty ()
let js_cacheb : (js_string t) js_array t = jsnew array_empty ()

let add_to_cache s res =
  let md5 = string @@ Digest.to_hex @@ Digest.string s in
  js_cachea##push(md5);
  js_cacheb##push(res)

(* Main bcache *)
let bcache : (Digest.t, js_string t) Hashtbl.t = Hashtbl.create 200

let populate_bcache () =
  let open Lwt in
  let preload_js msum =
    let open XmlHttpRequest in
    let js_url = "bcache/" ^ msum in
    (* Firebug.console##log(js_url); *)
    perform_raw ~response_type:Text js_url >>= fun frame ->
    let md5        = Digest.from_hex msum in
    Hashtbl.add bcache md5 frame.content;
    Lwt.return_unit
  in
  Lwt.async (fun () ->
      XmlHttpRequest.get "bcache.list" >>= fun res ->
      Firebug.console##log_2(string "bcache file: ", string res.XmlHttpRequest.content);
      let m_list = Regexp.split (Regexp.regexp "\n") res.XmlHttpRequest.content in
      Firebug.console##log_2(string "number of files", List.length m_list);
      Lwt_list.iter_s preload_js m_list
    )

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

  populate_bcache ();

  let initial_primitive_count =
    Array.length (split_primitives (Symtable.data_primitive_names ())) in

  let compile s =
    let md5 = Digest.string s in
    try let js = Hashtbl.find bcache md5 in
      (* Avoid string conversion *)
      Firebug.console##log(string "cache hit!");
      Js.Unsafe.global##toplevelEval(js)
      (* "this" is not correctly bound here... *)
      (* Js.Unsafe.global##eval js *)
    with Not_found ->
    let prims =
      split_primitives (Symtable.data_primitive_names ()) in
    let unbound_primitive p =
      try ignore (Js.Unsafe.eval_string p); false with _ -> true in
    let stubs = ref [] in
    (* Array.iteri (fun i p -> *)
    (*   Jslog.printf Jslog.jscoq_log "primitive %d %s initial\n%!" i p *)
    (* ) prims; *)
    Array.iteri
      (fun i p ->
         if i >= initial_primitive_count && unbound_primitive p then
           stubs :=
             Format.sprintf
               "function %s(){caml_failwith(\"%s not implemented\")}" p p
             :: !stubs)
      prims;
    (* Try to speed things up? *)
    (* Option.Optim.disable "inline"; *)
    (* Option.Optim.disable "compact"; *)
    let output_program = Driver.from_string prims s in
    let b = Buffer.create 500000                    in
    output_program (Pretty_print.to_buffer b);
    Format.(pp_print_flush std_formatter ());
    Format.(pp_print_flush err_formatter ());
    flush stdout; flush stderr;
    let res = Buffer.contents b                     in
    let res = String.concat "" !stubs ^ res         in
    add_to_cache s (Js.string res);
    Js.Unsafe.global##toplevelEval(res)
  in
  Js.Unsafe.global##toplevelCompile <- compile (*XXX HACK!*);
  Js.Unsafe.global##toplevelEval <- (fun x -> Js.Unsafe.eval_string x);
  Js.Unsafe.global##dumpJsCacheA <- js_cachea;
  Js.Unsafe.global##dumpJsCacheB <- js_cacheb;
  ()

let _ = setup_dynlink ()

