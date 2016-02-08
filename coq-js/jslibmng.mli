(* JsCoq
 * Copyright (C) 2015 Emilio Gallego / Mines ParisTech
 *
 * LICENSE: GPLv3+
 *)

(* Library management for JsCoq.
 *
 * Due to the large size of Coq libraries, we perform caching and lazy
 * loading in the browser.
*)

open Js

(* XXX This should be the serialization of the jslib.ml:coq_pkg, but waiting for *)
class type pkgInfo = object
  method name        : ('self t, js_string t) meth_callback writeonly_prop
  method desc        : ('self t, js_string t) meth_callback writeonly_prop
  method no_files_   : ('self t, int)         meth_callback writeonly_prop
end

class type bundleInfo = object
  method pkgs        : ('self t, pkgInfo js_array t) meth_callback writeonly_prop
end

class type progressInfo = object
  method bundle_name_ : ('self t, js_string t) meth_callback writeonly_prop
  method pkg_name_    : ('self t, js_string t) meth_callback writeonly_prop
  method loaded       : ('self t, int)         meth_callback writeonly_prop
  method total        : ('self t, int)         meth_callback writeonly_prop
end

(** [init callback pkg_callbacks] gather package list and start preloading, call
    [callback] when done *)
val init : (unit -> unit)         ->
           (bundleInfo -> unit)   ->
           (progressInfo -> unit) ->
           (string -> unit)       ->
           (progressInfo -> unit) -> unit

(** [load_pkg pkg_file] load package [file], returns the total number
    of packages *)
val load_pkg : string -> unit

(** [coq_resource_req url] query the manager's cache for object [url] *)
val coq_vo_req  : js_string t -> js_string t option

(** [coq_cma_req cma] load the [cma] file or else do nothing *)
val coq_cma_req : string -> unit

(** [request_byte_cache md5] return [Some js] if bytecode with with
    digest [md5] is in the cache, None otherwise *)
val request_byte_cache : Digest.t -> js_string t option
