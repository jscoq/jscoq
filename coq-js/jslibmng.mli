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

open Js_of_ocaml
open Js

(* XXX This should be the serialization of the jslib.ml:coq_pkg, but waiting for *)
class type pkgInfo = object
  method name        : js_string t writeonly_prop
  method desc        : js_string t writeonly_prop
  method no_files_   : int         writeonly_prop
end

class type bundleInfo = object
  method desc        : js_string t            writeonly_prop
  method deps        : js_string t js_array t writeonly_prop
  method pkgs        : pkgInfo   t js_array t writeonly_prop
end

class type progressInfo = object
  method bundle_name_ : js_string t writeonly_prop
  method pkg_name_    : js_string t writeonly_prop
  method loaded       : int         writeonly_prop
  method total        : int         writeonly_prop
end

(* Global Callbacks *)
type pkg_callbacks = {
  bundle_info     : bundleInfo t -> unit;
  bundle_start    : bundleInfo t -> unit;
  bundle_load     : bundleInfo t -> unit;
  pkg_start    : progressInfo t -> unit;
  pkg_progress : progressInfo t -> unit;
  pkg_load     : progressInfo t -> unit;
}

(** [init callback lib_path pkg_callbacks available_pkg init_pkgs]
    gather package list [available_pkg] and start preloading
    [init_pkgs] from directory [lib_path], calls [callback] when
    done. *)
val init : (unit -> unit) -> pkg_callbacks ->
  js_string t ->
  js_string t js_array t -> js_string t js_array t -> unit

(** [load_pkg pkg_file] load package [file], returns the total number
    of packages *)
val load_pkg : string -> unit

(** [coq_resource_req url] query the manager's cache for object [url] *)
val coq_vo_req  : string -> string option

(** [coq_cma_req cma] load the [cma] file or else do nothing *)
val coq_cma_req : string -> unit
