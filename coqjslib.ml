(* Helpers for Library building.

   By Emilio J. Gallego Arias, Mines ParisTech, Paris.
*)

open Format

(* Paths we include for now, without the Coq prefix!

   XXX: move to JS.
 *)

let to_name = String.concat "_"
let to_dir  = String.concat "/"

let pp_str ppf s = fprintf ppf "%s" s

let rec pp_list pp fmt l = match l with
    []         -> fprintf fmt ""
  | csx :: []  -> fprintf fmt "%a" pp csx
  | csx :: csl -> fprintf fmt "%a %a" pp csx (pp_list pp) csl

let output_librule fmt bpath path =
  let name    = to_name path                     in
  let dir     = to_dir  path                     in
  let coqdir  = to_dir ["$(COQDIR)"; bpath; dir] in
  let fsdir   = to_dir ["filesys"; name]         in
  let vo_pat  = to_dir [coqdir; "*.vo"]          in
  let cma_pat = to_dir [coqdir; "*.cma"]         in
  (* Rule for the dir *)
  fprintf fmt "%s:\n\tmkdir -p %s\n" fsdir fsdir;
  (* Pattern expansion *)
  fprintf fmt "%s_VO:=$(wildcard %s)\n"  name vo_pat;
  fprintf fmt "%s_CMA:=$(wildcard %s)\n" name cma_pat;
  (* Copy rule *)
  fprintf fmt "%s: %s $(%s_VO) $(%s_CMA)\n\t$(shell for i in $(%s_VO);  do cat $$i > %s/`basename $$i`; done)\n\t$(shell for i in $(%s_CMA); do cat $$i > %s/`basename $$i`; done)\n\n"
    name fsdir name name name fsdir name fsdir
(*
  COQ_SETOIDS=$(COQTDIR)/Setoids/*.vo
  COQ_SETOIDS_DEST=filesys/coq_setoids
  coq_setoids: $(COQ_SETOIDS)
  $(shell for i in $(COQ_SETOIDS); do base64 $$i > $(COQ_SETOIDS_DEST)/`basename $$i`; done)
*)

let output_global_rules fmt =
  (* XXX: make dirs *)
  fprintf fmt "libs-auto: %a\n" (pp_list pp_str) @@
    List.map to_name (Jsdftlib.coq_theory_list @ Jsdftlib.plugin_list)

let gen_makefile () =
  List.iter (output_librule std_formatter "plugins")  Jsdftlib.plugin_list;
  List.iter (output_librule std_formatter "theories") Jsdftlib.theory_list;
  output_global_rules std_formatter

let _ =
  gen_makefile ()

