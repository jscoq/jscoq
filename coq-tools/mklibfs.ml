(*
   Build the std filesystem for jscoq

   By Emilio J. Gallego Arias, Mines ParisTech, Paris.
*)

open Format
module Dl = Dftlibs

let pp_str ppf s = fprintf ppf "%s" s

let rec pp_list pp fmt l = match l with
    []         -> fprintf fmt ""
  | csx :: []  -> fprintf fmt "%a" pp csx
  | csx :: csl -> fprintf fmt "%a %a" pp csx (pp_list pp) csl

let output_librule fmt bpath path =
  let name    = Dl.to_name path                                in
  (* Strip "Coq" suffix *)
  let dir     = List.tl path                                   in
  let coqdir  = Dl.to_dir ("$(COQDIR)" :: bpath :: dir)        in
  let outdir  = Dl.to_dir (Dl.prefix :: (List.hd path) :: dir) in
  let vo_pat  = Dl.to_dir [coqdir; "*.vo"]                     in
  let cma_pat = Dl.to_dir [coqdir; "*.cma"]                    in
  (* Rule for the dir *)
  fprintf fmt "%s_dir:\n\tmkdir -p %s\n" name outdir;
  (* Pattern expansion *)
  fprintf fmt "%s_VO:=$(wildcard %s)\n"  name vo_pat;
  fprintf fmt "%s_CMA:=$(wildcard %s)\n" name cma_pat;
  (* Copy rule *)
  fprintf fmt "%s: %s_dir $(%s_VO) $(%s_CMA)\n\t$(shell for i in $(%s_VO);  do cp -a $$i %s/`basename $$i`; done)\n\t$(shell for i in $(%s_CMA); do cp -a $$i %s/`basename $$i`; done)\n\n"
    name name name name name outdir name outdir
(*
  COQ_SETOIDS=$(COQTDIR)/Setoids/*.vo
  COQ_SETOIDS_DEST=filesys/coq_setoids
  coq_setoids: $(COQ_SETOIDS)
  $(shell for i in $(COQ_SETOIDS); do base64 $$i > $(COQ_SETOIDS_DEST)/`basename $$i`; done)
*)

let output_global_rules fmt =
  (* XXX: make dirs *)
  fprintf fmt "libs-auto: %a\n" (pp_list pp_str) @@
    List.map Dl.to_name (Dl.coq_theory_list @ Dl.plugin_list)

let gen_makefile () =
  List.iter (output_librule std_formatter "plugins")  Dl.plugin_list;
  List.iter (output_librule std_formatter "theories") Dl.coq_theory_list;
  output_global_rules std_formatter

let _ =
  gen_makefile ()

