(* Hack to support dynamic linking in jsoo *)
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
  let initial_primitive_count =
    Array.length (split_primitives (Symtable.data_primitive_names ())) in

  let compile s =
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
    Js.Unsafe.global##toplevelEval(res)
  in
  Js.Unsafe.global##toplevelCompile <- compile (*XXX HACK!*);
  Js.Unsafe.global##toplevelEval <- (fun x -> Js.Unsafe.eval_string x);
  ()

let _ = setup_dynlink ()

