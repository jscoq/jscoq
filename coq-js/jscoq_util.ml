(* Coq JavaScript API. Based in the coq source code and js_of_ocaml.
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2019 Shachar Itzhaky, Technion, Haifa.
 * LICENSE: GPLv3+
 *
 *)

let rec pp_opt (d : Pp.t) = let open Pp in
  let rec flatten_glue l = match l with
    | []  -> []
    | (Ppcmd_glue g :: l) -> flatten_glue (List.map repr g @ flatten_glue l)
    | (Ppcmd_string s1 :: Ppcmd_string s2 :: l) -> flatten_glue (Ppcmd_string (s1 ^ s2) :: flatten_glue l)
    | (x :: l) -> x :: flatten_glue l
  in
  unrepr (match repr d with
      | Ppcmd_glue []   -> Ppcmd_empty
      | Ppcmd_glue [x]  -> repr (pp_opt x)
      | Ppcmd_glue l    -> Ppcmd_glue List.(map pp_opt (map unrepr (flatten_glue (map repr l))))
      | Ppcmd_box(bt,d) -> Ppcmd_box(bt, pp_opt d)
      | Ppcmd_tag(t, d) -> Ppcmd_tag(t,  pp_opt d)
      | d -> d
    )
[@@warning "-4"]

let fbc_opt (fbc : Feedback.feedback_content) =
  match fbc with
  | Message(id,loc,msg) -> Feedback.Message(id,loc,pp_opt msg)
  | _ -> fbc
[@@warning "-4"]

let fb_opt (fb : Feedback.feedback) =
  { fb with contents = fbc_opt fb.contents }

