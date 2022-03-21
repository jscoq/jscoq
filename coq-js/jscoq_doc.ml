(************************************************************************)
(* Coq SerAPI Plugin                                                    *)
(* Copyright 2016 Emilio J. Gallego Arias, MINES ParisTech              *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)
(* LICENSE: GPLv3+                                                      *)
(************************************************************************)

(******************************************************************************)
(* Taken from Core_kernel, (c) Jane Street, releaser under Apache License 2.0 *)
let split_while xs ~f =
  let rec loop acc = function
    | hd :: tl when f hd -> loop (hd :: acc) tl
    | t -> (List.rev acc, t)
  in
  loop [] xs

(* XXX: move to coq_pp_utils *)
module JsCoqPp = struct
  open Format
let pp_stateid fmt id = fprintf fmt "%d" (Stateid.to_int id)

let pp_str fmt str = fprintf fmt "%s" str

let pp_opt pp fmt opt = match opt with
  | None   -> ()
  | Some x -> fprintf fmt "%a" pp x

let rec pp_list ?sep pp fmt l = match l with
    []         -> fprintf fmt ""
  | csx :: []  -> fprintf fmt "@[%a@]" pp csx
  | csx :: csl -> fprintf fmt "@[%a@]%a@;%a" pp csx (pp_opt pp_str) sep (pp_list ?sep pp) csl
end
open JsCoqPp

(* Internal Coq document model: At the suggestion of Clément Pit--Claudel,
 * we extend the STM document model to work on a cancel-based fashion.
 *
 * All Coq STM edit/add operations *must* be accessed performed using
 * this interface in order to maintain consistency.
 *)

(* Our document model is linear for now *)
type ser_doc = Stm.doc * Stateid.t list

let pp fmt l =
  Format.fprintf fmt "@[%a@]" (pp_list ~sep:" " pp_stateid) l

let _dump_doc doc =
  Format.eprintf "%a@\n%!" pp doc

let create doc = doc, [Stateid.initial]

let tip ser_doc =
  let _, sdoc = ser_doc in
  List.hd sdoc

(* Sadly this is not properly exported from Stm/Vernac *)
exception NoSuchState of Stateid.t

let _ = CErrors.register_handler (function
    | NoSuchState sid ->
      Some (Pp.str ("Trying to add on top of non-existent span: " ^ Stateid.to_string sid))
    | _ ->
      None)

let parse ~doc ~ontop stm =
  let doc, sdoc = doc in
  if not (List.mem ontop sdoc) then raise (NoSuchState ontop);
  let pa = Pcoq.Parsable.make (Stream.of_string stm) in
  let entry = Pvernac.main_entry in
  Option.get @@ Stm.parse_sentence ~doc ~entry ontop pa

(* Main add logic; we check that the ontop state is present in the
 * document, as it could well happen that the user request to add
 * arrives out of order wrt to a cancel request demanded by Coq, even
 * if I think we agree this shouldn't be possible. Then, we add and
 * update our document.
 *)
let add ~doc ~ontop ~newid stm =
  let doc, sdoc = doc in
  let verb = false                                       in
  if not (List.mem ontop sdoc) then raise (NoSuchState ontop);
  let pa = Pcoq.Parsable.make (Stream.of_string stm)     in
  let entry = Pvernac.main_entry in
  let east = Option.get Stm.(parse_sentence ~doc ~entry ontop pa) in
  let ndoc, new_st, foc = Stm.add ~doc ~ontop ~newtip:newid verb east in
  let new_sdoc = new_st :: sdoc in
  east.CAst.loc, foc, (ndoc,new_sdoc)

let query ~doc ~at ~route query =
  let doc, sdoc = doc in
  if not (List.mem at sdoc) then raise (NoSuchState at);
  let pa = Pcoq.Parsable.make (Stream.of_string query) in
  Stm.query ~doc ~at ~route pa

let load ~doc filename ~echo =
  let ndoc, sdoc = doc in
  let vernac_state = Vernac.State.
    { doc = ndoc; sid = tip doc; proof = None; time = false } in
  (* loading with ~check:true to avoid some stack overflows in stm *)
  let vernac_state' =
    Vernac.load_vernac ~echo ~check:true ~interactive:false
                        ~state:vernac_state filename in
  let new_sdoc = vernac_state'.sid :: sdoc in
  (vernac_state.doc, new_sdoc)

(* invalid range returns a list of all the invalid stateid from
   can_st and the new doc _in reverse order_ *)
let invalid_range ~sdoc can_st =
  if not (List.mem can_st sdoc)
  then [], sdoc
  else split_while sdoc
        ~f:(fun st -> Stateid.newer_than st can_st || Stateid.equal st can_st)

(* XXX: Not implemented yet *)
let cancel_interval st (foc : Stm.focus) =
  let fmt = Format.err_formatter in
  Format.fprintf fmt "Cancel interval: [%a -- %a]" pp_stateid st pp_stateid Stm.(foc.stop);
  []

(* We follow a suggestion by Clément to report sentence invalidation
 * in a more modular way: When we issue the cancel command, we will
 * look for the cancelled part
 *)
let cancel ~doc can_st =
  let doc, sdoc = doc in
  (* dump_doc (); *)
  (* cancel and keep range *)
  let c_ran, k_ran = invalid_range ~sdoc can_st in
  (* Special case for a cancel on the initial state! *)
  let k_ran, edit_st = match k_ran with
    | []         -> [Stateid.initial], Stateid.initial
    | (st::rstm) -> (st::rstm), st
  in
  let doc, eres = Stm.edit_at ~doc edit_st in
  match eres with
  | NewTip -> c_ran, (doc,k_ran)
    (* - [tip] is the new document tip.
       - [st]   -- [stop] is dropped.
       - [stop] -- [tip]  has been kept.
       - [start] is where the editing zone starts
       - [add] happen on top of [id].
    *)
  | Focus foc -> cancel_interval edit_st foc, (doc, sdoc)


(* Edit is deprecated, we implement it in terms of cancel. *)
let edit ~doc edit_st =
  let doc, sdoc = doc in
  if not (List.mem edit_st sdoc)
  then [], (doc,sdoc)
  else
    let doc, eres = Stm.edit_at ~doc edit_st in
    match eres with
    | NewTip    -> let cc, sdoc = split_while sdoc ~f:(fun st -> Stateid.newer_than st edit_st) in cc, (doc, sdoc)
    | Focus foc -> cancel_interval edit_st foc, (doc, sdoc)

let observe ~doc sid =
  let doc, sdoc = doc in
  let doc = Stm.observe ~doc sid in
  doc, sdoc

(** tactic info *)
let _count_goals (pst : Declare.Proof.t) : int =
  let pf = Declare.Proof.get pst in
  let { Proof.goals ; _ } = Proof.data pf in
  List.length goals

let get_hyp_name sigma (g : Evar.t) =
  let open Context.Named in
  (* The next 4 lines will find the hypothesis (env of type
     named_context) of a particular goal, it is indeed black magic :( *)
  let evi = Evd.find sigma g in
  let env, _sigma = Evd.evar_filtered_env (Global.env ()) evi, Evd.evar_concl evi in
  let env = Environ.named_context env in
  (* We just fold over the name context to extract the names *)
  let names = fold_inside (fun acc d -> Declaration.get_id d :: acc) env ~init:[] in
  names

let get_hyps_name sigma pst =
  let pf = Declare.Proof.get pst in
  let { Proof.goals ; _ } = Proof.data pf in
  List.map (get_hyp_name sigma) goals

let diff_pstates sigma (_pst1 : Declare.Proof.t) (pst2 : Declare.Proof.t) =
  get_hyps_name sigma pst2

(* Hack for now *)
let tmp_sid : int ref = ref (max_int - 1)

let pstate_of_st m = match m with
  | Stm.Valid (Some { Vernacstate.lemmas; _ } ) ->
    Option.map (Vernacstate.LemmaStack.with_top ~f:(fun p -> p)) lemmas
  | _ -> None

let context_of_st m = match m with
  | Stm.Valid (Some { Vernacstate.lemmas = Some lemma; _ } ) ->
    Vernacstate.LemmaStack.with_top lemma
      ~f:(fun p -> Declare.Proof.get_current_context p)
    (* let pstate = st.Vernacstate.proof in *)
    (* let summary = States.summary_of_state st.Vernacstate.system in
     * Safe_typing.env_of_safe_env Summary.(project_from_summary summary Global.global_env_summary_tag) *)
  | _ ->
    let env = Global.env () in Evd.from_env env, env

let exec_tactic_speculatively ~doc ~pstate ~sid tac =
  let pa = Pcoq.Parsable.make (Stream.of_string tac) in
  let entry = Pvernac.main_entry in

  match Stm.parse_sentence ~doc sid ~entry pa with
  | None -> []
  | Some ast ->
    (* Execute the sentence. TODO add a fucntion to atomically add and
       execute a sentence. *)
    decr tmp_sid;
    (* nsid == newtip ; also todo check add_focus *)
    let doc, nsid, _add_focus = Stm.add ~doc ~ontop:sid ~newtip:(Stateid.of_int !tmp_sid) false ast in
    let doc = Stm.observe ~doc nsid in
    let st = Stm.state_of_id ~doc nsid in
    let pstate' = pstate_of_st st in
    let sigma', _env = context_of_st st in
    let _doc, _focus = Stm.edit_at ~doc sid in
    match pstate' with
    | None -> []                  (* the proof was closed *)
    | Some pstate' ->
      diff_pstates sigma' pstate pstate'

let tactic_info ~doc ~sid tac =
  let doc, _ = doc in
  let st = Stm.state_of_id ~doc sid in
  (* let sigma, env = context_of_st st in *)
  let pstate = pstate_of_st st in
  match pstate with
  | None -> []                    (* No open proof *)
  | Some pstate ->
    exec_tactic_speculatively ~doc ~pstate ~sid tac

