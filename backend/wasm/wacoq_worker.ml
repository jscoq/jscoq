external emit : string -> unit = "wacoq_emit" (* implemented in `core.ts` *)


let fb_handler (fb : Feedback.feedback) =
  emit @@ "[]" (*serialize [Feedback fb]*)

let handleRequest json_str =
  "[]"
  (*
  let resp =
  try
    let cmd = deserialize json_str                     in
    match cmd with
      | Result.Error e -> [JsonExn e]
      | Result.Ok cmd -> wacoq_execute cmd
  with exn ->
    [coq_exn_info exn]
  in
  Interpreter.cleanup () ;
  serialize resp *)

let handleRequestsFromStdin () =
  try
    while true do
      emit @@ handleRequest @@ Stdlib.read_line ()
    done
  with End_of_file -> ()


let () =
  try
    (* emit @@ serialize [CoqInfo (info_string ())] ; *)
    ignore @@ Feedback.add_feeder fb_handler ;
    Callback.register "wacoq_post" handleRequest ;
    if (Array.length Sys.argv > 1) && Sys.argv.(1) = "-stdin" then
      handleRequestsFromStdin ()
  with CErrors.UserError(pp) ->
    print_endline @@ "error! " ^ Pp.string_of_ppcmds pp
