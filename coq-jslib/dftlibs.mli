type selector =
  | All
  | Only of string list
  | Except of string list

val to_name : string list -> string
val to_dir : string list -> string
val prefix : string

val plugin_list : string list list
val coq_theory_list : string list list
val user_contrib_list : string list list

val pkgs : (string * string list * (string list * selector) list) list

