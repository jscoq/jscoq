let to_name = String.concat "_"
let to_dir  = String.concat "/"
let prefix  = "coq-fs"

(* Default library list *)
let plugin_list =
  [ ["syntax"]
  ; ["decl_mode"]
  ; ["cc"]
  ; ["firstorder"]
  ; ["setoid_ring"]
  (* These two were disabled *)
  ; ["extraction"]
  ; ["funind"]
  ; ["quote"]
  ]

(* Plugins disabled for performance reasons:

   funind
   extraction
*)

let coq_theory_list =
  [ ["Init"]
  ; ["Bool"]
  ; ["Logic"]
  ; ["Program"]
  ; ["Classes"]
  ; ["Structures"]
  ; ["Relations"]
  ; ["Setoids"]
  ; ["Arith"]
  ; ["PArith"]
  ; ["NArith"]
  ; ["ZArith"]
  ; ["Lists"]
  ; ["Vectors"]
  ; ["Unicode"]

  ; ["Numbers"]
  ; ["Numbers"; "NatInt"]
  ; ["Numbers"; "Natural"; "Abstract"]
  ; ["Numbers"; "Integer"; "Abstract"]
  ]

let addons_list =
  [ ["Ssreflect"] ]

