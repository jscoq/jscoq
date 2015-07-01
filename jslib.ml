let theory_list =
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

  ; ["Numbers"]
  ; ["Numbers"; "NatInt"]
  ; ["Numbers"; "Natural"; "Abstract"]
  ; ["Numbers"; "Integer"; "Abstract"]
  ]

let plugin_list =
  [ ["setoid_ring"]
  ; ["quote"]
  ; ["syntax"]
  ; ["decl_mode"]
  ; ["cc"]
  ; ["firstorder"]
  ]

(* Disabled for performance reasons:

funind
extraction

*)
