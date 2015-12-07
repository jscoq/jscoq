let to_name = String.concat "_"
let to_dir  = String.concat "/"
let prefix  = "coq-fs"

(* Default FS list *)
let plugin_list =
  [ ["Coq"; "syntax"]
  ; ["Coq"; "decl_mode"]
  ; ["Coq"; "cc"]
  ; ["Coq"; "firstorder"]
  ; ["Coq"; "setoid_ring"]
  ; ["Coq"; "extraction"]
  ; ["Coq"; "funind"]
  ; ["Coq"; "quote"]
  ]

let coq_theory_list =
  [ ["Coq"; "Init"]
  ; ["Coq"; "Unicode"]
  ; ["Coq"; "Bool"]
  ; ["Coq"; "Logic"]
  ; ["Coq"; "Program"]
  ; ["Coq"; "Classes"]
  ; ["Coq"; "Structures"]
  ; ["Coq"; "Relations"]
  ; ["Coq"; "Setoids"]
  ; ["Coq"; "Arith"]
  ; ["Coq"; "PArith"]
  ; ["Coq"; "NArith"]
  ; ["Coq"; "ZArith"]
  ; ["Coq"; "Lists"]
  ; ["Coq"; "Vectors"]

  ; ["Coq"; "Numbers"]
  ; ["Coq"; "Numbers"; "NatInt"]
  ; ["Coq"; "Numbers"; "Natural"; "Abstract"]
  ; ["Coq"; "Numbers"; "Integer"; "Abstract"]
  ]

(* Packages *)

let pkgs : (string * string list list) list=
  [ "init",
    [ ["Coq"; "syntax"]
    ; ["Coq"; "decl_mode"]
    ; ["Coq"; "cc"]
    ; ["Coq"; "firstorder"]
    ; ["Coq"; "extraction"]
    ; ["Coq"; "funind"]
    ; ["Coq"; "quote"]
    ; ["Coq"; "Init"]
    ; ["Coq"; "Bool"]
    ; ["Coq"; "Unicode"]
    ; ["mathcomp"; "ssreflect"]
    ]
  ; "math-comp",
    [ ["mathcomp"; "algebra"]
    ; ["mathcomp"; "fingroup"]
    ; ["mathcomp"; "solvable"]
    ; ["mathcomp"; "field"]
    ]
  ; "coq-base",
    [ ["Coq"; "Logic"]
    ; ["Coq"; "Program"]
    ; ["Coq"; "Classes"]
    ; ["Coq"; "Structures"]
    ; ["Coq"; "Relations"]
    ; ["Coq"; "Setoids"]
    ; ["Coq"; "Lists"]
    ; ["Coq"; "Vectors"]
    ]
  ; "coq-arith",
    [ ["Coq"; "setoid_ring"]
    ; ["Coq"; "Arith"]
    ; ["Coq"; "PArith"]
    ; ["Coq"; "NArith"]
    ; ["Coq"; "ZArith"]
    ; ["Coq"; "Numbers"]
    ; ["Coq"; "Numbers"; "NatInt"]
    ; ["Coq"; "Numbers"; "Natural"; "Abstract"]
    ; ["Coq"; "Numbers"; "Integer"; "Abstract"]
    ]
  ]

