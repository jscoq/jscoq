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

  ; ["Coq"; "fourier"]
  ; ["Coq"; "omega"]
  ; ["Coq"; "romega"]
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
  ; ["Coq"; "Reals"]
  ; ["Coq"; "Strings"]

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
    ; ["Coq"; "Strings"]
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
  ; "coq-reals",
    [ ["Coq"; "fourier"]
    ; ["Coq"; "omega"]
    ; ["Coq"; "Reals"] ]
  ; "coquelicot",
    [ [ "Coquelicot" ] ]
  ; "flocq",
    [ ["Coq"; "romega"]
    ; [ "Flocq" ; "Core" ] ]
  ; "tlc",
    [ ["TLC"] ]
  ; "sf",
    [ ["SF"] ]
  ]

