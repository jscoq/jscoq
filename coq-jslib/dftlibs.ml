type selector =
  | All
  | Only of string list
  | Except of string list

let all_of pkgs = List.map (fun pkg -> (pkg, All)) pkgs

let to_name = String.concat "_"
let to_dir  = String.concat "/"
let prefix  = "coq-pkgs"

(* Default FS list *)
let plugin_list =
  [ ["ltac"]
  ; ["syntax"]
  ; ["cc"]
  ; ["firstorder"]
  ; ["ring"]
  ; ["extraction"]
  ; ["funind"]
  ; ["btauto"]
  ; ["rtauto"]  (* TODO add this to one of the bundles *)

  ; ["micromega"]
  ; ["nsatz"]
  ; ["ssrmatching"]
  ; ["ssr"]
  ; ["derive"]  (* TODO add this to one of the bundles *)
  ]

let coq_theory_list =
  [ ["Init"]
  ; ["Unicode"]
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
  ; ["QArith"]
  ; ["Lists"]
  ; ["Vectors"]
  ; ["Reals"]
  ; ["Sets"]
  ; ["FSets"]
  ; ["MSets"]
  ; ["Sorting"]
  ; ["Wellfounded"]
  ; ["Strings"]
  ; ["Floats"]

  ; ["Numbers"]
  ; ["Numbers"; "NatInt"]
  ; ["Numbers"; "Natural"; "Abstract"]
  ; ["Numbers"; "Natural"; "Peano"]
  ; ["Numbers"; "Integer"; "Abstract"]
  ; ["Numbers"; "Cyclic"; "Abstract"]
  ; ["Numbers"; "Cyclic"; "Int31"]
  ; ["Numbers"; "Cyclic"; "Int63"]
  ; ["Numbers"; "Cyclic"; "ZModulo"]
  ]

let user_contrib_list =
  [ ["Ltac2"]
  ]

(* Packages: name, deps, modules *)

let pkgs : (string * string list * (string list * selector) list) list =
  [ "init", [], all_of
    [ ["Coq"; "ltac"]
    ; ["Coq"; "syntax"]
    ; ["Coq"; "cc"]
    ; ["Coq"; "firstorder"]
    ; ["Coq"; "btauto"]
    ; ["Coq"; "Init"]
    ; ["Coq"; "Bool"]
    ; ["Coq"; "Unicode"]
    ; ["Coq"; "ssrmatching"]
    ; ["Coq"; "ssr"]
    ; ["Ltac2"]
    ; ["mathcomp"; "ssreflect"]
    ]
  ; "coq-base", [], all_of
    [ ["Coq"; "Logic"]
    ; ["Coq"; "Program"]
    ; ["Coq"; "Classes"]
    ; ["Coq"; "Structures"]
    ; ["Coq"; "Relations"]
    ; ["Coq"; "Setoids"]
    ; ["Coq"; "Wellfounded"]
    ; ["Coq"; "Strings"]
    ; ["Coq"; "Numbers"]
    ; ["Coq"; "Numbers"; "NatInt"]
    ; ["Coq"; "Numbers"; "Natural"; "Abstract"]
    ; ["Coq"; "extraction"]
    ; ["Coq"; "funind"]
    ] @
    [ ["Coq"; "Arith"], Only ["PeanoNat.vo"; "Le.vo"; "Lt.vo"; "Ge.vo"; "Gt.vo";
                              "Plus.vo"; "Minus.vo"; "Compare_dec.vo"; "Wf_nat.vo"]
    ]
  ; "coq-collections", ["coq-base"], all_of
    [ ["Coq"; "Lists"]
    ; ["Coq"; "Vectors"]
    ; ["Coq"; "Sets"]
    ; ["Coq"; "FSets"]
    ; ["Coq"; "MSets"]
    ; ["Coq"; "Sorting"]
    ]
  ; "coq-arith", ["coq-base"; "coq-collections"],
    [ ["Coq"; "Numbers"; "Natural"; "Peano"], All
    ; ["Coq"; "Numbers"; "Integer"; "Abstract"], All
    ; ["Coq"; "Numbers"; "Cyclic"; "Abstract"], All
    ; ["Coq"; "Numbers"; "Cyclic"; "Int31"], All
    ; ["Coq"; "Numbers"; "Cyclic"; "Int63"], All
    ; ["Coq"; "Numbers"; "Cyclic"; "ZModulo"], All
    ; ["Coq"; "setoid_ring"], All
    ; ["Coq"; "Arith"], Except ["PeanoNat.vo"; "Le.vo"; "Lt.vo"; "Ge.vo"; "Gt.vo";
                                "Plus.vo"; "Minus.vo"; "Compare_dec.vo"; "Wf_nat.vo"]
    ; ["Coq"; "NArith"], All
    ; ["Coq"; "PArith"], All
    ; ["Coq"; "ZArith"], All
    ; ["Coq"; "QArith"], All
    ; ["Coq"; "omega"], All
    ]

  ; "coq-reals", ["coq-arith"], all_of
    (* [ ["Coq"; "fourier"] *)
    [ ["Coq"; "micromega"]
    ; ["Coq"; "nsatz"]
    ; ["Coq"; "Reals"]
    ; ["Coq"; "Floats"]
    ]

  ; "mtac", ["coq-arith"], all_of
    [ ["Mtac"]
    ]

  ; "coquelicot", ["coq-reals"], all_of
    [ [ "Coquelicot" ] ]

  ; "flocq", ["coq-reals"], all_of
    [ [ "Flocq" ; "Core" ]
    ; [ "Flocq" ; "Appli" ]
    ; [ "Flocq" ; "Calc" ]
    ; [ "Flocq" ; "Translate" ]
    ; [ "Flocq" ; "Prop" ] ]

  ; "tlc", ["coq-reals"], all_of
    [ ["TLC"] ]

  (* This remains here even if we build the packages using coq-build.js as
     it seems the dependencies on coq-reals is not detected properly a*)
  ; "lf", ["coq-reals"], all_of
    [ ["LF"] ]

  ; "plf", ["lf"], all_of
    [ ["PLF"] ]

  ; "cpdt", ["coq-reals"], all_of
    [ ["Cpdt"] ]

  ; "color", [ "coq-reals"], all_of
    [ ["CoLoR" ; "Filter"]
    ; ["CoLoR" ; "RPO"]
    ; ["CoLoR" ; "Coccinelle"]
    ; ["CoLoR" ; "Coccinelle" ; "list_extensions"]
    ; ["CoLoR" ; "Coccinelle" ; "term_orderings"]
    ; ["CoLoR" ; "Coccinelle" ; "basis"]
    ; ["CoLoR" ; "Coccinelle" ; "examples"]
    ; ["CoLoR" ; "Coccinelle" ; "examples" ; "cime_trace"]
    ; ["CoLoR" ; "Coccinelle" ; "ac_matching"]
    ; ["CoLoR" ; "Coccinelle" ; "term_algebra"]
    ; ["CoLoR" ; "Coccinelle" ; "unification"]
    ; ["CoLoR" ; "NonTermin"]
    ; ["CoLoR" ; "Term"]
    ; ["CoLoR" ; "Term" ; "Lambda"]
    ; ["CoLoR" ; "Term" ; "SimpleType"]
    ; ["CoLoR" ; "Term" ; "String"]
    ; ["CoLoR" ; "Term" ; "Varyadic"]
    ; ["CoLoR" ; "Term" ; "WithArity"]
    ; ["CoLoR" ; "HORPO"]
    ; ["CoLoR" ; "ProofChecker"]
    ; ["CoLoR" ; "MatrixInt"]
    ; ["CoLoR" ; "SemLab"]
    ; ["CoLoR" ; "Conversion"]
    ; ["CoLoR" ; "DP"]
    ; ["CoLoR" ; "Util"]
    ; ["CoLoR" ; "Util" ; "Multiset"]
    ; ["CoLoR" ; "Util" ; "Vector"]
    ; ["CoLoR" ; "Util" ; "Pair"]
    ; ["CoLoR" ; "Util" ; "FSet"]
    ; ["CoLoR" ; "Util" ; "Integer"]
    ; ["CoLoR" ; "Util" ; "FMap"]
    ; ["CoLoR" ; "Util" ; "Matrix"]
    ; ["CoLoR" ; "Util" ; "Logic"]
    ; ["CoLoR" ; "Util" ; "Polynom"]
    ; ["CoLoR" ; "Util" ; "Option"]
    ; ["CoLoR" ; "Util" ; "FGraph"]
    ; ["CoLoR" ; "Util" ; "Function"]
    ; ["CoLoR" ; "Util" ; "List"]
    ; ["CoLoR" ; "Util" ; "Relation"]
    ; ["CoLoR" ; "Util" ; "Bool"]
    ; ["CoLoR" ; "Util" ; "Nat"]
    ; ["CoLoR" ; "Util" ; "Set"]
    ; ["CoLoR" ; "Util" ; "Algebra"]
    ; ["CoLoR" ; "PolyInt"]
    ; ["CoLoR" ; "SubtermCrit"]
    ; ["CoLoR" ; "MPO"]
    ; ["CoLoR" ; "MannaNess"]
    ]

  ; "dsp", ["mathcomp"], all_of
    [ ["Dsp"] ]

  ; "relalg", ["coq-arith"], all_of
    [ ["RelationAlgebra"] ]

  ; "hott-init", [], all_of
    [ ["Coq"; "syntax"]
    ; ["Coq"; "Init"]
    ; ["Coq"; "Bool"]
    ; ["Coq"; "Program"]
    ; ["Coq"; "Unicode"]
    ]

  ; "hott", ["hott-init"], all_of

    [ ["HoTT"]
    ; ["HoTT" ; "Algebra"]
    ; ["HoTT" ; "Basics"]
    ; ["HoTT" ; "categories"]
    ; ["HoTT" ; "categories"; "Adjoint"]
    ; ["HoTT" ; "categories"; "Adjoint"; "Composition"]
    ; ["HoTT" ; "categories"; "Adjoint"; "Functorial"]
    ; ["HoTT" ; "categories"; "Adjoint"; "UniversalMorphisms"]
    ; ["HoTT" ; "categories"; "Cat"]
    ; ["HoTT" ; "categories"; "Category"]
    ; ["HoTT" ; "categories"; "Category"; "Sigma"]
    ; ["HoTT" ; "categories"; "Category"; "Subcategory"]
    ; ["HoTT" ; "categories"; "CategoryOfSections"]
    ; ["HoTT" ; "categories"; "Comma"]
    ; ["HoTT" ; "categories"; "ExponentialLaws"]
    ; ["HoTT" ; "categories"; "ExponentialLaws"; "Law1"]
    ; ["HoTT" ; "categories"; "ExponentialLaws"; "Law2"]
    ; ["HoTT" ; "categories"; "ExponentialLaws"; "Law3"]
    ; ["HoTT" ; "categories"; "ExponentialLaws"; "Law4"]
    ; ["HoTT" ; "categories"; "Functor"]
    ; ["HoTT" ; "categories"; "Functor"; "Composition"]
    ; ["HoTT" ; "categories"; "Functor"; "Composition"; "Functorial"]
    ; ["HoTT" ; "categories"; "Functor"; "Prod"]
    ; ["HoTT" ; "categories"; "Functor"; "Pointwise"]
    ; ["HoTT" ; "categories"; "FunctorCategory"]
    ; ["HoTT" ; "categories"; "Grothendieck"]
    ; ["HoTT" ; "categories"; "Grothendieck"; "ToSet"]
    ; ["HoTT" ; "categories"; "GroupoidCategory"]
    ; ["HoTT" ; "categories"; "InitialTerminalCategory"]
    ; ["HoTT" ; "categories"; "KanExtensions"]
    ; ["HoTT" ; "categories"; "LaxComma"]
    ; ["HoTT" ; "categories"; "Limits"]
    ; ["HoTT" ; "categories"; "NaturalTransformation"]
    ; ["HoTT" ; "categories"; "NaturalTransformation"; "Composition"]
    ; ["HoTT" ; "categories"; "Profunctor"]
    ; ["HoTT" ; "categories"; "Pseudofunctor"]
    ; ["HoTT" ; "categories"; "PseudonaturalTransformation"]
    ; ["HoTT" ; "categories"; "SetCategory"]
    ; ["HoTT" ; "categories"; "SetCategory"; "Functors"]
    ; ["HoTT" ; "categories"; "Structure"]
    ; ["HoTT" ; "Comodalities"]
    ; ["HoTT" ; "HIT"]
    ; ["HoTT" ; "Modalities"]
    ; ["HoTT" ; "Spaces"]
    ; ["HoTT" ; "Tactics"]
    ; ["HoTT" ; "Types"] ]

  ; "unimath", [ ], all_of

    [ ["UniMath"]
    ; ["UniMath" ; "CategoryTheory" ]
    ; ["UniMath" ; "CategoryTheory" ; "limits" ]
    ; ["UniMath" ; "CategoryTheory" ; "colimits" ]
    ; ["UniMath" ; "PAdics" ]
    ; ["UniMath" ; "Ktheory" ]
    ; ["UniMath" ; "Tactics" ]
    ; ["UniMath" ; "SubstitutionSystems" ]
    ; ["UniMath" ; "Foundations" ]
    ; ["UniMath" ; "Foundations" ; "Basics" ]
    ; ["UniMath" ; "Foundations" ; "Combinatorics" ]
    ; ["UniMath" ; "Foundations" ; "Algebra" ]
    ; ["UniMath" ; "Foundations" ; "NumberSystems" ]
    ; ["UniMath" ; "Dedekind" ]
    ]

  ; "peacoq", [ "init" ], all_of
    [ ["PeaCoq"] ]

  ; "extlib", [ "coq-reals" ], all_of
    [ ["ExtLib"]
    ; ["ExtLib" ; "Core" ]
    ; ["ExtLib" ; "Data" ]
    ; ["ExtLib" ; "Data"; "Eq" ]
    ; ["ExtLib" ; "Data"; "Graph" ]
    ; ["ExtLib" ; "Data"; "Map" ]
    ; ["ExtLib" ; "Data"; "Monads" ]
    ; ["ExtLib" ; "Data"; "Set" ]
    ; ["ExtLib" ; "Generic" ]
    ; ["ExtLib" ; "Programming" ]
    ; ["ExtLib" ; "Recur" ]
    ; ["ExtLib" ; "Relations" ]
    ; ["ExtLib" ; "Structures" ]
    ; ["ExtLib" ; "Tactics" ]
    ]

  ; "plugin-utils", [ ], all_of
    [ ["PluginUtils"] ]

  ; "mirrorcore", [ "plugin-utils"; "extlib" ], all_of
    [ ["MirrorCore"]
    ; ["MirrorCore" ; "Lambda" ]
    ; ["MirrorCore" ; "Lambda"; "Rewrite" ]
    ; ["MirrorCore" ; "MTypes" ]
    ; ["MirrorCore" ; "Reify" ]
    ; ["MirrorCore" ; "RTac" ]
    ; ["MirrorCore" ; "Subst" ]
    ; ["MirrorCore" ; "syms" ]
    ; ["MirrorCore" ; "Util" ]
    ; ["MirrorCore" ; "Views" ]

    ; ["McExamples" ; "Cancel" ]
    ]

  ; "stdpp", [ "coq-reals" ], all_of
    [ [ "stdpp" ] ]

  ; "iris", [ "stdpp" ], all_of
    [ [ "iris" ]
    ; [ "iris" ; "algebra" ]
    ; [ "iris" ; "base_logic" ]
    ; [ "iris" ; "base_logic" ; "lib" ]
    ; [ "iris" ; "heap_lang" ]
    ; [ "iris" ; "base_lang" ; "lib" ]
    ; [ "iris" ; "bi" ]
    ; [ "iris" ; "bi"; "lib" ]
    ; [ "iris" ; "program_logic" ]
    ; [ "iris" ; "proofmode" ]
    ; [ "iris" ; "tests" ]
    ]

  ; "elpi", [ ], all_of
    [ [ "elpi" ]
    ; [ "elpi" ; "ltac" ]
    ; [ "elpi" ; "tutorial" ]
    ; [ "elpi" ; "derive" ]
    ]

  ; "equations", [ "coq-reals" ], all_of
    [ [ "Equations" ]
    ; [ "Equations" ; "Prop" ]
    ]

  ; "simpleio", [ "extlib" ], all_of
    [ [ "SimpleIO" ] ]

  ; "quickchick", [ "coq-reals"; "extlib" ; "simpleio" ], all_of
    [ [ "QuickChick" ]
    ]
  ]
