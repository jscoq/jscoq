# JsCoq 1.0 ((())((()()(()))((()()))))
--------------------------------------

  - [ ] Automatic parsing mode.
  - [ ] Execution gutters.
  - [ ] Move to sertop.
  - [ ] UI layout.
  - [x] Worker support.
  - [_] Use Dune as build system

Pending worker tasks:

+ Race: we cancel, then add before the cancelled arrives. Review and
  factorize code.
+ don't reexec states, as this brings back the parser to an improper
  state.
+ Better printing.
+ Library tweaks.
+ quick prev/next creates problems in long commands.
+ we are reusing span_ids and this is not ok for the STM.

  Released on: 

# JsCoq 0.9 "The idea kills the idea"
-------------------------------------

  - [ ] Support for UI layouts.
  - [_] Use Dune as build system
  - [x] Support for Coq 8.9
  - [x] Static compilation of cma/cmo. (thanks @hhugo).
  - [x] Support for Coq 8.6/8.7/8.8/8.9.
  - [x] Migrated to ppx for jsoo syntax.
  - [x] Port to Ocaml 4.06.1
  - [x] Port to JSOO 3.1.0
  - [x] Full support for SF.
  - [x] Many small fixes.
  - [x] Goal display on hover.

  Released on: 

# JsCoq 0.8 "The most inefficient programming language ever designed"
-------------------------------------

  - Port to Ocaml 4.03.0.
  - Fast package loading using TypedArrays. (thanks @gasche @hhugo).
  - Many small fixes.

  Released on: 13/06/2016

# JsCoq 0.7 "Hott"
--------------------------------

  - New panel support.
  - Support many more addons.

# JsCoq 0.6 "���𐄽𐄺�"
--------------------------------

  - JSON/sexp serialization of Constr_uctions.
  - Add jscoq loader.

# JsCoq 0.5 "Alexandria"
--------------------------------

  - Library manager support.
  - Coqdoc backend.

# JsCoq 0.4 "For real"
--------------------------------

  - New manager for multi-snippet documents.
  - Rudimentary Cache of cma => js compilation.

# JsCoq 0.3 "Kitties everywhere"
--------------------------------

  - New IDE/parsing based on CodeMirror.

# JsCoq 0.2 "Castle edition"
----------------------------

  - Asynchronous library caching.
  - CMA precompilation

# JsCoq 0.1 "Mediterranean edition"
-----------------------------------

  - Initial release, support for plugins and modules.