# JsCoq 0.10 ((())((()()(()))((()()))))
---------------------------------------

  - [ ] Automatic parsing mode.
  - [ ] Execution gutters.
  - [ ] Move to sertop.
  - [ ] Support for UI layouts.
  - [_] Use Dune as build system (@ejgallego)

Pending worker tasks:

+ Race: we cancel, then we add before the cancelled event arrives.
+ Be careful about re-execing states, as this brings back the parser to an improper state.
+ quick prev/next creates problems in long commands.
+ we are reusing span_ids and this is not ok for the STM.

  Released on: 

# JsCoq 0.9 "The idea kills the idea"
-------------------------------------

  - [x] JsCoq now runs as a worker (@ejgallego @corwin-of-amber).
  - [x] Support for Coq 8.6/8.7/8.8/8.9. (@ejgallego)
  - [x] Port to Ocaml 4.07.1. (@ejgallego)
  - [x] Port to JSOO 3.3.0. (@ejgallego)
  - [x] Static compilation of cma/cmo. (@ejgallego, thanks @hhugo).
  - [x] Migrated to ppx for jsoo syntax. (@ejgallego)
  - [x] Native rendering of Coq's Pp type. (@corwin-of-amber)
  - [x] Migrate from d3 to jQuery for DOM manipulation. (@corwin-of-amber)
  - [x] Full support for Software Foundations. (@ejgallego)
  - [x] Many small fixes. (@ejgallego @corwin-of-amber)
  - [x] Goal display on hover. (@ejgallego @corwin-of-amber)
  - [x] Building with 32-bit on macOS. (@corwin-of-amber)
  - [x] Contextual info when hovering identifiers in goals pane. (@corwin-of-amber)
  - [x] Contextual info for identifier under cursor. (@corwin-of-amber)
  - [x] Support for adding packages from Zip files. (@corwin-of-amber)
  - [x] Automatic download of packages on Require. (@corwin-of-amber)
  - [x] Fine-grained module dependencies for Coq standard library. (@corwin-of-amber)
  - [x] company-coq-style symbols and subscripts. (@corwin-of-amber)
  - [x] Auto-completion of tactics and lemmas. (@corwin-of-amber)
  - [x] PoC running on Node.js. (@corwin-of-amber)
  - [x] Improved goal display (@ejgallego)
  - [x] Use Dune as build system (@ejgallego)

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
