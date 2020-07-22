# JsCoq 0.12 "<-as usual->"
-----------------------------------------

 - Port to Coq 8.12 (@ejgallego)
 - [addons] Update mathcomp to 1.11 (@ejgallego)
 - Chunked packages: split large library addons into multiple chunks,
   which are loaded on demand. (@corwin-of-amber)

# JsCoq 0.11 "<-lib->"
-----------------------------------------

 - Project moved to https://github.com/jscoq/jscoq
 - Port to Coq 8.11 (@ejgallego)
 - Ltac2 is now built from the included Coq source and loaded by
   default by the init package (@ejgallego)
 - Primitive floats are available. Note that writing .vo files that
   use primitive floats is not possible from jsCoq; this is due to the
   js runtime representation for integers being already a float, so
   `Marshall` will be confused. Only writing `.vo` files is
   problematic tho, you can however use primitive floats normally, and
   load .vo files that where compiled with `coqc` using primitive
   floats normally (@ejgallego)
 - Enforce explicit module prefix in `Require` statements for non-Coq
   packages, to avoid ambiguity (@corwin-of-amber)
 - Init options for finer control of jsCoq's behavior: `show`, `focus`,
   `replace`, and `init_import` (@corwin-of-amber)
 - Line numbers continue across code snippets on the same page. Useful
   for `coqdoc`-generated pages (@corwin-of-amber)
 - Accept dropped `.coq-pkg` files as packages to add to the current
   session (@corwin-of-amber)
 - Allow multiple directories for package files (@corwin-of-amber)

## JsCoq 0.11.1

 - Bump js_of_ocaml to 3.6.0 (@ejgallego)
 - More accurate error location marker (@corwin-of-amber)

# JsCoq 0.10 "((())((()()(()))((()()))))"
-----------------------------------------

 - Use Dune as build system (@ejgallego @corwin-of-amber)
 - Port to Coq 8.10 (@ejgallego)
 - Miscellaneous improvements on the build system (@corwin-of-amber)
 - [bugfix] Error with goCursor + active error stms (@corwin-of-amber)
 - Goal display improvements using code from serlib (@ejgallego, @corwin-of-amber)
 - Improvements on printing of feedback messages (@corwin-of-amber)
 - Preliminary support for .vo compilation (@corwin-of-amber)
 - Bind Ctrl-Space to auto-completion (@corwin-of-amber)
 - Workaround JSOO problem with `Lazy` (@corwin-of-amber)
 - [bugfix] Contention in autocomplete between company-coq and Tex-input (@corwin-of-amber)
 - Simple UI for compiling pure-Coq projects in the browser (@corwin-of-amber, in-progress)
 - Timeout support and worker reset button (@corwin-of-amber)
 - Splash image (@corwin-of-amber)
 - [bugfix] Scrolling issue with special symbols in company-coq (@corwin-of-amber)
 - A scratchpad - a page with just an empty editor (@corwin-of-amber)
 - Open/save file dialogs that support local persistence (in the browser) and files (@corwin-of-amber)
 - Asynchronous document management to circumvent various race conditions (@corwin-of-amber)
 - Use serlib for serialization of Coq datatypes to JSON (@ejgallego)
 - New query `Ast` which does return a traversable Ast representation (@ejgallego)
 - NPM package build for publishing (@corwin-of-amber)
 - New layout using CSS flexbox (@corwin-of-amber)
 - Button to interrupt long-running tactics (@corwin-of-amber)
 - Decentralized build mode for addons (@corwin-of-amber)
 - [feature] Setting Coq options through jsCoq configuration argument (#108 @corwin-of-amber)

  Released on: 2020/01/27

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
  - [x] Port to JSOO 3.4.0. (@ejgallego @corwin-of-amber)
  - [x] Workaround https://github.com/ocsigen/js_of_ocaml/issues/772 (@corwin-of-amber)
  - [x] Performance and usability improvements to company-coq mode (@corwin-of-amber)

  Released on: 2019/04/23

# JsCoq 0.8 "The most inefficient programming language ever designed"
-------------------------------------

  - Port to Ocaml 4.03.0.
  - Fast package loading using TypedArrays. (thanks @gasche @hhugo).
  - Many small fixes.

  Released on: 2016/06/13

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
