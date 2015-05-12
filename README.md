Run Coq in your browser!
------------------------

This is a proof-of-concept implementation of a Coq REPL running in the
browser.

Note that the whole of Coq runs in the browser, using the great
`js_of_ocaml` Ocaml bytecode to javascript compiler.

The shell is a modification of the
[js\_of\_ocaml](http://ocsigen.org/js_of_ocaml/) toplevel, linked to
Coq.

Surprisingly, it mostly works when linked against an unpatched Coq
trunk. Unfortunately, loading modules is still broken, see below.

Try it by yourself <https://x80.org/rhino-coq/> !

_Remember that you'll get a barebones Coq shell, without notations or
libraries loaded, you can paste almost any file however._

**A note about the code**

The code is a mess written by a person with zero knowledge of
Javascript, and Coq internals, and only a slight idea of Ocaml.
The goal of this project was to do a proof of concept and get things
running.

However, I hope it can evolve into a fully-working Coq setup and IDE.

## What is broken ##

Plugin and module loading don't work. They will likely be fixed in the
Coq Coding Sprint. `vm_compute` and `native_compute` aren't supported
either. The threading library is a stub.

No other issues for now.

## Contact ##

Emilio J. Gallego Arias `e+jscoq at x80.org`.

## How to Install ##

* Install Ocaml 4.02 and Opam.
* Install the following opam packages: `derive reactiveData tyxml`
* Install js\_of\_ocaml <http://ocsigen.org/js_of_ocaml/> from git.
* Download and build Coq master from <https://github.com/coq/coq>, configure and make as follows:

        $ ./configure -local -natdynlink no -coqide no -byteonly -no-native-compiler
        $ make -j
* Edit `COQDIR` in `Makefile` to point to the directory where you have just built Coq.
* Type:
        $ make
  and profit!

We also support building a coqtop.js executable that can be run using
`node`, linked with atom, etc...

* Apply `coqtop.patch` to Coq source code, then:
        $ make coqtop.js
        $ nodejs coqtop.js
  and profit again!
