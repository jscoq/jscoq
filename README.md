Run Coq in your browser using JavaScript
----------------------------------------

A proof-of-concept implementation of a Coq REPL running in the
browser. Note that the whole Coq stack runs in the browser, we do this
using the amazing `js_of_ocaml` Ocaml bytecode to javascript compiler.

The shell is basically a modification of the
[js\_of\_ocaml](http://ocsigen.org/js_of_ocaml/) toplevel, linked to
Coq.

Surprisingly, it runs when linked against an unpatched coq
trunk. However a few things are still broken, see below.

See it by yourself <https://x80.org/rhino-coq/>.

**Note about the code**

Don't expect too much of the code, it is a mess written by a person
with zero knowledge of Javascript, Coq internals, and Ocaml.

The goal was to do a proof of concept and get things running. However,
I hope it evolves into a fully-working Coq setup.

## What is broken ##

Plugin and module loading are broken. They will likely be fixed during
the Coq Coding Sprint.

`vm_compute` and `native_compute` don't work either.

The rest seems to be working.

## Contact ##

Emilio J. Gallego Arias <e+jscoq@x80.org>

## How to Install ##

* Setup Ocaml 4.02 and Opam.
* Install the following opam packages: `reactiveData tyxml`
* Install js\_of\_ocaml <http://ocsigen.org/js_of_ocaml/> from git.
* Download and build Coq trunk from <https://github.com/coq/coq>, configure as:

        $ ./configure -local -natdynlink no -coqide no -byteonly
        $ make -j

* Edit `COQDIR` in the `Makefile` to point to the directory where the Coq build is.
* Type:

        $ make

  and profit!

We also support building a coqtop.js executable that can be run using
the `nodejs` command line implementation, or linked with atom.

* Apply the `coqtop.patch` to Coq source code.
* `$ make coqtop.js`
* `$ nodejs coqtop.js`
  Profit!
