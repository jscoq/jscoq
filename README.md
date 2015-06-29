Run Coq in your browser!
------------------------

A proof-of-concept implementation of a Coq Toplevel running in the
browser.

Note that the whole of Coq runs in the inside the browser, we use the
`js_of_ocaml` Ocaml bytecode to javascript compiler to make this happen.

For now we support a very basic shell, basically a small modification
of the [js\_of\_ocaml](http://ocsigen.org/js_of_ocaml/) toplevel,
linked to Coq.

Try it by yourself <https://x80.org/rhino-coq/> !

**A note about the code**

The code is a mess, written by a person with zero knowledge of
Javascript, Coq internals, and only a slight idea of Ocaml, but it
will improve. Please don't submit code-cleanup issues for now.

## What is broken ##

`vm_compute` and `native_compute` aren't supported either. Performance
is terrible (specially in unification, matching and ltac). The
threading library is a stub.

## Contact ##

Emilio J. Gallego Arias `e+jscoq at x80.org`.

## How to Install ##

Unfortunately, due to javascript limitations you need both a 32bit and
64bit Ocaml runtime.

* First, install Ocaml 4.02.0 both in 32 and 64 bit
  versions. [opam-compiler-conf](https://github.com/gasche/opam-compiler-conf)
  could be useful for that.

* Install the following opam packages in both runtimes:

        opam install ocamlfind camlp4 camlp5 base64 cppo ppx_tools higlo ocp-indent tyxml js_of_ocaml reactiveData

* Install js\_of\_ocaml <http://ocsigen.org/js_of_ocaml/> from git in both runtimes.

* Download and build Coq master from <https://github.com/coq/coq>, configure and make using 32bit ocaml:

        $ ./configure -local -natdynlink no -coqide no -byteonly -no-native-compiler
        $ make
* Edit `COQDIR` in `Makefile` to point to the directory where you have just built Coq.
* Type:

        $ make

  in the 32bit runtime. js_of_ocaml will fail due to needing 8Gb of
  memory to optimize the coq bytecode. Switch to the 64 bit runtime
  and make again, it will succeed.

  Preprocessing the libraries is still to be added to the makefile.

We also used to support building a coqtop.js executable that can be run using
`node`, linked with atom, etc...

* Apply `coqtop.patch` to Coq source code, then:

        $ make coqtop.js
        $ nodejs coqtop.js
  and profit again!
