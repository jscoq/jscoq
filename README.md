Run Coq in your browser!
------------------------

A proof-of-concept implementation of a Coq Toplevel running in the
browser. Note that we only support recent Chromium versions for the moment.

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

* First, you have to install Ocaml 4.02.0 both in 32 and 64 bit
  versions. [opam-compiler-conf](https://github.com/gasche/opam-compiler-conf)
  is very useful for that, see [this
  issue](https://github.com/gasche/opam-compiler-conf/issues/7) on how
  to use it to build a 32bit ocaml].

  Once built, edit `build.sh` to indicate the names of your opam switches, example:

        OCAMLDIST64=4.02.0+local-git-emilio-local
        OCAMLDIST32=4.02.0+local-git-32-emilio-local

* Install the following opam packages in both runtimes:

        opam install ocamlfind camlp4 camlp5 base64 cppo ppx_tools higlo ocp-indent tyxml js_of_ocaml reactiveData

* Install js\_of\_ocaml <http://ocsigen.org/js_of_ocaml/> from git in
  both runtimes. You'll need to issue a make uninstall first.

* Download and build Coq master from <https://github.com/coq/coq>, configure and make using 32bit ocaml:

        $ ./configure -local -natdynlink no -coqide no -byteonly -no-native-compiler
        $ ./build.sh

* Edit `COQDIR` in `Makefile` to point to the directory where you have just built Coq.

* Type:
        $ ./build.sh

  build.sh tries to manage the pain of the 32/64 bit switch, you can also use make if you know what you are doing.

  Preprocessing the libraries so they can be loaded is still to be
  added to the makefile, sorry.

We also used to support building a coqtop.js executable that can be run using
`node`, linked with atom, etc...

* Apply `coqtop.patch` to Coq source code, then:

        $ make coqtop.js
        $ nodejs coqtop.js
  and profit again!
