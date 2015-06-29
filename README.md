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

The code is a mess, written by a person with no knowledge of
Javascript, Coq internals, and only a slight idea of Ocaml, but it
will improve. Please don't submit code-cleanup issues for now.

## What is broken ##

`vm_compute` and `native_compute` don't work. Performance
is quite bad (specially in unification, matching and ltac). The
threading library is a stub.

## Contact ##

Emilio J. Gallego Arias `e+jscoq at x80.org`.

## How to Install ##

Due to javascript limitations (no support for 64 bits integeres) and
high memory demands of the js_of_ocaml optimizer we need to use a
32bit and 64bit Ocaml runtime.

* The provided script `toolchain-setup.sh` will take care of most
  things provided you have a recent opam.

  You should modify it to point to a git version of js_of_ocaml by
  editing the JS_OF_OCAML_DIR variable, also tweaking NJOBS may be
  necessary. In Ubuntu, the gcc-multilib package is required.

* Download and build Coq master from <https://github.com/coq/coq>, configure and make as follows:

````
$ opam switch 4.02.1+32bit
$ ./configure -local -natdynlink no -coqide no -byteonly -no-native-compiler
$ make # -j as desired
````

  A tip is to edit $(COQDIR)/theories/Init/Prelude.v and comment out extraction_plugin & recdef_plugin.

* Edit `COQDIR` in `Makefile` to point to the directory where Coq is.

* Typing
        $ ./build.sh

  should do the trick. build.sh tries to manage the pain of the 32/64
  bit switch, you can also use regular make if you know what you are doing.

  In order to use a browser with the file protocol you may want to start it as:
        $ chromium-browser --allow-file-access-from-files

  Profit!

We also used to support building a coqtop.js executable that can be run using
`node`, linked with atom, etc...

* Apply `coqtop.patch` to Coq source code, then:

        $ make coqtop.js
        $ nodejs coqtop.js
  and profit again!
