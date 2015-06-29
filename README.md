Run Coq in your browser!
------------------------

Here you can find a proof-of-concept implementation of a Coq Toplevel
suited to run in the browser. Not only the toplevel runs inside the
browser, but Coq does too, by the magic of the `js_of_ocaml` bytecode
to javascript compiler.

For now we support a basic shell (modified from
[js\_of\_ocaml](http://ocsigen.org/js_of_ocaml/), and Google
Chromium/Chrome. It also runs in my old Galaxy Nexus.

Try it: <https://x80.org/rhino-coq/> !

**A note about the code**

The code is a mess, consequence of my low Javascript/Coq internals
knowledge and of the experimental nature of the project. We will
improve it, but please don't submit code-cleanup issues for now.

## What is broken ##

Loading ML modules is quite slow due to dynamic
compilation. Performance is quite bad (specially in unification,
matching and ltac).

`vm_compute` and `native_compute` are not supported either. There may
be threading problems.

## Contact ##

Emilio J. Gallego Arias `e+jscoq at x80.org`.

## How to Install ##

* First you need to build a dual 32/64 bits toolchain. If you have a
  recent opam system and a multiarch gcc (`gcc-multilib` package in
  Debian/Ubuntu), running:
````
$ git clone https://github.com/ocsigen/js_of_ocaml.git ~/external/js_of_ocaml
$ toolchain-setup.sh
````
  should take care of it.

  If your copy of js_of_ocaml is in another location, editing the
  script and set JS_OF_OCAML_DIR appropriately. Tweaking the NJOBS
  variable may be necessary too.
* Second, you need to download and build Coq master:
````
$ git clone https://github.com/coq/coq.git ~/external/coq-git
$ pushd ~/external/coq-git
$ opam switch 4.02.1+32bit
$ ./configure -local -natdynlink no -coqide no -byteonly -no-native-compiler
$ make # -j as desired
$ popd
````
  Editing $(COQDIR)/theories/Init/Prelude.v and commenting out the
  extraction and recdef is recommended for now.

  If you want to use a different location for Coq, edit `COQDIR` in JsCoq `Makefile`.
* Finally
````
$ ./build.sh
````
  should build jscoq. The script tries to manage the pain of the 32/64
  bit switch, you can also use make if you know what you are doing.
* In order to use a browser locally you may need to start it as:
````
$ chromium-browser --allow-file-access-from-files index.html
````
* Profit!
* We used to support building a coqtop.js executable, to be run with
  `node`, linked with atom, etc...

  `coqtop.patch` contains the old patch in case you are interested:
````
$ make coqtop.js
$ nodejs coqtop.js
````
  used to work.
