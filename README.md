Run Coq in your browser!
------------------------

This project allows you to build a Coq toplevel that will fully run in
the browser, using the `js_of_ocaml` compiler.

Chrome dev (45) is basically mandatory for now. Mozilla Firefox seems to
work fine too, but has some problems due to a small stack default size.

In order to load large plugins, Chrome must be told to increase the
stack size: `google-chrome --js-flags="--stack-size=65536"`. Unfortunately, there's no way to do
this in Firefox.

It also runs in my old Galaxy Nexus, but it has performance problems
due to the Chrome version on it (43).

Try it: <https://x80.org/rhino-coq/> !

[Warning: I use that URL to distrubute all kind of weird
experiments. Rememeber, this is still alpha software, we will provide
a more stable link soon.]

The basic Coq toplevel is a minimal modification of the
[js\_of\_ocaml](http://ocsigen.org/js_of_ocaml/) one, but the plan is
to evolve to an IDE more tailored to Coq.

## Reporting Bugs ##

Feel free to use the issue tracker. Please include your
browser/OS/user-agent and command line options.

For now the code is a mess, we have focused on getting the thing
running, but we are working on rewriting it now. Thus, IMHO, pull
requests don't make sense yet, but any other contribution or comment
is really welcome!

## What is broken ##

Loading ML modules is quite slow due to dynamic
compilation. Performance is bad in Chrome 43, 44.

`vm_compute` and `native_compute` are not supported. There may be
threading and performance problems.

## Contact ##

Emilio J. Gallego Arias `e+jscoq at x80.org`.

## How to Install ##

* First you need to build a dual 32/64 bits Ocaml toolchain. You need a
  recent opam system and a multiarch gcc (`gcc-multilib` package in
  Debian/Ubuntu), then run:
````
$ git clone https://github.com/ocsigen/js_of_ocaml.git ~/external/js_of_ocaml
$ ./toolchain-setup.sh
````
  and that should do the trick.

  If your copy of js_of_ocaml is in a different location, edit the setup
  script and set the JS_OF_OCAML_DIR variable appropriately. Tweaking the NJOBS
  variable may be necessary too (64 jobs by default).
* Second, you need to build Coq trunk/master:
````
$ git clone https://github.com/coq/coq.git ~/external/coq-git
$ cd ~/external/coq-git
$ opam switch 4.02.1+32bit
$ eval `opam config env`
$ ./configure -local -natdynlink no -coqide no -byteonly -no-native-compiler
$ make               # use -j N as desired
````
  If you want to use a different location for Coq, edit the `COQDIR` variable in JsCoq's `Makefile`.
* You may want to select what libraries get included. `jslib.ml` allows
  you to do that. For now we recommend editing
  $(COQDIR)/theories/Init/Prelude.v and comment out the extraction
  and recdef plugins, as they take long time to compile.
* Finally:
````
$ ./build.sh
````
  should build jscoq. The script tries to manage the pain of the 32/64
  bit switch, but you can also use make if you know what you are doing.
* In order to use a browser locally you may need to start it as:
````
$ google-chrome-unstable --allow-file-access-from-files --js-flags="--stack-size=65536" index.html
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
