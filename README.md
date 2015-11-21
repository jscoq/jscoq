Run Coq in your browser!
------------------------

A [Coq](https://coq.inria.fr) Integrated Development Enviroment
running in the browser! Try it:

<https://x80.org/rhino-coq/>

The goal of this project is to open new UI/interaction possibilites,
and to improve the acessibility of the platform itself.

Coq 8.5 is compiled to javascript using `js_of_ocaml` compiler, no
servers or external programs are needed. JsCoq runs fine in Chrome (>=
45) or Mozilla Firefox. It also runs in my old Galaxy Nexus.

* **Important:** Libraries are fully qualified, so you need to do `Require Import Coq.List.Lists", etc...
* **Important:** The project is pretty much at pre-alpha technology demo, you are welcome to use it but expect trouble.

## API

The current release provides a `coqManager` javascript object, so you can
embed Coq in your particular javascript application.

We are sorry we are scarce on documentation for now, but a look to
`newide.html` should give you an idea on to use jsCoq in your own
html pages.

## Reporting Bugs ##

Feel free to use the issue tracker. Please include your
browser/OS/user-agent and command line options.

We don't consider the code/architecture stable yet, but any
contribution or comment is really welcome!

## What is broken ##

* Loading ML modules may be slow if not using the bytecode cache.
* `vm_compute` and `native_compute` are not supported.
* There surely are threading and performance problems.

## Contact & Sponsorship ##
![FEEVER Logo](/images/feever-logo.png?raw=true "Feever Logo")

jsCoq has been make possible thanks to funding by the [FEEVER](http://feever.fr) project.

Contact: Emilio J. Gallego Arias `e+jscoq at x80.org`.

## How to Install/Build ##

* _warning_: The build process takes more than 8GiB of RAM.
* First, you need a dual 32/64 bits Ocaml toolchain. Get a
  recent opam and a multiarch gcc (`gcc-multilib` package in
  Debian/Ubuntu), then run:

  ````
$ cp -a opam/4.02.3+32bit ~/.opam/compilers/4.02.3/
$ git clone https://github.com/ocsigen/js_of_ocaml.git ~/external/js_of_ocaml
$ ./toolchain-setup.sh
  ````

  and it should do the trick.

  If your copy of js_of_ocaml is in a different location, edit the setup
  script and set the JS_OF_OCAML_DIR variable appropriately. Tweaking the NJOBS
  variable may be necessary too (64 jobs by default).

* Second, you need to build Coq trunk/master:

  ````
$ git clone https://github.com/coq/coq.git ~/external/coq-git
$ cd ~/external/coq-git
$ opam switch 4.02.3+32bit
$ eval `opam config env`
$ ./configure -local -natdynlink no -coqide no -native-compiler no
$ make               # use -j N as desired
  ````

  If you want to use a different location for Coq, edit the `COQDIR` variable in JsCoq's `Makefile`.

  We recommend to edit $(COQDIR)/theories/Init/Prelude.v and comment
  out the extraction and recdef plugins, they take long time to
  compile.
* You may want to select what libraries get
  included. `coq-tools/dftlibs.ml` allows you to do that.

* Finally:

  ````
$ ./build.sh
  ````

  should build jscoq. The script tries to manage the pain of the 32/64
  bit switch, you can also use make if you know what you are doing.

* To run jscoq in locally you may need to start your browser as:

  ````
$ google-chrome-beta --allow-file-access-from-files --js-flags="--stack-size=65536" index.html
  ````

* _Bytecode cache_:
  By default JsCoq must compile ocaml's bytecode to javascript
  on the fly to load cma plugins.

  However, this process can be cached by creating a bcache. The
  process is a bit involved. First, you must load all the .cma files
  from a regular web browser, so they get compiled and cached. Then
  call the `dumpCache` function from the JS console to download the
  cache, which must be then processed using the
  `coq-tools/byte_cache.js` program to generate a `/bcache.list` file
  and a `/bcache` directory.
* Profit!
* Extra/Experimental: ssreflect.

  Get the ssreflect distribution at
  `git://scm.gforge.inria.fr/coq-contribs/ssreflect`. Then build with:

  ```
$ # Patch ssr if needed.
$ opam switch 4.02.3+32bit
$ eval `opam config env`
$ export PATH=~/external/coq-git/bin:$PATH
$ coq_makefile -f Make > Makefile
$ make byte
  ```

  For current Coq v8.5, you need to patch ssr [look in the patch folder].
