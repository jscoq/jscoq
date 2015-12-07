Run Coq in your browser!
------------------------

A [Coq](https://coq.inria.fr) Online Integrated Development Environment
running in the browser! Try it:

<https://x80.org/rhino-coq/>

The goal of this project is to open new UI/interaction possibilites,
and to improve the acessibility of the platform itself.

Coq 8.5 is compiled to javascript using `js_of_ocaml` compiler, no
servers or external programs are needed. JsCoq runs fine in Chrome (>=
45) or Mozilla Firefox. It also runs in my old Galaxy Nexus.

* **Important:** Libraries are fully qualified, so you need to do `Require Import Coq.List.Lists", etc...
* **Important:** The project is pretty much at pre-alpha technology demo, you are welcome to use it but expect trouble.

## API / How to use

The current release provides a `coqManager` javascript object, so you can
embed Coq in your particular javascript application. The basic use is:

````
  <script type="text/javascript">
   var coq = new CoqManager (['addnC', 'prime_above']);
  </script>
```

But it requires some particular UI classes present in the document for
now. Look at `newide.html` to get more an idea on how to use jsCoq in
your own html pages.

Coqdoc can also be used to generate jsCoq documents, we are publish a
patched coqdoc here soon.

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

* Second, you need to build Coq v8.5:

  ````
$ git clone https://github.com/coq/coq.git ~/external/coq-git
$ cd ~/external/coq-git
$ git checkout v8.5
$ opam switch 4.02.3+32bit
$ eval `opam config env`
$ ./configure -local -coqide no -native-compiler no
$ make               # use -j N as desired
  ````

  Note that jsCoq is currently broken by commit
  coq/coq@3940441dffdfc3a8f968760c249f6a2e8a1e0912 , please use
  coq/coq@ef8718a7fd3bcd960d954093d8c636525e6cc492 or apply the patch
  in the patch folder which provides a workaround (the issue is not
  fully solved).

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

  By default JsCoq must compile ocaml's bytecode to javascript on the
  fly to load cma plugins.  However, we can cache the process of
  compilation by creating a bcache. The process is a bit involved:

  1) Load all the .cma files you want to be cached from a regular web
     browser, they will get compiled and cached.

  2) Call the `dumpCache()` function from the JS console; this should
     download the cache.

  3) Place the files in the `jscoq` directory, and do `make
     bcache`. The cache will be then processed using the
     `coq-tools/byte_cache.js` program to generate a `/bcache.list`
     file and a `/bcache` directory.

     This requires node.

* Profit!
* Packages: ssreflect/mathcomp.

  JsCoq supports extra addons, including ssreflect. In order to build
  it with JsCoq, download the ssreflect distribution from
  `https://github.com/math-comp/math-comp`

  Go to the main directory and then build with:

  ```
$ opam switch 4.02.3+32bit
$ eval `opam config env`
$ export PATH=~/external/coq-git/bin:$PATH
$ make
  ```

  You need to specify in the jsCoq makefile the place where math-comp
  has been downloaded, `~/external/coq/math-comp` is the default.

  A patch optimizing mathcomp loading times can be found in the patch
  folder, highly recommended. Also, some parts don't seem to build
  with 8.5, so this process can be a bit too manual as of now.
