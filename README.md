Run the Coq Proof Assistant in your browser!
------------------------

jsCoq is an Online Integrated Development Environment
for the [Coq](https://coq.inria.fr) proof assistant and runs in your browser! Try it:

<https://x80.org/rhino-coq/>

The goal of this project is to open new UI/interaction possibilites,
and to improve the acessibility of the platform itself.

We support Chrome (>= 48) and Firefox (>= 45). JsCoq is written in
ES2015, thus any standard-compliant browser should work.
JsCoq also runs in my 4-years old Galaxy Nexus.

Coq is compiled to javascript using the `js_of_ocaml` compiler. No
servers or external programs are needed.
We want to **strongly thank** the `js_of_ocaml` developers. Without
their great and quick support jsCoq wouldn't have been possible.

**Important:** The Coq standard libraries are qualified in jsCoq, thus
you need to prefix your imports:

```coq
Require Import Lists.
```
becomes
```coq
From Coq Require Import List.Lists.
```

#### Development version

The preview release of jsCoq 0.9 for Coq 8.6 is available at:

<https://x80.org/rhino-trunk/>

See below for different versions, including a HoTT-enabled one.

### Collacoq

A small pastebin-like server based on haste is available at
https://x80.org/collacoq

Note that this is totally experimental, data loss is guaranteed.

See also the branch at https://github.com/ejgallego/haste-server/tree/collacoq

Help with Collacoq is very welcome!

## API / How to embed in your own webpage

JsCoq provides a `coqManager` javascript object for embedding Coq in
your particular application, blog, or webpage. The basic pattern to
add jsCoq to webpage with Coq code is:

```javascript
  <script src="$path/js/jscoq-loader.js" type="text/javascript"></script>
  <script type="text/javascript">
    loadJsCoq($path).then( () => new CoqManager ($list_of_ids, [$options]) );
  </script>
```

where `$path` is the path the jsCoq distribution, `$list_of_ids` is
the list of textareas that will form the Coq document. See below for
available `$options`.

The jsCoq (landing webpage)[newide.html] is a good actually running example.

### Options

JsCoq accepts the following options as an optional second parameter to
the constructor:

* `base_path`: Path where jsCoq is installed.
* `wrapper_id`: id of the div where to attach the panel.
* `all_pkgs`, `init_pkgs`: List of Coq's packages to show/preload.
* `prelude: bool`: Whether to load Coq's prelude or not.
* `mock: bool`: Use a mock jsCoq object, useful for prototyping.

### Examples

The main page includes a proof of the infinitude of primes by
G. Gonthier. We provide some more examples as a showcase of the tool:

- dft.v: https://x80.org/rhino-coq/examples/dft.html

  A small development of the theory of the Fourier Transform following
  Julius Orion Smith III's "The Mathematics of the Discrete Fourier
  Transform"

- Mtac: The Mtac tutorial by Beta Zilliani:

  https://x80.org/rhino-coq/examples/mtac_tutorial.html

- Stlc: The "Simply Typed Lambda Calculus" chapter from Software
  Foundations by Benjamin Pierce et al:

  https://x80.org/rhino-coq/examples/Stlc.html

- StackMachine: The First chapter of the book "Certified Programming
  with Dependent Types" by Adam Chlipala:

  https://x80.org/rhino-coq/examples/Cpdt.StackMachine.html

- MirrorCore:
  - A simple demo:
    https://x80.org/rhino-coq/examples/mirrorcore.html
  - A demo of developing a cancellation algorithm for commutative
    monoids:
    https://x80.org/rhino-coq/examples/mirror-core-rtac-demo.html

### Homotopy Type Theory

jsCoq supports the HoTT library which requires a special build of Coq,
an online version is at: https://x80.org/rhino-hott/

### Serialization

JsCoq will support serialization to Json or Sexps for Coq's internal
data structures, but this effort has been split to an independent
development. See https://github.com/ejgallego/coq-serapi for more
information.

### CoqDoc

A coqdoc replacement that is better suited to produce jsCoq output
while (mostly) remaining compatible is being developed at
https://github.com/ejgallego/udoc

It works kind of OK for converting coqdoc files, but it produces some
artifacts and omits some declarations.

There is also a superseded experimental version of coqdoc outputting
jsCoq at https://github.com/ejgallego/coq/tree/coqdoc

Just build coqdoc normally and use the option `--backend=jscoq`.

## Mailing List ##

You can subscribe to the jsCoq mailing list at:

https://x80.org/cgi-bin/mailman/listinfo/jscoq

The list archives should be also available through Gmane at group:

`gmane.science.mathematics.logic.coq.jscoq`

you can post to the list using nntp.

## Troubleshooting ##

* Clearing the browser cache may solve lots of issues.
* Consider using `--js-flags="--stack-size=65536"` in Chrome if you get `StackOverflows`.

## Contributing ##

This is certainly an alpha-status project, but any contribution or
comment is really welcome! Please submit your pull request for review
to the mailing list using `git request-pull`. You can also submit a
github PR, but it is not guaranteed that we'll look into it.

## Reporting Bugs ##

Feel free to use the issue tracker. Please include your
browser/OS/user-agent and command line options.

## CodeMirror ##

[CodeMirror](https://codemirror.net/) has played a crucial role in the
project, we are very happy with it, thanks a lot!

Please consider supporting the development of CodeMirror with a donation.

## What is broken ##

* Loading ML modules is slow.
* Loading `.vo` files is slow.
* `vm_compute` and `native_compute` are not supported.
* There surely are threading and performance problems.

## Contact & Sponsorship ##

![FEEVER Logo](/images/feever-logo.png?raw=true "Feever Logo")

jsCoq has been make possible thanks to funding by the [FEEVER](http://feever.fr) project.

Contact: Emilio J. Gallego Arias `e+jscoq at x80.org`.

## jsCoq Users:

Incomplete list of places where jsCoq has been used:

* Coq Winter School 2016: “Advanced Software Verification And Computer Proof”. _Sophia Antipolis_
  https://team.inria.fr/marelle/en/advanced-coq-winter-school-2016/
* Mathematical Components, an Introduction, _Satellite workshop of the ITP 2016 conference_, August 27th, Nancy, France
  https://github.com/math-comp/wiki/wiki/tutorial-itp2016

### jsCoq in the press

- http://www.mines-paristech.fr/Actualites/jsCoq-ou-Coq-dans-un-navigateur/2118
- https://news.ycombinator.com/item?id=9836900

## How to Install/Build ##

You can download ready-to-use builds from
https://github.com/ejgallego/jscoq-builds/ ; find below the
instructions to build JsCoq yourself.

* _warning_: The build process may take *more* than 8GiB of RAM.
* First, you need a dual 32/64 bits Ocaml toolchain. Get a
  recent opam and a multiarch gcc (`gcc-multilib` package in
  Debian/Ubuntu), then run:

  ```
$ cp -a opam/4.03.0+32bit ~/.opam/compilers/4.03.0/
$ ./toolchain-setup.sh
  ```

  and it should do the trick.

  You can tweak some variables in the `build-common.sh` file.

* Second, you need to build Coq v8.6:

  ```
$ git clone https://github.com/coq/coq.git ~/external/coq-git-32
$ cd ~/external/coq-git-32
$ git checkout v8.6 # Or trunk at this moment.
$ opam switch 4.03.0+32bit
$ eval `opam config env`
$ ./configure -local -coqide no -native-compiler no
$ make               # use -j N as desired
  ```

  jsCoq is compatible with vanilla Coq v8.6. However, we maintain a
  tree with some specific patches at
  https://github.com/ejgallego/coq/tree/jscoq-patchqueue

* You must checkout jsCoq git submodules:

  ```
$ git submodules update --remote
  ```

* Adjust build parameters in `config.mk`.

  If you want to use a different location for the Coq sources, edit
  the `COQDIR` variable, `ADDONS` will select what libraries get
  included. See the file for more paremeters.


* Finally:

  ```
$ ./build.sh
  ```

  should build jscoq. The script tries to manage the pain of the 32/64
  bit switch, you can also use make if you want finer control.

* To run jscoq in locally you may need to start your browser as:

  ```
$ google-chrome-beta --allow-file-access-from-files --js-flags="--stack-size=65536" index.html
  ```

* Profit!

### Building Addon Packages:

  JsCoq supports many extra addons, including ssreflect. Package
  download and building is still not very streamlined. External
  packages are built into jscoq in two steps:

  - Building the package itself with the Coq version linked to jsCoq.
  - Generating the package files for jsCoq.

  The first step can be taken care of by the `Makefile.addons` makefile.

  ```
$ opam switch 4.03.0+32bit
$ eval `opam config env`
$ export PATH=~/external/coq-git-32/bin:$PATH
$ make -f Makefile.addons $TARGET
  ```

  You will need to adjust the makefile to point out the location of
  the packages, most of them are assumed to live in `~/external/coq/$package`.

  For the second step, edit the `config.mk` file to select the
  packages you want to install, and call `./build.sh` again.

  A patch optimizing mathcomp loading times can be found in the patch
  folder, highly recommended.

## Commit tag conventions [work in progress]:

- [jscoq]: ML/Coq interface.
- [ui]: Html/Css commit
- [cm]: CodeMirror provider.
- [libs]: Coq Library support and format.
- [doc]: Documentation.
- [addons]: Addons support.
- [build]: Build system.

## Documents

See the `notes/` directory for some random notes about the project.
