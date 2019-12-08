Run the Coq Proof Assistant in your browser!
------------------------

[![Build Status](https://travis-ci.org/ejgallego/jscoq.svg?branch=v8.11)](https://travis-ci.org/ejgallego/jscoq) [![Gitter](https://badges.gitter.im/jscoq/Lobby.svg)](https://gitter.im/jscoq/Lobby)

jsCoq is an Online Integrated Development Environment for the
[Coq](https://coq.inria.fr) proof assistant and runs in your browser!
We aim to enable new UI/interaction possibilities and to improve the
accessibility of the Coq platform itself. Current stable version is
jsCoq v8.11+0.11.0~beta supporting Coq 8.11, try it:

<https://jscoq.github.io>

JsCoq is written in ES2017, thus any recent standard-compliant browser
should work. jsCoq also runs in my 8-year old Galaxy Nexus. Browser
performance is quite variable these days, see the [Troubleshooting](#Troubleshooting) section if you have problems.

Coq is compiled to JavaScript using the [`js_of_ocaml`](http://ocsigen.org/js_of_ocaml) compiler. No
servers or external programs are needed.
We want to _strongly thank_ the `js_of_ocaml` developers. Without
their great and quick support jsCoq wouldn't have been possible.

## Are you a jsCoq user?

Have you developed a course **using jsCoq**? If so, please submit a
pull request or an issue so we can add your lectures to the list of
[jsCoq users](#jsCoq-Users) This is essential to guarantee future
funding of the project.

## Basic Usage

The main page showcases jsCoq by walking through a proof for the infinitude of primes using
[`math-comp`](https://github.com/math-comp/math-comp), due to Georges Gonthier.
Once jsCoq finishes loading, you can step through the proof using the arrow buttons on the toolbar (top right),
or using these keyboard shortcuts:

| Shortcut           | Action           |
|--------------------|------------------|
| Alt-N or Alt-↓     | Go to next       |
| Alt-P or Alt-↑     | Go to previous   |
| Alt-Enter or Alt-→ | Go to cursor     |

You can open a blank editor and experiment with your own Coq developments using the
[scratchpad](https://jscoq.github.io/node_modules/jscoq/examples/scratchpad.html).
The same keyboard shortcuts apply here.

The scratchpad's contents are saved in your browser's local storage (IndexedDB, specifically),
so they are not lost if you close the browser window or refresh the page.
You can, in fact, store more than one document using the local open/save file dialogs:

| Shortcut           | Action                                                        |
|--------------------|---------------------------------------------------------------|
| Ctrl-S             | Save file (with the last name provided, or `untitled.v`)      |
| Ctrl-Shift-S       | Save file as (prompts for file name)                          |
| Ctrl-O             | Open file (prompts for file name, supports tab completion)    |
| Ctrl-Alt-O         | Open file from disk (using the browser's Open dialog)         |

On Mac, replace Ctrl with ⌘ (command) and Alt with ⌥ (option), as is traditional.

## Development Version

Development for jsCoq 0.11 takes place in the `v8.11` branch. A
preview build of jsCoq 0.11 is usually available at:

<https://x80.org/rhino-coq/v8.11/>

jsCoq is easy to develop using the Chrome developer tools; the jsCoq
object has a `debug` flag, and it is possible to compile Coq with
debug information by setting the makefile variable `JSCOQ_DEBUG=yes`.

Previous Coq versions can be accessed at:

- <https://x80.org/rhino-coq/v8.10/>
- <https://x80.org/rhino-coq/v8.9/>
- <https://x80.org/rhino-coq/v8.8/>
- <https://x80.org/rhino-coq/v8.7/>
- <https://x80.org/rhino-coq/v8.6/>
- <https://x80.org/rhino-coq/v8.5/>

## Publications

A paper describing the ideas behind jsCoq has been published in the
proceeding of the [UITP 2016 workshop](http://www.informatik.uni-bremen.de/uitp/current/). The
paper is available from the open access
[EPTCS](http://eptcs.web.cse.unsw.edu.au/paper.cgi?UITP2016.2)
proceedings. The recommended citation is:

```bibtex
@Inproceedings{gallego:uitp2016,
  author    = {Gallego Arias, Emilio Jes\'us and Pin, Beno\^it and Jouvelot, Pierre},
  year      = {2017},
  title     = {{jsCoq}: Towards Hybrid Theorem Proving Interfaces},
  editor    = {Autexier, Serge and Quaresma, Pedro},
  booktitle = {{\rmfamily Proceedings of the 12th Workshop on} User Interfaces for Theorem Provers,
               {\rmfamily Coimbra, Portugal, 2nd July 2016}},
  series    = {Electronic Proceedings in Theoretical Computer Science},
  volume    = {239},
  publisher = {Open Publishing Association},
  pages     = {15-27},
  doi       = {10.4204/EPTCS.239.2},
  issn      = {2075-2180}
}
```

Some further ideas behind jsCoq are also discussed in
[SerAPI: Machine-Friendly, Data-Centric Serialization for COQ. Technical Report](https://hal-mines-paristech.archives-ouvertes.fr/hal-01384408)

## Collacoq

A small pastebin-like server based on haste is available at
https://x80.org/collacoq.
Note that this service is totally experimental, data loss is guaranteed.

See also the branch at https://github.com/ejgallego/haste-server/tree/collacoq
Help with Collacoq is very welcome!

## Troubleshooting

**Are you getting a `StackOverflow` exception?** Unfortunately these
are hard to fix; you may be stuck with them for a while.

* Clearing the browser cache usually solves lots of issues.
* Change browser, if using Firefox try Chrome, if using Chrome try Firerox.
* Consider using `--js-flags="--stack-size=65536"` in Chrome if you get `StackOverflows`.
* Use the `--js-flags="--harmony-tailcalls"` command line flag.
* Enable the `chrome://flags/#enable-javascript-harmony` flag if you get `StackOverflows`.

## API / How to embed in your own webpage

JsCoq provides a `coqManager` javascript object for embedding Coq in
your particular application, blog, or webpage. The basic pattern to
add jsCoq to webpage with Coq code is:

```javascript
  <script src="$path/ui-js/jscoq-loader.js" type="text/javascript"></script>
  <script type="text/javascript">
    loadJsCoq($path).then( () => new CoqManager ($list_of_ids, {$options}) );
  </script>
```

where `$path` is the path the jsCoq distribution, `$list_of_ids` is
the list of textareas that will form the Coq document. See below for
available `$options`.

The jsCoq [landing webpage](index.html) is a good running example.

### Options

JsCoq accepts the following options as an optional second parameter to
the `CoqManager` constructor:

| Key             | Type            | Default         | Description                                                                                                   |
|-----------------|-----------------|-----------------|---------------------------------------------------------------------------------------------------------------|
| `base_path`     | string          | `'./'`          | Path where jsCoq is installed.                                                                                |
| `wrapper_id`    | string          | `'ide-wrapper'` | Id of `<div>` element in which the jsCoq panel is to be created.                                              |
| `layout`        | string          | `'flex'`        | Choose between a flex-based layout (`'flex'`) and one based on fixed positioning (`'fixed'`).               |
| `all_pkgs`      | array of string | (see below)     | List of available packages that will be listed in the packages panel.                                         |
| `init_pkgs`     | array of string | `['init']`      | Packages to load at startup.                                                                                  |
| `prelude`       | boolean         | `true`          | Load the Coq prelude (`Coq.Init.Prelude`) at startup. (If set, make sure that `init_pkgs` includes `'init'`.) |
| `implicit_libs` | boolean         | `false`         | Allow `Require`ing modules by short name only (e.g., `Require Arith.`).                                       |
| `theme`         | string          | `'light'`       | IDE theme to use; includes icon set and color scheme. Supported values are `'light'` and `'dark'`.            |
| `file_dialog`   | boolean         | `false`         | Enables UI for loading and saving files (^O/^S, or ⌘O/⌘S on Mac).                                             |
| `editor`        | object          | `{}`            | Additional options to be passed to CodeMirror.                                                                |
| `coq`           | object          | `{}`            | Additional Coq option values to be set at startup.                                                            |

The list of available packages defaults to all Coq libraries and addons
available with the current version of jsCoq. At the moment, it is:
```js
['init', 'coq-base', 'coq-collections', 'coq-arith', 'coq-reals',  
 'math-comp', 'elpi', 'equations', 'ltac2',
 'coquelicot', 'flocq', 'lf', 'plf', 'cpdt', 'color']
```

The `editor` property may contain any option supported by CodeMirror
(see [here](https://codemirror.net/doc/manual.html#config)).

The `coq` property may hold a list of Coq properties mapped to their
values, and is case sensitive (see [here](https://coq.inria.fr/refman/coq-optindex.html)).
For example:
```js
{'Implicit Arguments': true, 'Default Timeout': 10}
```

## Examples

The main page includes a proof of the infinitude of primes by
G. Gonthier. We provide some more examples as a showcase of the tool:

- The Logical Foundations suite:
  + https://x80.org/rhino-coq/v8.9/examples/lf/
  + https://x80.org/rhino-coq/v8.9/examples/plf/

- dft.v: https://x80.org/rhino-coq/v8.9/examples/dft.html

  A small development of the theory of the Fourier Transform following
  Julius Orion Smith III's "The Mathematics of the Discrete Fourier
  Transform"

- The IRIS program logic, by Robbert Krebbers et al.

  https://x80.org/rhino-coq/v8.9/examples/iris.html

### Outdated examples [but still working]

- Mtac: The Mtac tutorial by Beta Zilliani:

  https://x80.org/rhino-coq/v8.5/examples/mtac_tutorial.html

- Stlc: The "Simply Typed Lambda Calculus" chapter from Software
  Foundations by Benjamin Pierce et al:

  https://x80.org/rhino-coq/v8.6/examples/Stlc.html

- StackMachine: The First chapter of the book "Certified Programming
  with Dependent Types" by Adam Chlipala:

  https://x80.org/rhino-coq/examples/Cpdt.StackMachine.html

- MirrorCore:
  - A simple demo:
    https://x80.org/rhino-coq/v8.5/examples/mirrorcore.html
  - A demo of developing a cancellation algorithm for commutative
    monoids:
    https://x80.org/rhino-coq/v8.5/examples/mirror-core-rtac-demo.html

## CoqDoc

A `coqdoc` replacement that is better suited to produce jsCoq output
while (mostly) remaining compatible is being developed at
https://github.com/ejgallego/udoc

It works OK for converting `coqdoc` files, but it may produce some
artifacts and have bugs.

## Mailing List ##

You can subscribe to the jsCoq mailing list at:

https://x80.org/cgi-bin/mailman/listinfo/jscoq

The list archives should be also available through Gmane at group:

`gmane.science.mathematics.logic.coq.jscoq`

you can post to the list using nntp.

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
* There surely are threading and performance problems.
* `vm_compute` and `native_compute` are devired to regular `compute`.

## Contact & Sponsorship ##

![FEEVER Logo](/ui-images/feever-logo.png?raw=true "Feever Logo")

jsCoq has been make possible thanks to funding by the [FEEVER](http://feever.fr) project.

Contact: Emilio J. Gallego Arias `e+jscoq at x80.org`.

## jsCoq Users:

Incomplete list of places where jsCoq has been used:

* Coq Winter School 2016: “Advanced Software Verification And Computer Proof”. _Sophia Antipolis_
  https://team.inria.fr/marelle/en/advanced-coq-winter-school-2016/
* Coq Winter School 2016-2017 (SSReflect & MathComp) “Advanced
  Software Verification And Computer Proof”. _Sophia Antipolis_
  https://team.inria.fr/marelle/en/advanced-coq-winter-school-2016-2017/
* Mathematical Components, an Introduction, _Satellite workshop of the ITP 2016 conference_, August 27th, Nancy, France
  https://github.com/math-comp/wiki/wiki/tutorial-itp2016
* Several examples of the "Mathematical Components Book" https://math-comp.github.io/mcb/
* School on "Preuves et Programmes" at l'École de Mines https://www-sop.inria.fr/marelle/mines/
* Mini Corso di Coq a Pavoda: http://www-sop.inria.fr/members/Enrico.Tassi/padova2017/
* Elpi Tutorial / Demo at CoqPL 2017 _Los Angeles_ https://lpcic.github.io/coq-elpi-www/tutorial-demo_CoqPL2018.html
* Coq Winter School 2017-2018 (SSReflect & MathComp) _Sophia Antipolis_ https://team.inria.fr/marelle/en/coq-winter-school-2017-2018-ssreflect-mathcomp/
* Lectures at the "Journées Nationales du Calcul Formel" by Assia Mahboubi:
  https://specfun.inria.fr/amahboub/Jncf18/cours2.html
* [Types Summer School](https://sites.google.com/view/2018eutypesschool/home): http://www-sop.inria.fr/teams/marelle/types18/
* Coq Winter School 2018-2019 (SSReflect & MathComp)  https://team.inria.fr/marelle/en/coq-winter-school-2018-2019-ssreflect-mathcomp/
* CASS 2020, Coq Andes Summer School https://cass.pleiad.cl/
* [Lectures on Separation Logic](https://madiot.fr/sepcourse/) by Jean-Marie Madiot in MPRI's course "Proofs of programs", using Arthur Charguéraud's material. [See it in action!](https://madiot.fr/sepcourse/coq/)

### jsCoq in the press

- http://www.mines-paristech.fr/Actualites/jsCoq-ou-Coq-dans-un-navigateur/2118
- https://news.ycombinator.com/item?id=9836900

## How to Install/Build

You can download ready-to-use builds from
https://github.com/ejgallego/jscoq-builds/ ; find below the
instructions to build JsCoq yourself, it is reasonably easy:
```shell
$ git submodule update --remote
$ ./etc/toolchain-setup.sh
$ make coq
$ make jscoq
```

For more detailed description and prerequisites, see [docs/build.md](./docs/build.md).

### Addon Packages:

  One of jsCoq's strengths is its support for bundling addon
  packages. In order to add your Coq package to jsCoq, you need to add
  a definition file in the `coq-addons` repository. We recommend you
  use one of the existing files as a model.

  Also, you need to define a jsCoq package by editing the
  `coq-jslib//dftlibs.ml` file. Once that is done, calling `make jscoq` agian.

## Serialization

JsCoq used to support serialization to Json or Sexps for Coq's
internal data structures, but this effort has been split to an
independent development. See https://github.com/ejgallego/coq-serapi
for more information.

## Documents

See the `etc/notes/` directory for some random notes about the project.
