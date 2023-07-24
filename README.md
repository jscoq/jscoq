Run the Coq Proof Assistant in your browser!
------------------------

![Build Status](https://github.com/jscoq/jscoq/actions/workflows/ci.yml/badge.svg)

jsCoq is an Online Integrated Development Environment for the
[Coq](https://coq.inria.fr) proof assistant and runs in your browser!
We aim to enable new UI/interaction possibilities and to improve the
accessibility of the Coq platform itself. Current stable version is
jsCoq 0.16.1 supporting Coq 8.16.0, try it:

<https://coq.vercel.app>

jsCoq is written to conform to ES2017; any recent standard-compliant
browser should be able to run it. No servers or external programs are needed.
See the [Troubleshooting](#Troubleshooting) section if you have problems.

jsCoq is community-developed by a [team of contributors](#Credits).

## Are you a jsCoq user?

Have you developed or taught a course **using jsCoq**? Do you have some feedback for us?

If so, please submit a pull request or an issue so we can add your
lectures to the list of [jsCoq users](#jsCoq-Users). This is essential
to guarantee future funding of the project.

## Basic Usage

The main page showcases jsCoq by walking through a proof for the infinitude of primes using
[`math-comp`](https://github.com/math-comp/math-comp), due to Georges Gonthier.

Once jsCoq finishes loading, you can step through the proof using the
arrow buttons on the toolbar (top right), or using these keyboard
shortcuts:

| Shortcut           | Action           |
|--------------------|------------------|
| Alt-N or Alt-↓     | Go to next       |
| Alt-P or Alt-↑     | Go to previous   |
| Alt-Enter or Alt-→ | Go to cursor     |

You can open a blank editor and experiment with your own Coq developments using the
[scratchpad](https://coq.vercel.app/scratchpad.html).
The same keyboard shortcuts apply here.

The scratchpad's contents are saved in your browser's local storage (IndexedDB, specifically),
so they are not lost if you close the browser window or refresh the page.
You can, in fact, store more than one document using the local open/save file dialogs:

| Shortcut           | Action                                                                       |
|--------------------|------------------------------------------------------------------------------|
| Ctrl-S             | Save file (with the last name provided, or `untitled.v`)                     |
| Ctrl-Shift-S       | Save file as (prompts for file name; also has options to download or share the content)  |
| Ctrl-Alt-S         | Save file to disk (using the browser's Save dialog, or preset destination)   |
| Ctrl-O             | Open file (prompts for file name, supports tab completion)                   |
| Ctrl-Alt-O         | Open file from disk (using the browser's Open dialog)                        |

On Mac, replace Ctrl with ⌘ (command) and Alt with ⌥ (option), as is traditional.

Drag `.v` files from your local drive onto the scratchpad to open them.
You can also drag multiple files, which will open up a project pane to the left of the editor, allowing you to switch between them; this functionality is still experimental.

### Sharing your development

A small pastebin-like server based on [Hastebin](https://hastebin.com) is available for sharing `.v` files between users.
Open the save dialog (Ctrl-Shift-S) and click "Share"; then share the URL from your browser's location bar with anyone you like.
The URL represents the state of the document at the moment it was shared, and this state is read-only. Every time you click "Share", a fresh URL is generated.
Shared content is not saved forever, though; documents are typically available for a period of ~30 days.

## How to build your own jsCoq documents

See the [dedicated page](docs/embedding.md) for information on advanced
options and jsCoq HTML embedding API. A quick setup can be done with:

```
$ npm install jscoq
```

then copy and adapt the [template page](https://github.com/ejgallego/jscoq/blob/v8.14/examples/npm-template.html)
page to your needs.

*For a more detailed tutorial and information, refer to* [docs/embedding.md](docs/embedding.md).

##  Contributing and Developer Information

See the [dedicated page](docs/developing.md) for developer information
as well as links to past versions and tools.

This is a beta-status project, but any contribution or comment is
really welcome! See [the contributing guide](CONTRIBUTING.md) for more
information.

## Publications

See the [dedicated file](docs/papers.md)

## Examples

The main page includes a proof of the infinitude of primes by
G. Gonthier. We provide some more examples as a showcase of the tool:

- The Software Foundations suite (so far, LF and PLF volumes):
  + https://jscoq.github.io/ext/sf

 - Mike Nahas's Coq Tutorial: https://corwin-of-amber.github.io/jscoq/tut/nahas/nahas_tutorial.html

### Outdated examples [but still working]

- dft.v: https://x80.org/rhino-coq/v8.11/examples/dft.html

  A small development of the theory of the Fourier Transform following
  Julius Orion Smith III's "The Mathematics of the Discrete Fourier
  Transform"

- equations: https://x80.org/rhino-coq/v8.11/examples/equations_intro.htmla

  Introduction to the [Coq Equations](https://github.com/mattam82/Coq-Equations) package from
  the official documentation.

- The IRIS program logic, by Robbert Krebbers et al.

  https://x80.org/rhino-coq/v8.9/examples/iris.html

- Mtac: The Mtac tutorial by Beta Zilliani:

  https://x80.org/rhino-coq/v8.5/examples/mtac_tutorial.html

- StackMachine: The First chapter of the book "Certified Programming
  with Dependent Types" by Adam Chlipala:

  https://x80.org/rhino-coq/v8.5/examples/Cpdt.StackMachine.html

- MirrorCore:

  - A simple demo:
    https://x80.org/rhino-coq/v8.5/examples/mirrorcore.html

  - A demo of developing a cancellation algorithm for commutative
    monoids:
    https://x80.org/rhino-coq/v8.5/examples/mirror-core-rtac-demo.html

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
* [EPIT 2020 - Spring School on Homotopy Type Theory](https://github.com/HoTT/EPIT-2020)

### jsCoq in the press

- http://www.mines-paristech.fr/Actualites/jsCoq-ou-Coq-dans-un-navigateur/2118
- https://news.ycombinator.com/item?id=9836900

### Addon Packages

One of jsCoq's strengths is its support for bundling addon
packages. In order to add your Coq package to jsCoq, you need to compile
it with jsCoq's version of Coq.
Head over to [jscoq/addons](https://github.com/jscoq/addons) for pointers to
some well-known packages that have been compiled for jsCoq and are bundled
with every version of jsCoq.
You can use these as examples for bundling your own libraries.

## Troubleshooting

**Are you getting a `StackOverflow` exception?** Unfortunately these
are hard to fix; you may be stuck with them for a while.

* Clearing the browser cache usually solves lots of issues.
* Change browser, if using Firefox try Chrome, if using Chrome try Firefox.

### Reporting Bugs ###

Feel free to use the issue tracker. Please include your
browser/OS/user-agent and any command-line options.

### Contact and on-line help ###

- [jsCoq's Zulip Room](https://coq.zulipchat.com/#narrow/stream/256336-jsCoq), main developer chat
- [jsCoq's gitter](https://gitter.im/jscoq/Lobby), legacy developer chat
- [Coq's discourse](https://coq.discourse.group/) [use the jscoq tag], for general announcements and questions
- [StackOverflow](https://stackoverflow.com/) [use the jscoq tag]

### What is broken ###

* Loading ML modules is slow.
* Loading `.vo` files is slow.
* There surely are threading and performance problems.
* `vm_compute` and `native_compute` fall back to regular `compute`.

## Documents

See the `etc/notes/` directory for some random notes about the project.

## Credits

### Core developer team

- [Emilio Jesús Gallego Arias](https://www.irif.fr/~gallego/) , Inria, Université de Paris, IRIF
- [Shachar Itzhaky](https://cs.technion.ac.il/~shachari/) , Technion

### Past Contributors

- Benoît Pin, [CRI, MINES ParisTech](https://www.cri.ensmp.fr)

## Acknowledgements

![FEEVER Logo](/frontend/classic/images/feever-logo.png?raw=true "Feever Logo")

jsCoq was made possible thanks to funding by the
[FEEVER](http://feever.fr) project and support from [MINES
ParisTech](http://www.mines-paristech.eu)

We want to _strongly thank_ the `js_of_ocaml` developers. Without
their great and quick support jsCoq wouldn't have been possible.

[CodeMirror](https://codemirror.net/) has played a crucial role in the
project, we are very happy with it, thanks a lot!

Please consider supporting the development of CodeMirror with a donation.
