## Contributing to jsCoq

Thanks for willing to contribute to jsCoq! Contributing is as easy as
opening a pull request, issue, or dropping by the Zulip channel and
talking to us.

### Building and debugging

A quick jsCoq build can be done as:
```sh
./etc/setup-toolchain.sh
make jscoq
make serve
```

then point your browser to `http://localhost:8013`

See [./docs/build](./docs/build) for more detailed information on
build and dependencies.

### Project and source code organization

As of today, the project is structured in 4 directories:

- `vendor`: contains a submodule with the current version of Flèche
  used by jsCoq, this allows us to have a combined fast incremental
  build, and crucially, to develop Flèche and jsCoq at the same time.

- `backend`: contains the source code for the jsCoq workers and a
  typescript library, `coq-worker.ts` to communicate with them. As of
  today, they are thin wrappers over `Flèche`, mainly managing events,
  runtime setup, and packages. In particular, we can find:
  + `backend/jsoo` / `backend/wasm`: worker code
  + `backend/commmon`: common jsCoq interpreter

- `frontend`: contains the source code for the browser frontend and
  for the CLI. This is as of today a pretty standard node / browser
  build setup based on `esbuild`.

- `lib`: contains some common code, likely to be removed

### Build process

The build process of jsCoq involves 3 steps:

- **worker build**: this is a standard OCaml build using dune, see the
  corresponding `dune` files, but there is little special about it

- **frontend build**: this is a standard `esbuild` build, controlled
  by the several `esbuild-*.mjs` files.

- **packages build**: in order to test jsCoq, a set of `.coq-pkg`
  files for the standard library are created, this is done using
  `dune` to call the `jscoq` CLI

The whole build is driven by a top-level `dune` file.

### Coding style

Nothing very special has to be kept in mind, we follow standard OCaml
practice, with `ocp-indent` and `ocamlformat` indentation guidelines,
but we are liberal in some places, in particular with regards to
intra-line indentation. We compile with a very strict set of warnings.

### Review and merge guidelines

We recommend that most non-trivial changes take place using pull
requests. Any contributor can merge a pull request [including their
own] provided the pull request:

- has updated the `CHANGES.md` file,
- passes GitHub CI,
- has been reviewed if needed.

Note that we'd like to favor an agile development style, and remain
liberal in merging PRs.

While one approving review from other contributor is encouraged before
merging, feel free to go ahead if you are confident the change is
correct, if a review doesn't happen in a reasonable amount of time, or
if delaying the merge would interfere with your development plans.

We prefer GPG signed commits as well as `Signed-off-by` commits.

### Commit tag conventions [work in progress]:

We have some [soft] commit tag conventions:

- [jscoq]: ML/Coq interface
- [ui]: Html/Css commit
- [cm]: CodeMirror provider
- [libs]: Coq Library support and format
- [doc]: Documentation
- [addons]: Addons support
- [build]: Build system
- [feature]: Adding a new feature
- [bugfix]: Bug fix
- [refactor]: Refactoring commit (no functional change intended)
- [ci] / [travis]: Continuous integration
- [test]: Adding or modifying a test
- [misc]: Miscellanenous small things

### Previous jsCoq versions

Some previous jsCoq version can be accessed at:

- <https://x80.org/rhino-coq/v8.11/>
- <https://x80.org/rhino-coq/v8.10/>
- <https://x80.org/rhino-coq/v8.9/>
- <https://x80.org/rhino-coq/v8.8/>
- <https://x80.org/rhino-coq/v8.7/>
- <https://x80.org/rhino-coq/v8.6/>
- <https://x80.org/rhino-coq/v8.5/>
