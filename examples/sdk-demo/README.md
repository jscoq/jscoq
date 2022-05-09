# jsCoq SDK — a minimal example

This small project showcases how to compile a library for use in jsCoq.
It uses the [Elements of Group Theory](https://github.com/coq-contribs/group-theory)
library as a demonstration.

The `Makefile` in this directory will clone the repo, then launch Dune
with the `dune` file within a jsCoq SDK environment.

### Prerequisites

 * Docker
 * Dune 3.1 or above
 * jsCoq SDK

The latter can be downloaded and installed by running `make setup`.

### Building and Running

Simply run
```bash
% npm i   # if you used `make setup`, this already ran
% make
```

Then serve the `sdk-demo` directory over HTTP with *e.g.* `npx serve` or `npx http-server`.

By default, it will build using the jsCoq version that is listed in `package.json`.
If you care for a different version, run this first:
```bash
% npm run jscoq@<ver>   # e.g. jscoq@latest or jscoq@0.15.0
```