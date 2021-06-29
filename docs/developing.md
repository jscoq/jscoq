## Development versions

Development for jsCoq 0.14 takes place in the `v8.14` branch. A
preview build of jsCoq 0.14 is usually available at:

<https://x80.org/rhino-coq/v8.14/>

but not updated these days. We are working on having an auto-deployed
build for each commit, help is much welcome!

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

## Docker

We will provide instructions about Docker here soon.

## How to Install/Build

See [docs/build.md](./build.md).

## Addons

We will provide improved instructions for addons here soon, using
Docker.

## Serialization

jsCoq used to support serialization to Json or Sexps for Coq's
internal data structures, but this effort has been split to an
independent development. See https://github.com/ejgallego/coq-serapi
for more information.
