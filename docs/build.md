# Building jsCoq

The following instructions describe the procedure for building jsCoq
on a Unix-like system. The required packages can be obtained using
`apt` (Debian), MacPorts/Homebrew (macOS), or the like.

## System-level Prerequisites

In case of problems, we recommend looking first at our [Dockerfile](../etc/Docker/Dockerfile)
which contains detailed package and build instructions for Debian (and please feel free
to contribute a OSX CI job).

To build jsCoq you will need a modern Unix system (Linux or macOS), and:

 * OPAM 2.2 (you can get the installer from https://opam.ocaml.org/doc/Install.html)
   - `bubblewrap` is a dependency of OPAM, you can either install it (`apt install bubblewrap`),
     or skip it by running `opam init --disable-sandboxing`
 * Coq dependencies system dependencies, currently `libgmp`
   + `apt install libgmp-dev`
   + or `apt install libgmp-dev:i386` if you are using the 32 bit
   OCaml version (see below)
 * Node.js 22.x or above + NPM
   - Default versions from `apt` are typically too old; follow the
     [Node.js installation instructions](https://nodejs.org/en/download/package-manager/) to get a newer version.

## Getting the sources

To clone the jsCoq repos, use:
```sh
git clone --recursive git@github.com:jscoq/jscoq.git  # (this repo)
```

## jsCoq Dependencies

jsCoq build requires a dedicated opam switch, the easiest way to setup is just to call

```sh
./etc/toolchain-setup.sh     # optionally --64, see below
```

which will install OCaml 4.14.2 (32-bit version) and the required
packages into a switch called `jscoq+32bit`.

**Note**: You can modify/tweak this switch without affecting your main
 OCaml installation.

### Using a 64 bit toolchain

On macOS 10.14 and above, and on WSL you will have trouble building
 32-bit executables. To use a 64-bit toolchain, include the `--64` flag:
```
./etc/toolchain-setup.sh --64
```

The switch will be called `jscoq+64bit` in this case, and the
`Makefile` will use the workspace `dune-workspace-64` automatically
for the build. This is controlled by adding a file `config.inc` to the
tree.

 _Word of caution about the 64-bit build:_ Using `--64` means that `.vo` files will be compiled on your native 64-bit architecture, using [a patch](https://github.com/jscoq/jscoq/blob/v8.16/etc/patches/coerce-32bit.patch) that attempts to make them compatible with the 32-bit runtime in the browser.
 While this has worked so far, it is brittle and may cause some unexpected behavior in certain corner cases.

**Important Note:** If you plan to build any addons which are built using `coq_makefile`, then you should run `opam switch jscoq+32bit` [or `+64bits`] before any `make` command, in order to choose the right version
of OCaml and Coq.
For Dune builds, configure the switch in your `dune-workspace`.

## Fetching Coq

To fetch the Coq sources from the repository and configure it for build do:
```sh
make coq
```

## Building jsCoq

To build a usable jsCoq version, just do:

```sh
make jscoq
```

This will create a working distribution under `_build/jscoq+32bit/` (or `_build/jscoq+64bit`).

Now serve the files from the distribution directory via HTTP (`make serve`), and
navigate your browser to `http://localhost:8030/`.

You can also build the `wacoq` version using:

```sh
make jscoq
```

### Debugging

To debug the backend, use
```sh
make JSCOQ_DEBUG=1 jscoq
```

This will in particular produce a worker annotated with source map, and not minimized.

jsCoq is easy to develop using the Chrome or Firefox developer tools; the jsCoq
object also has a `debug` flag you can set.

## Building accompanying libraries (optional)

 5. Install jsCoq binaries.
```sh
make install   # this installs jsCoq's version of Coq in the
               # jscoq+32bit (or +64bit) OPAM switch
```

 6. Clone https://github.com/jscoq/addons in a separate working directory.
```sh
git clone --recursive https://github.com/jscoq/addons jscoq-addons
cd jscoq-addons
```

 7. Build the libraries you are interested in.
```sh
cd mathcomp
make
```

 8. Create NPM packages for compiled libraries.
```
make pack   # in jscoq-addons working directory
```

This creates `.tgz` files for packages in `_build/jscoq+32bit` (or `+64bit`).
You can then `npm install` them in your jsCoq distribution.

## Outdated tips

### Google flags

In the past, we used to need this to run Chrome:

```sh
google-chrome --allow-file-access-from-files --js-flags="--harmony-tailcalls" --js-flags="--stack-size=65536" _build/jscoq+32bit
```

That's not relevant anymore, but keeping this documented just in case.
