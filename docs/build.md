# Building jsCoq

The following instructions describe the procedure for building jsCoq
on a Unix-like system. The required packages can be obtained using
`apt` (Debian), MacPorts/Homebrew (macOS), or the like.

## Prerequisites

 * OPAM 2 (you can get the installer from https://opam.ocaml.org/doc/Install.html)
   - `bubblewrap` is a dependency of OPAM, you can either install it (`apt install bubblewrap`),
     or skip it by running `opam init --disable-sandboxing`
 * m4 (`apt install m4`)
 * npm (bundled with latest Nodejs, follow the [instructions](https://github.com/nodesource/distributions/blob/master/README.md#installation-instructions)).

## Build steps

 1. Clone the jsCoq repo.
```sh
git clone --recursive git@github.com:ejgallego/jscoq.git  # (this repo)
cd jscoq
```

 2. Install OCaml 4.08.1 (32-bit version) and required packages.
```sh
./etc/toolchain-setup.sh     # optionally --64, see below
```
 **Note 1**: This will create an OPAM switch called `jscoq+32bit` using the
 `4.07.1+32bit` compiler, which the build will then use. You can modify/tweak
 this switch without affecting your main OCaml installation.

 **Note 2:** On macOS 10.14 and above and on WSL you will have trouble building
 32-bit executables. To use a 64-bit toolchain, include the `--64` flag:
```
./etc/toolchain-setup.sh --64
```
 The switch will be called `jscoq+64bit` in this case, and the `Makefile` will
 use the workspace `dune-workspace-64` for the build.

**Important Note:** if you plan to build any addons with ML code which
is built using `coq_makefile`, then you should run `opam switch jscoq+32bit` [or `+64bits`] before any `make` command, in order to choose the right version
of OCaml and Coq.

 3. Fetch Coq 8.10 sources from the repository and configure it for build.
```sh
make coq
```

 4. Build `jscoq_worker.js` (the main jsCoq file) and additional package files.
```sh
make jscoq
```

This will create a working distribution under `_build/jscoq+32bit/` (or `_build/jscoq+64bit`).

Now serve the files from the distribution directory via HTTP, and
navigate your browser to `http://localhost/index.html`, or run them locally:
```sh
 google-chrome --allow-file-access-from-files --js-flags="--harmony-tailcalls" --js-flags="--stack-size=65536" _build/jscoq+32bit
```

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