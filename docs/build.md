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
```
git clone --recursive git@github.com:ejgallego/jscoq.git (this repo)
```
 2. Install OCaml 4.07.1 (32-bit version) and required packages.
```
./etc/toolchain-setup.sh
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
is built using `coq_makefile` then you should perform an `opam switch
jscoq+32bit` [or 64 bits] before starting the build process at
all. Otherwise the wrong OCaml version will be fetched.

 3. Fetch Coq 8.10 sources from the repository and configure it for build.

```
make coq
```
 4. Build `jscoq_worker.js` (the main jsCoq file) and additional package files.
```
make jscoq
```
 5. (Optional) Build math-comp and other accompanying libraries.
```
make addons
make jscoq
```

This will create a working distribution under `_build/jscoq+32bit/` (or `_build/jscoq+64bit`).

Now serve the files from the distribution directory via HTTP, and
navigate your browser to `http://localhost/index.html`, or run them locally:
```
 google-chrome --allow-file-access-from-files --js-flags="--harmony-tailcalls" --js-flags="--stack-size=65536" _build/jscoq+32bit
```
