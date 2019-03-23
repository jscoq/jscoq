# Building jsCoq

The following instructions describe the procedure for building jsCoq on a Unix-like
system.
The required packages can be obtained using `apt` (Debian), MacPorts/Homebrew (macOS),
or the like.

## Prerequisites
 * OPAM 2  (use binary installer from https://opam.ocaml.org/doc/Install.html)
 * m4 (`apt install m4`)
 * bubblewrap (`apt install bubblewrap`)
 * npm (bundled with latest Nodejs, follow the [instructions](https://github.com/nodesource/distributions/blob/master/README.md#installation-instructions)).

## Build steps
 1. Clone the jsCoq repo.
```
git clone --recursive git@github.com:ejgallego/jscoq.git (this repo)
```
 2. Install OCaml 4.07.1 (32-bit version) and required packages.
```
./toolchain-setup.sh
```
 3. Fetch and build Coq (32-bit version), plugins and accompanying packages.
```
make coq
```
 4. Build `jscoq_worker.js` (the main jsCoq file) and additional package files.
```
./build.sh
```
 5. (Optional step)
    If you want to also build the extra libraries bundled with jsCoq (mathcomp, iris, ltac2, elpi, equations, dsp):
```
make addons
./build.sh
```

Now serve the files at the root directory of the project via HTTP, and
navigate your browser to `http://localhost/newide.html`, or run them locally:
```
 google-chrome --allow-file-access-from-files --js-flags="--harmony-tailcalls" --js-flags="--stack-size=65536" newide.html
```
