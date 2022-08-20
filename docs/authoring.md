# jsCoq SDK — for library authors

jsCoq is document-oriented, which means that it manipulates a single
document at any given time.
If your project consists of multiple compilation units, they need to
be compiled first in order for `Require` statements to work.
This is similar to the operation mode of other Coq IDEs.

In jsCoq, compiled modules are organized in *packages*, which are essentially ZIP archives containing the `.vo` files and an additional *manifest* file, in JSON format, that contains some metadata and helps jsCoq with automatic resolution of module dependencies.
The former is expected to have a file extension `.coq-pkg`, and the latter, `.json`; for example, `my-toy.coq-pkg` and `my-toy.json`.

The huge caveat is that because jsCoq is bundled with its own version of Coq, as well as the Coq standard library, and because this version is different then the version of Coq you probably have installed on your machine, just compiling your `.v` files as you normally do will not work.
Even if you have the exact version number and magic (*e.g.* `8.15.1/81500`),
the resulting `.vo` files will not be binary-compatible with jsCoq's, because, in general, every build of Coq generates different hashes for standard library objects.
(See section "Troubleshooting" below for common errors that might arise as a result.)

## jsCoq SDK: the main ingredients

The solution offered by jsCoq consists of the following components:
 * A Docker image containing `coqc` and all native binary dependencies required to compile `.v` files. We regularly publish x86-64 and arm64 images on Dockerhub.
 * A script (bundled as a subcommand of the jsCoq CLI) that sets up an environment in which `coqc`, `coqdep`, and `coqtop` are redirected to run the corresponding programs in a Docker container.

This alleviates the need to compile jsCoq yourself (a process described in [`build.md`](./build.md)).
Instead,

 1. Pull the SDK image from Dockerhub and tag it:
    ```bash
    % docker pull jscoq/jscoq:sdk
    % docker tag jscoq/jscoq:sdk jscoq:sdk
    ```
 2. Install jsCoq from NPM, locally in your project:
    ```
    % npm i jscoq
    ```

### Building packages

Now you can run any build command you normally would, prefixed by `npx jscoq sdk`, *e.g.*:
```
% npx jscoq sdk dune build
```
or
```
% npx jscoq sdk make
```

Look at this [nifty demo](../examples/sdk-demo/) if you want to quickly experiment and test whether your setup works.

It is useful to understand the steps that `jscoq sdk` takes when running your build. The process is not airtight so you may have to troubleshoot a little.

 1. Creates a temporary directory `/tmp/jscoq-sdk/hijack`, with links to jsCoq's `cli.cjs` named `coqc`, `coqdep`, `coqtop`, and adds this directory at the front of the `PATH` environment variable. Now every invocation of these programs will go through jsCoq.
 2. Executes the build command in the modified environment.
 3. As soon as `coqc` (or any other command) is invoked, the CLI locates `node_modules/jscoq` in your project directory.
 4. Creates a temporary directory `/tmp/jscoq-sdk/coqlib` and *unpacks* the Coq standard library files from `.coq-pkg` files that are shipped with jsCoq.
 5. Creates a [Docker volume](https://docs.docker.com/storage/volumes/) named `jscoq-sdk`, and copies `/tmp/jscoq-sdk/coqlib` onto it.
 5. Fires up a Docker container in which it *mounts* `/tmp/jscoq-sdk` as well as the mount point that contains the current working directory.
 For example, if the working directory is `/Users/avid/coq/developer`,
 then the entire subtree `/Users/avid` is mounted.
 6. Runs the respective program in the container, with `COQCORELIB` set to `/opt/jscoq-sdk/coqlib` — a directory that resides on the `jscoq-sdk` volume.

Because the build command is run on a [bind mount](https://docs.docker.com/storage/bind-mounts/), compilation artifacts are written directly to host folders.

To take a better look at what jsCoq SDK is doing, set the environment variable `JSCOQ=verbose`.
This turns on some logging messages that are sent to the standard error stream.
(Note that build environments such as Dune that internally parse the output of `coqdep` may choke on the log messages if they are not too careful about separating stdout from stderr.)

## Troubleshooting

### If Docker fails to start

Make sure your Docker daemon is running. If you see this message:
```
docker: Error response from daemon: Bad response from Docker engine.
```

Then probably the daemon is stopped or crashed. Try restarting it.

If you see this message:
```
Unable to find image 'jscoq:sdk' locally
```

Then something went wrong with pulling the SDK image and/or tagging it.
Run `docker image ls` and make sure that `jscoq` with tag `sdk` is there, *e.g.*:
```
REPOSITORY        TAG      IMAGE ID       CREATED         SIZE
jscoq/jscoq       sdk      9e7217981297   3 hours ago      561MB
jscoq             sdk      9e7217981297   3 hours ago      561MB
```

### If compilation works, but results in incompatible `.vo` files

A common error scenario stemming from binary incompatiblity is trying to load compiled `.vo` files and seeing this error:
```
Error: Compiled library Basics.vo makes inconsistent assumptions
over library Coq.Init.Notations
```
another error that may occur is:
```
Anomaly; input_value: integer too large
```
The latter is the result of compiling with a 64-bit build of Coq (jsCoq uses 32-bit, because JavaScript runtimes in browsers are 32-bit).

Make sure the SDK's `coqc` is invoked (run with env `JSCOQ=verbose`).
Then make sure that the version of jsCoq that is served on your Web page is the same NPM package that you have installed.

jsCoq caches the coqlib files to avoid having to copy them for every file compiled.
The CLI tries to be smart about it and evict the cache if the package directory has changed; but to make sure there are no stale library files, `rm -rf /tmp/jscoq-sdk` is always a good thing to try.
