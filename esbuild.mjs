#!/usr/bin/env node
import process from "process";
import * as esbuild from "esbuild";

let watchConfig = (entry) => {
  return {
    onRebuild(error, result) {
      console.log(`[watch] build started (rebuild for ${entry})`);
      if (error) {
        error.errors.forEach((error) =>
          console.error(
            `> ${error.location.file}:${error.location.line}:${error.location.column}: error: ${error.text}`
          )
        );
      } else console.log(`[watch] build finished (rebuild for ${entry}`);
    },
  };
};

let watch = process.argv.includes("--watch") ? watchConfig : (entry) => false;
let minify = process.argv.includes("--minify");
let disable_sourcemap = process.argv.includes("--sourcemap=no");
let sourcemap = disable_sourcemap ? null : { sourcemap: true };

// Node build
var cliEntry = "./frontend/cli/cli.ts";
var nodecli = esbuild
  .build({
    entryPoints: [cliEntry],
    bundle: true,
    platform: "node",
    format: "cjs",
    loader: {
      '.bc.cjs': 'copy'
    },
    outfile: "dist/cli/cli.cjs",
    ...sourcemap,
    minify,
    // watch: watch(nodeEntry),
  })
  .then(() => {
    console.log(`[watch] build finished for ${cliEntry}`);
  })
  .catch(() => process.exit(1));

// Backend build, WASM worker.
/* var backendEntry = "./backend/wasm/wacoq_worker.ts" 
var backend = esbuild
  .build({
    entryPoints: [backendEntry],
    bundle: true,
    platform: "browser",
    outdir: "dist",
    ...sourcemap,
    minify,
    // watch: watch(frontEndEntry),
  })
  .then(() => {
    console.log(`[watch] build finished for ${backendEntry}`);
  })
  .catch(() => process.exit(1)); */

// Frontend build, for modern Chrome
var frontEndEntry = "./frontend/classic/js/index.js"
var frontend = esbuild
  .build({
    entryPoints: [frontEndEntry],
    bundle: true,
    ...sourcemap,
    platform: "browser",
    format: "esm",
    loader: {
      '.png': 'binary',
      '.svg': 'binary'
    },
    outdir: "dist/frontend",
    minify,
    // watch: watch(frontEndEntry),
  })
  .then(() => {
    console.log(`[watch] build finished for ${frontEndEntry}`);
  })
  .catch(() => process.exit(1));

// TODO: run serve if --serve was passed.
// await Promise.all([nodecli, backend, frontend]);
await Promise.all([frontend])
