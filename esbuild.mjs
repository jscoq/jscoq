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

// Backend build, WASM worker.
var backendEntry = "./backend/wasm/wacoq_worker.ts"
var backend = esbuild
  .build({
    entryPoints: [backendEntry],
    bundle: true,
    platform: "browser",
    format: "esm",
    outdir: "dist",
    inject: ["./backend/wasm/shims/process-shim.js",
             "./backend/wasm/shims/buffer-shim.js"
            ],
    define: {
      global: "self"
    },
    ...sourcemap,
    minify,
    // watch: watch(frontEndEntry),
  })
  .then(() => {
    console.log(`[watch] build finished for ${backendEntry}`);
  })
  .catch(() => process.exit(1));

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
      '.svg': 'dataurl'
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
await Promise.all([frontend,backend])
