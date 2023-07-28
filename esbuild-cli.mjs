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
    outfile: "dist-cli/cli.cjs",
    ...sourcemap,
    minify,
    // watch: watch(cliEntry),
  })
  .then(() => {
    console.log(`[watch] build finished for ${cliEntry}`);
  })
  .catch(() => process.exit(1));

await nodecli;
