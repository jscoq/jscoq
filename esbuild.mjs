#!/usr/bin/env node
import fs from 'fs';
import path from 'path';
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
let sourcemap = disable_sourcemap ? null : { sourcemap: "inline" };
let sourcemap_view = disable_sourcemap ? null : { sourcemap: "inline" };
let enableMeta = false

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
    metafile: enableMeta,
    ...sourcemap,
    minify,
    // watch: watch(frontEndEntry),
  })
  .then((res) => {
    if(enableMeta) fs.writeFileSync('backend-meta.json', JSON.stringify(res.metafile));
    console.log(`[watch] build finished for ${backendEntry}`);
  })
  .catch((exn) => {
    console.log(exn);
    process.exit(1)}
  );

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
    metafile: enableMeta,
    outdir: "dist/frontend",
    minify,
    // watch: watch(frontEndEntry),
  })
  .then((res) => {
    if(enableMeta) fs.writeFileSync('frontend-meta.json', JSON.stringify(res.metafile));
    console.log(`[watch] build finished for ${frontEndEntry}`);
  })
  .catch((exn) => {
    console.log(exn);
    process.exit(1)}
  );

function viewBuild(name, dir, file) {
  return esbuild
    .build({
      entryPoints: [path.join(dir, file)],
      bundle: true,
      ...sourcemap_view,
      platform: "browser",
      outdir: path.join("dist/frontend", name),
      outbase: dir,
      minify,
      metafile: enableMeta,
      // watch: watch(file),
    })
    .then((res) => {
      if(enableMeta) fs.writeFileSync(name + '-meta.json', JSON.stringify(res.metafile));
      console.log(`[watch] build finished for ${file}`);
    })
    .catch((exn) => {
      console.log(exn);
      process.exit(1)
    }
          );
}

var infoView = viewBuild("info-view", "./vendor/coq-lsp/editor/code/views/info/", "index.tsx");

// TODO: run serve if --serve was passed.
await Promise.all([frontend, backend, infoView])
