#!/usr/bin/env node
import fs from 'fs';
import path from 'path';
import process from "process";
import * as esbuild from "esbuild";
import { sassPlugin } from "esbuild-sass-plugin";

const plugins = [{
  name: 'esbuild-problem-matcher',
  setup(build) {
    let file = build.initialOptions.entryPoints[0];

    build.onStart(() => {
      console.log(`[watch] build started for ${file}`);
    });

    build.onEnd(result => {
      if(result.errors.length > 0) {
        result.errors.forEach((e) =>
          console.error(
            `> ${e.location.file}:${e.location.line}:${e.location.column}: error: ${e.text}`
          )
        );
      } else {
        console.log(`[watch] build finished for ${file}`);
        if (enableMeta) {
          fs.writeFileSync(`${file}.json`, JSON.stringify(result.metafile, null, 2));
        }
      }
    });
  },
}];

const watchContext = async (ctxp) => {
  let ctx = await ctxp;

  if (process.argv.includes("--watch")) {
    await ctx.watch();
  } else {
    await ctx.rebuild();
    await ctx.dispose();
  }
};

let minify = process.argv.includes("--minify");
let disable_sourcemap = process.argv.includes("--sourcemap=no");
let sourcemap = disable_sourcemap ? null : { sourcemap: "inline" };
let sourcemap_view = disable_sourcemap ? null : { sourcemap: "inline" };
let enableMeta = false

// Backend build, WASM worker.
var backendEntry = "./backend/wasm/wacoq_worker.ts"
var backend = watchContext(esbuild.context({
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
  plugins
}));

// Frontend build, for modern Chrome
var frontEndEntry = "./frontend/classic/js/index.js"
var frontend = watchContext(esbuild.context({
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
  plugins: [sassPlugin(), ...plugins]
}));

function viewBuild(name, dir, file) {
  return watchContext(esbuild.context({
    entryPoints: [path.join(dir, file)],
    bundle: true,
    ...sourcemap_view,
    platform: "browser",
    outdir: path.join("dist/frontend", name),
    outbase: dir,
    minify,
    loader: {
      '.png': 'binary',
      '.svg': 'dataurl',
      '.ttf': 'dataurl',
      '.woff': 'dataurl',
      '.woff2': 'dataurl',
    },
    metafile: enableMeta,
    plugins
  }));
}

var infoView = viewBuild("info-view", "./vendor/coq-lsp/editor/code/views/info/", "index.tsx");
var infoViewCss = viewBuild("info-view", "./frontend/views/info/", "iframe.css");

// TODO: run serve if --serve was passed.
await Promise.all([frontend, backend, infoView, infoViewCss])
