#!/usr/bin/env node

/**
 * Useful for development: creates links to addons from a given directory.
 */


const fs = require('fs'),
      path = require('path'),
      glob = require('glob'),
      mkdirp = require('mkdirp');

const DEFAULT_CONTEXT = 'jscoq+64bit', DEFAULT_SCOPE = '@jscoq';

const opts = require('commander')
    .option('-c,--build-context <switch>', 'Dune context to look in for build artifacts', DEFAULT_CONTEXT)
    .option('-s,--scope <name>', 'NPM scope for packages', DEFAULT_SCOPE)
    .parse();

const pkgDir = './node_modules',
      pkgPrefix = opts.scope.replace(/^([^@])/, '@$1').replace(/([^/])$/, '$1/'),
      buildRel = `_build/${opts.buildContext}`;

function consumeFromDirectory(dir) {
    dir = cd_maybe(dir, buildRel);

    for (let fn of glob.sync('**/package.json', {cwd: dir})) {
        try {
            var manifest = JSON.parse(fs.readFileSync(path.join(dir, fn)));
        }
        catch (e) {
            console.warn(`in ${fn}:`, e); continue;
        }

        if (manifest.name.startsWith(pkgPrefix)) {
            var source = path.join(cd_maybe('.', buildRel), pkgDir, manifest.name),
                target = path.join(dir, path.dirname(fn));
            console.log(`${manifest.name}  -->  ${target}`);
            mkdirp.sync(path.dirname(source));
            ln_sf(path.resolve(target), source);
        }
    }
}

// `ln -sf`
function ln_sf(target, source) {
    var exists = false;
    try { fs.lstatSync(source); exists = true; } catch {}
    if (exists) fs.unlinkSync(source);
    fs.symlinkSync(target, source);
}

function cd_maybe(dir, rel) {
    var d = path.join(dir, rel);
    try {
        if (fs.statSync(d).isDirectory()) return d
    }
    catch {}
    return dir;
}


for (let dir of opts.args) {
    consumeFromDirectory(dir);
}
