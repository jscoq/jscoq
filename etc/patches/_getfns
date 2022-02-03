#!/usr/bin/env node

const fs = require('fs');

for (let patchFn of process.argv.slice(2)) {
    var inp = fs.readFileSync(patchFn, 'utf-8');
    for (let mo of inp.matchAll(/^--- a\/(.*)/mg)) {
        console.log(mo[1]);
    }
}
