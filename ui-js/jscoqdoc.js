#!/usr/bin/env node

const fs = require('fs'),
      path = require('path'),
      chld = require('child-process-promise');


const JSCOQ_URL = process.env['JSCOQ_URL'] || '.',
      SCRIPTS = ["ui-js/jscoq-loader.js", "ui-js/jscoq-agent.js"],
      STYLES = ["ui-css/jscoqdoc.css"];

function treatText(text) {
    return text
        .replace(/(<link href=")coqdoc[.]css(".*>)/, (_, pref, suf) =>
            [...SCRIPTS.map(mkScript), ...STYLES.map(mkStyle)].join('\n'));
}

function treatFile(fn) {
    var text = fs.readFileSync(fn, 'utf-8');
    fs.writeFileSync(fn, treatText(text));
}

function url(fn) {
    return `${JSCOQ_URL}/${fn}`;
}

function mkScript(fn) {
    return `<script src="${url(fn)}"></script>`;
}
function mkStyle(fn) {
    return `<link href="${url(fn)}" rel="stylesheet" type="text/css" />`;
}

async function main() {
    var args = process.argv.slice(2),
        coqdocArgs = args.filter(x => !x.endsWith('.html')),
        html = args.map(a => {
            if (a.endsWith('.html')) return a;
            else if (a.endsWith('.v'))
                return path.basename(a).replace(/[.]v$/, '.html')
        }).filter(x => x);

    if (coqdocArgs.length > 0) {
        await chld.spawn('coqdoc', coqdocArgs, {stdio: 'inherit'});
    }

    for (let fn of html)
        treatFile(fn);
}

main().catch(e => {
    console.log(`error: ${e.message}`);
    process.exit(1);
})
