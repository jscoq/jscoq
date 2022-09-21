#!/usr/bin/env node
//@ts-check

const fs = require('fs'),
      path = require('path'),
      chld = require('child-process-promise');

const JSCOQ_URL = process.env['JSCOQ_URL'] || '.',
      SCRIPTS = ["frontend/classic/js/jscoq-agent.js"],
      STYLES = ["frontend/classic/css/jscoqdoc.css"];

const DEFAULT_TEMPLATE =`
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"
"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
  <meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
  {{default-tags}}
  <title>{{title}}</title>
</head>
<body>
<div id="page">
<div id="header"></div>
<div id="main" class="jscoqdoc">
{{the-document}}
</div>
</div>
</body>
</html>
`

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
    return `<script src="${url(fn)}" type="module"></script>`;
}
function mkStyle(fn) {
    return `<link href="${url(fn)}" rel="stylesheet" type="text/css" />`;
}

function intoTemplate(template, values) {
    return template.replace(/{{(.*)}}/g, (_, key) => values[key] ?? '');
}

function processBody(template, vFn, htmlFn) {
    const title = path.basename(vFn),
          tags = [...SCRIPTS.map(mkScript), ...STYLES.map(mkStyle)].join('\n');
    return intoTemplate(template, {
        'the-document': fs.readFileSync(htmlFn),
        'default-tags': tags,
        title
    });
}

function parseArgs(args) {
    var opts = {};
    if (args[0] === '--template') {
        opts['template'] = args[1];
        args = args.slice(2);
    }
    return {args, opts};
}

async function generateDocs(coqdocArgs, opts) {
    var template = opts.template ? fs.readFileSync(opts.template, 'utf-8')
                             : DEFAULT_TEMPLATE;

    await chld.spawn('coqdoc', ['--body-only', ...coqdocArgs], {stdio: 'inherit'});
    for (let vFn of coqdocArgs) {
        if (vFn.endsWith('.v')) {
            let htmlFn = path.basename(vFn).replace(/[.]v$/, '.html');
            fs.writeFileSync(htmlFn, processBody(template, vFn, htmlFn));
        }
    }
}

async function main() {
    var {args, opts} = parseArgs(process.argv.slice(2)),
        coqdocArgs = args.filter(x => !x.endsWith('.html')),
        html = args.filter(x => x.endsWith('.html'));

    if (coqdocArgs.length > 0)
        await generateDocs(coqdocArgs, opts);

    for (let fn of html)
        treatFile(fn);
}

main().catch(e => {
    console.log(`error: ${e.message}`);
    process.exit(1);
})
