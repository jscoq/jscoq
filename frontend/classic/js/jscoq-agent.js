///@ts-check
/**
 * Injects jsCoq into an existing page.
 * This script is adapted from the Software Foundations jsCoq build.
 * So, it may require some tweaking depending on your development and styles.
 */
import { JsCoq, Deprettify } from './index.js';

function jsCoqInject() {
    var b = document.body;
    b.setAttribute('id', 'ide-wrapper');
    b.classList.add('toggled');
    b.classList.add(isTerse() ? 'terse' : 'full');

    var plug = document.createElement('div');
    plug.setAttribute('id', 'jscoq-plug');
    plug.addEventListener('click', jsCoqStart);
    b.append(plug);
}

var jsCoqShow = location.search === '?jscoq=on' ||
                location.search !== '?jscoq=off' && localStorage.jsCoqShow === 'true';

var jscoq_ids  = ['#main > div.code, #main > div.HIDEFROMHTML > div.code'];
var jscoq_opts = {
    layout:    'flex',
    show:      jsCoqShow,
    focus:     false,
    replace:   true,
    editor:    { mode: { 'company-coq': true }, className: 'jscoq code-tight' },
    init_pkgs: ['init'],
    all_pkgs:  { '+': ['coq'] },
    init_import: ['utf8'],
    implicit_libs: true
};

async function jsCoqLoad() {
    // - remove empty code fragments (coqdoc generates some spurious ones)
    for (let code of document.querySelectorAll('#main > div.code')) {
        if (code.textContent?.match(/^\s*$/)) code.remove();
    }

    // - make page div focusable so that keyboard scrolling works
    var page = /** @type {HTMLElement} */ (document.querySelector('#page'));
    page.setAttribute('tabindex', '-1');
    page.focus();

    // - load and start jsCoq
    await JsCoq.load(jscoq_opts.base_path);

    Deprettify.REPLACES.push(   // LF,PLF define their own versions (for Imp)
        [/∨/g, '\\/'], [/∧/g, '/\\'], [/↔/g, '<->'], [/≤/g, '<='], [/≠/g, '<>'],
        [/∈/g, '\\in']);

    var coq = await JsCoq.start(jscoq_ids, jscoq_opts);
    //@ts-ignore
    window.coq = coq;
    window.addEventListener('beforeunload', () => { localStorage.jsCoqShow = coq.layout.isVisible(); })
}

function jsCoqStart() {
    //@ts-ignore
    window.coq.layout.show();
}

/** SF-style terse mode */
function isTerse() {
    return !!document.querySelector('[src$="/slides.js"]');
}

if (location.search !== '?jscoq=no') {
    window.addEventListener('DOMContentLoaded', () => {
        jsCoqInject();
        jsCoqLoad();
    });
}
