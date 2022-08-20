/**
 * Legacy backward-compat with 0.15.x and older versions that did not
 * user ES modules.
 */

var loadModuleCompat = function(fn) {
    // Note: can only load a single module! `window._jscoq_resolve` is global.
    return new Promise(function (resolve, error) {
        var script    = document.createElement('script');
        script.type   = 'module';
        script.innerText = `import { JsCoq } from './${fn}'; window.JsCoq = JsCoq; window._jscoq_resolve(JsCoq);`;
        window._jscoq_resolve = resolve;
        document.head.appendChild(script);
    });
};

var scriptDir = (typeof document !== 'undefined' && document.currentScript) ?
        document.currentScript.attributes.src.value.replace(/[^/]*$/, '') : undefined,
    basePath = scriptDir ? `${scriptDir}../` : "./";
    loading = loadModuleCompat(basePath + 'ui-js/index.js');


console.warn(`Loading jsCoq in compatibility mode; switching to ES modules is recommended:\n  ` +
    `Use \`<script type="module">import { JsCoq } from './${basePath}jscoq.js'\` instead of \`<script src="...">\`.`)
    

var JsCoq = {
    async load(...a) {
        return (await loading).load(...a);
    },
    async start(...a) {
        return (await loading).start(...a);
    }
};

var loadJsCoq = JsCoq.load; // first approx?