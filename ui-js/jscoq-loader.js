// The jsCoq loader
// (c) 2015-2016 Mines ParisTech/ARMINES
//
// CoqManager manages a document composed of several coq snippets,
// allowing the user to send/retract indivual coq sentences throu
// them. The Coq snippets can be provided by several sources, we just
// require them to be able to list parts and implement marks.
//
// We also provide a side panel with proof and query buffers.

"use strict";

var loadJs = function(js) {
    return new Promise(function (resolve, error) {
        var script    = document.createElement('script');
        script.type   = 'text/javascript';
        script.src    = js + '.js';
        script.onload = resolve;
        document.head.appendChild(script);
    });
};

var loadJsCoq, JsCoq;

(function(){

    if (typeof module !== 'undefined')
        module = undefined;  /* for Electron */
    
    var loadCss = function(css) {

        var link   = document.createElement("link");
        link.href  = css+'.css';
        link.type  = "text/css";
        link.rel   = "stylesheet";

        document.head.appendChild(link);
    };

    var scriptDir = (typeof document !== 'undefined' && document.currentScript) ?
        document.currentScript.attributes.src.value.replace(/[^/]*$/, '') : undefined;

    // In order for jsCoq to work we need to load:
    // - Codemirror CSS [core + themes]
    // - Codemirror JS  [core + emacs keymap + addons]
    // - Codemirror custom modes and addons [coq + company-coq + tex-input]
    // - jQuery
    // - JSZip
    // - localForage
    // - jsCoq = cm-provider + coq-packages + coq-manager

    loadJsCoq = async function(base_path, node_modules_path) {

        base_path = (base_path || JsCoq.base_path).replace(/([^/])$/, '$1/');
        JsCoq.base_path = base_path;

        node_modules_path = (node_modules_path ||
                             base_path + (JsCoq.is_npm ? "../" : "node_modules/"))
                            .replace(/([^/])$/, '$1/')
        JsCoq.node_modules_path = node_modules_path;

        loadCss(node_modules_path + 'codemirror/lib/codemirror');
        loadCss(node_modules_path + 'codemirror/theme/blackboard');
        loadCss(node_modules_path + 'codemirror/theme/darcula');
        loadCss(node_modules_path + 'codemirror/addon/hint/show-hint');
        loadCss(node_modules_path + 'codemirror/addon/dialog/dialog');
        loadCss(base_path + 'ui-css/coq-log');
        loadCss(base_path + 'ui-css/coq-base');
        loadCss(base_path + 'ui-css/coq-light');
        loadCss(base_path + 'ui-css/coq-dark');

        var files = [node_modules_path + 'codemirror/lib/codemirror',
                     node_modules_path + 'codemirror/keymap/emacs',
                     node_modules_path + 'codemirror/addon/selection/mark-selection',
                     node_modules_path + 'codemirror/addon/edit/matchbrackets',
                     node_modules_path + 'codemirror/addon/hint/show-hint',
                     node_modules_path + 'codemirror/addon/dialog/dialog',
                     node_modules_path + 'jquery/dist/jquery.min',
                     node_modules_path + 'jszip/dist/jszip.min',
                     node_modules_path + 'localforage/dist/localforage.min',
                     base_path + 'ui-external/CodeMirror-TeX-input/addon/hint/tex-input-hint',
                     base_path + 'ui-js/jscoq',
                     base_path + 'ui-js/mode/coq-mode',
                     base_path + 'ui-js/addon/company-coq',
                     base_path + 'ui-js/cm-provider',
                     base_path + 'ui-js/format-pprint',
                     base_path + 'ui-js/settings',
                     base_path + 'ui-js/coq-packages',
                     base_path + 'ui-js/coq-layout-classic',
                     base_path + 'ui-js/coq-manager'];

        for (let js of files) await loadJs(js);
    };

    JsCoq = {
        base_path: scriptDir ? `${scriptDir}../` : "./",
        node_modules_path: '',
        loaded: undefined,

        is_npm: false,  /* indicates that jsCoq was installed via `npm install` */

        load(base_path, node_modules_path) {
            return this.loaded ||
                (this.loaded = loadJsCoq(base_path, node_modules_path));
        },

        async start(...args) {
            var base_path = undefined, node_modules_path = undefined,
                jscoq_ids = ['ide-wrapper'], jscoq_opts = {};
            
            if (typeof args[0] === 'string') base_path = args.shift();
            if (typeof args[0] === 'string') node_modules_path = args.shift();
            if (Array.isArray(args[0])) jscoq_ids = args.shift();
            if (args[0]) jscoq_opts = args.shift();

            if (args.length > 0) console.warn('too many arguments to JsCoq.start()');

            // Umm.
            base_path = base_path || jscoq_opts.base_path || JsCoq.base_path;
            jscoq_opts.base_path = jscoq_opts.base_path || base_path;

            await this.load(base_path, node_modules_path);
            return new CoqManager(jscoq_ids, jscoq_opts)
        }
    };

})();

// Local Variables:
// js-indent-level: 4
// End:
