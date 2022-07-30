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

var loadJsCoq, JsCoq;

(function() {

    if (typeof module !== 'undefined')
        module = undefined;  /* for Electron */
    
    var loadCss = function(fn) {
        var link   = document.createElement("link");
        link.href  = fn + '.css';
        link.type  = "text/css";
        link.rel   = "stylesheet";
        document.head.appendChild(link);
    };

    var loadJs = function(fn) {
        return new Promise(function (resolve, error) {
            var script    = document.createElement('script');
            script.type   = 'text/javascript';
            script.src    = fn + '.js';
            script.onload = resolve;
            document.head.appendChild(script);
        });
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

        var files = {
            'css':  [node_modules_path + 'codemirror/lib/codemirror',
                     node_modules_path + 'codemirror/theme/blackboard',
                     node_modules_path + 'codemirror/theme/darcula',
                     node_modules_path + 'codemirror/addon/hint/show-hint',
                     node_modules_path + 'codemirror/addon/dialog/dialog',
                     base_path + 'ui-css/coq-log',
                     base_path + 'ui-css/coq-base',
                     base_path + 'ui-css/coq-light',
                     base_path + 'ui-css/coq-dark',
                     base_path + 'ui-css/settings'],
            'js':   [node_modules_path + 'codemirror/lib/codemirror',
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
                     base_path + 'ui-js/coq-manager']
        };

        for (let fn of files.css)  loadCss(fn)
        for (let fn of files.js)   await loadJs(fn);
    };

    JsCoq = {
        backend: 'js',  /* 'js' or 'wa' */

        base_path: scriptDir ? `${scriptDir}../` : "./",
        node_modules_path: '',
        loaded: undefined,

        is_npm: false,  /* indicates that jsCoq was installed via `npm install` */

        load(...args) {
            let opts = this._getopt(...args),
                {base_path, node_modules_path} = opts;
            return this._load(base_path, node_modules_path).then(() => opts);
        },

        _load(base_path, node_modules_path) {
            return this.loaded ||
                (this.loaded = loadJsCoq(base_path, node_modules_path));
        },

        async start(...args) {
            let opts = this._getopt(...args),
                {base_path, node_modules_path, jscoq_ids, jscoq_opts} = opts;
            await this._load(base_path, node_modules_path);
            return new CoqManager(jscoq_ids, jscoq_opts)
        },

        _getopt(...args) {
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
            JsCoq.backend = jscoq_opts.backend || JsCoq.backend;

            return {base_path, node_modules_path, jscoq_ids, jscoq_opts}
        },

        globalConfig(v) {
            const defaults = {features: []},
                  ls = localStorage['jscoq:config'];
            try { var cfg = ls && JSON.parse(ls); }
            catch (e) { console.warn('(in local config)', ls, e); }
            if (v)
                localStorage['jscoq:config'] = JSON.stringify({...cfg, ...v})
            else return {...defaults, ...cfg};
        }
    };

})();

// Local Variables:
// js-indent-level: 4
// End:
