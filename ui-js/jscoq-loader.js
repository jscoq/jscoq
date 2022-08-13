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

import { CoqManager } from './coq-manager.js';

var loadJsCoq, JsCoqLoader;

(function() {

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

    var scriptDir = import.meta.url.replace(/[^/]*$/, '');

    // In order for jsCoq to work we need to load:
    // - Codemirror CSS [core + themes]
    // - Codemirror JS  [core + emacs keymap + addons]
    // - Codemirror custom modes and addons [coq + company-coq + tex-input]
    // - jQuery
    // - JSZip
    // - localForage
    // - jsCoq = cm-provider + coq-packages + coq-manager

    loadJsCoq = async function(base_path, node_modules_path, is_npm) {

        base_path = base_path.replace(/([^/])$/, '$1/');

        node_modules_path = (node_modules_path ||
                             base_path + (is_npm ? "../" : "node_modules/"))
                            .replace(/([^/])$/, '$1/')

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
                     base_path + 'ui-js/format-pprint']
        };

        for (let fn of files.css) loadCss(fn)
        for (let fn of files.js) await loadJs(fn);
    };

    JsCoqLoader = {

        loaded: undefined,

        _load(base_path, node_modules_path, is_npm) {
            return this.loaded ||
                (this.loaded = loadJsCoq(base_path, node_modules_path, is_npm));
        },

        _getopt(...args) {
            var base_path = undefined, node_modules_path = undefined,
                jscoq_ids = ['ide-wrapper'], jscoq_opts = {};

            // (maybe) set base path
            if (typeof args[0] === 'string') base_path = args.shift();
            base_path = base_path || jscoq_opts.base_path || scriptDir ? `${scriptDir}../` : "./";

            // (maybe) set node path
            if (typeof args[0] === 'string') node_modules_path = args.shift();

            // ids and options
            if (Array.isArray(args[0])) jscoq_ids = args.shift();
            if (args[0]) jscoq_opts = args.shift();

            if (args.length > 0) console.warn('too many arguments to JsCoqLoader.start()');

            var backend = jscoq_opts.backend || 'js';

            return {base_path, node_modules_path, jscoq_ids, jscoq_opts, backend}
        },

        _config(opts) {
            opts.globalConfig = function(v) {
                    const defaults = {features: []},
                          ls = localStorage['jscoq:config'];
                    try { var cfg = ls && JSON.parse(ls); }
                    catch (e) { console.warn('(in local config)', ls, e); }
                    if (v)
                        localStorage['jscoq:config'] = JSON.stringify({...cfg, ...v})
                    else return {...defaults, ...cfg};
            };

            return opts;
        },

        async start(...args) {

            var is_npm = false;
            let opts = this._getopt(...args),
                {base_path, node_modules_path, jscoq_ids, jscoq_opts, backend} = opts;
            await this._load(base_path, node_modules_path, is_npm);
            JsCoq = this._config(opts);
            JsCoq.is_npm = is_npm;
            return new CoqManager(jscoq_ids, jscoq_opts)

        }
    };

})();

export { JsCoqLoader };

// Local Variables:
// js-indent-level: 4
// End:
