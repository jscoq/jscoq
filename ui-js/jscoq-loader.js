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
    return function () {
        return new Promise(function (resolve, error) {
            var script    = document.createElement('script');
            script.type   = 'text/javascript';
            script.src    = js + '.js';
            script.onload = resolve;
            document.head.appendChild(script);
        });
    };
};

var loadJsCoq;

(function(){

    var loadCss = function(css) {

        var link   = document.createElement("link");
        link.href  = css+'.css';
        link.type  = "text/css";
        link.rel   = "stylesheet";
        link.media = "screen";

        document.head.appendChild(link);
    };


    // In order for jsCoq to work we need to load:
    // - Codemirror CSS [core+theme+coq]
    // - Codemirror JS  [core+coq+emacs]
    // - D3
    // - jsCoq = cm-provider + coq-packages + coq-manager

    loadJsCoq = function(base_path, node_modules_path) {

        base_path = base_path || "./";
        if (/[^/]$/.exec(base_path)) base_path += "/";

        node_modules_path = node_modules_path || base_path + "node_modules/";
        if (/[^/]$/.exec(node_modules_path)) node_modules_path += "/";

        loadCss(node_modules_path + 'codemirror/lib/codemirror');
        loadCss(node_modules_path + 'codemirror/theme/blackboard');
        loadCss(node_modules_path + 'codemirror/theme/blackboard');
        loadCss(node_modules_path + 'codemirror/addon/hint/show-hint');
        loadCss(base_path + 'ui-css/coq-log');
        loadCss(base_path + 'ui-css/coq-base');
        loadCss(base_path + 'ui-css/coq-light');

        var files = [node_modules_path + 'codemirror/lib/codemirror',
                     node_modules_path + 'codemirror/keymap/emacs',
                     node_modules_path + 'codemirror/addon/selection/mark-selection',
                     node_modules_path + 'codemirror/addon/edit/matchbrackets',
                     node_modules_path + 'codemirror/addon/hint/show-hint',
                     node_modules_path + 'jquery/dist/jquery.min',
                     node_modules_path + 'jszip/dist/jszip.min',
                     base_path + 'ui-external/CodeMirror-TeX-input/addon/hint/tex-input-hint',
                     base_path + 'coq-js/jscoq',
                     base_path + 'ui-js/mode/coq-mode',
                     base_path + 'ui-js/addon/company-coq',
                     base_path + 'ui-js/cm-provider',
                     base_path + 'ui-js/format-pprint',
                     base_path + 'ui-js/coq-packages',
                     base_path + 'ui-js/coq-layout-classic',
                     base_path + 'ui-js/coq-manager'];

        return files.reduce(function(prom, file) {
            return prom.then(loadJs(file));
        }, Promise.resolve());
    };

})();

// Local Variables:
// js-indent-level: 4
// End:
