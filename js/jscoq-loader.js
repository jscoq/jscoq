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
    }
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

    loadJsCoq = function(base_path) {

        //loadCss(base_path + 'css/coq-log');
        //loadCss(base_path + 'external/CodeMirror/lib/codemirror');
        //loadCss(base_path + 'external/CodeMirror/theme/blackboard');
        //loadCss(base_path + 'external/CodeMirror/theme/blackboard');
        //loadCss(base_path + 'css/coq-base');
        //loadCss(base_path + 'css/coq-light');

        var files = ['external/CodeMirror/lib/codemirror',
                     'external/CodeMirror/mode/coq/coq',
                     'external/CodeMirror/keymap/emacs',
                     'external/d3.min',
                     'js/cm-provider',
                     'js/coq-packages',
                     'js/coq-panels',
                     'js/coq-manager'];

        var files = files.map(file => base_path + file);

        return files.reduce(function(prom, file) {
            return prom.then(loadJs(file))
        }, Promise.resolve());

    };

})();

// Local Variables:
// js-indent-level: 4
// End:
