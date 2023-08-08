//@ts-check
"use strict"

// Main Frontend start point
import { CoqManager } from './coq-manager.js';

// Exports
export { CoqWorker } from '../../../backend';
export { PackageManager } from './coq-packages.js';
export { CmCoqProvider, Deprettify } from './cm-provider.js';
export { FormatPrettyPrint } from '../../format-pprint/js/index.js';

const scriptDir = import.meta.url.replace(/[^/]*$/, '');

const JsCoq = {
    backend: 'js',  /* 'js' or 'wa' */

    // js worker path, to be replaced soon
    base_path: scriptDir ? `${scriptDir}../../` : "./",

    // Main entry point
    async start(...args) {
        let { jscoq_ids, jscoq_opts } = this._getopts('start', ...args);
        this.base_path = jscoq_opts.base_path;
        //@ts-ignore
        window.JsCoq = this; // atm this is still needed by UI addons
        return new CoqManager(jscoq_ids, jscoq_opts);
    },

    /**
     * Parses "command line"-style arguments to `start()` and `load()`.
     * @param method name of method that invoked `_getopt` (for logging).
     * @param  {...any} args a sequence of values including
     *  * (string) base path for jsCoq resources
     *  * (string) node_modules path for library resources
     *  * (string[]) elements ids / CSS selectors designating interactive snippets
     *  * (object) options object passed to `CoqManager` (see `coq-manager.js`)
     * All arguments are optional. Assignment is done according to type.
     * @returns
     */
    _getopts(method, ...args) {

        var base_path = undefined,
            node_modules_path = undefined,
            jscoq_ids = ['ide-wrapper'],
            jscoq_opts = {};

        // Interpret args according to spec, skip missing values
        if (typeof args[0] === 'string') base_path = args.shift();
        if (typeof args[0] === 'string') node_modules_path = args.shift();
        if (Array.isArray(args[0])) jscoq_ids = args.shift();
        if (args[0]) jscoq_opts = args.shift();

        if (args.length > 0) console.warn(`too many arguments to JsCoq.${method}()`);

        // Backend setup
        jscoq_opts.backend = jscoq_opts.backend || this.backend;

        // Set base and node_modules path from options if not given, use defaults
        jscoq_opts.base_path = base_path || jscoq_opts.base_path || this.base_path;

        return {jscoq_ids, jscoq_opts}
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

export { JsCoq, CoqManager }

// Local Variables:
// js-indent-level: 4
// End:
