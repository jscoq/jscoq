//@ts-check
import { HeadlessCoqManager } from './headless';

var debugTime = false;

export class HeadlessCLI {

    constructor(base_path) {
        this.base_path = base_path;
        this.rc = 0;
    }

    installCommand(commander) {
        let loads = [], requires = [], require_pkgs = [];
        return commander.command('run')
            .option('--noinit',                                 'start without loading the Init library')
            .option('--load <f.coq-pkg>',                       'load package(s) and place in load path (comma separated, may repeat)')
            .option('--require <path>',                         'load Coq library path and import it (Require Import path.)')
            .option('--require-pkg <pkg>',                      'load package(s) and Require all modules included in it (comma separated, may repeat)')
            .option('-l, --load-vernac-source <f.v>',           'load Coq file f.v.')
            .option('--compile <f.v>',                          'compile Coq file f.v')
            .option('-o <f.vo>',                                'use f.vo as output file name')
            .option('--inspect <f.symb.json>',                  'inspect global symbols and serialize to file')
            .option('-e <command>',                             'run a vernacular command')
            .option('-v, --verbose',                            'print debug log messages and warnings')
            .on('option:load',        pkg => loads.push(...pkg.split(',')))
            .on('option:require',     path => requires.push(path))
            .on('option:require-pkg', pkg => require_pkgs.push(...pkg.split(',')))
            .action(async opts => {
                this.rc = await this.run({...opts, loads, requires, require_pkgs});
            });
    }

    async run(opts) {
        var coq = new HeadlessCoqManager(this.base_path);

        if (!opts.noinit) coq.options.prelude = true;
        if (opts.verbose) coq.options.log_debug = coq.options.warn = true;

        coq.options.all_pkgs.push(...opts.loads);
        coq.options.all_pkgs.push(...opts.require_pkgs.filter(x => !coq.options.all_pkgs.includes(x)));

        if (opts.loadVernacSource) coq.load(opts.loadVernacSource);

        for (let mod of opts.requires)
            coq.require(mod, true);

        if (opts.inspect) {
            coq.options.inspect = {};
            if (typeof opts.inspect === 'string')
                coq.options.inspect.filename = opts.inspect;
            if (opts.requires.length > 0)
                coq.options.inspect.modules = opts.requires.slice();
        }

        if (debugTime) { console.time('coq start'); }

        await coq.start();

        if (debugTime) { console.timeEnd('coq start'); }

        // `--require-pkg`s can only be handled after package manifests
        // have been loaded
        if (debugTime) { console.time('package import + commands'); }

        for (let pkg of opts.require_pkgs) {
            for (let mod of coq.packages.listModules(pkg)) {
                coq.require(mod);
                if (coq.options.inspect)
                    (coq.options.inspect.modules ??= []).push(mod);
            }
        }

        if (opts.E) coq.provider.enqueue(...opts.E.split(/(?<=\.)\s+/));

        try {
            await coq.when_done.promise;
            if (debugTime) { console.timeEnd('package import + commands'); }
        }
        catch (e) { console.log("Aborted."); return 1; }

        return 0;
    }
}

// Local Variables:
// js-indent-level: 4
// End:
