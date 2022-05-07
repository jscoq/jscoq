import { HeadlessCoqManager } from './headless';


class HeadlessCLI {

    constructor() { this.rc = 0; }

    installCommand(commander) {
        let requires = [], require_pkgs = [];
        return commander.command('run')
            .option('--noinit',                                 'start without loading the Init library')
            .option('--require <path>',                         'load Coq library path and import it (Require Import path.)')
            .option('--require-pkg <json>',                     'load a package and Require all modules included in it')
            .option('-l, --load-vernac-source <f.v>',           'load Coq file f.v.')
            .option('--compile <f.v>',                          'compile Coq file f.v')
            .option('-o <f.vo>',                                'use f.vo as output file name')
            .option('--inspect <f.symb.json>',                  'inspect global symbols and serialize to file')
            .option('-e <command>',                             'run a vernacular command')
            .option('-v, --verbose',                            'print debug log messages and warnings')
            .on('option:require',     path => { requires.push(path); })
            .on('option:require-pkg', json => { require_pkgs.push(json); })
            .action(async opts => {
                this.rc = await this.run({...opts, requires, require_pkgs});
            });
    }

    async run(opts) {
        var coq = new HeadlessCoqManager();

        if (!opts.noinit) coq.options.prelude = true;
        if (opts.verbose) coq.options.log_debug = coq.options.warn = true;

        if (opts.loadVernacSource) coq.load(opts.loadVernacSource);

        if (opts.E) coq.provider.enqueue(...opts.E.split(/(?<=\.)\s+/));

        if (opts.inspect) {
            coq.options.inspect = {};
            if (typeof opts.inspect === 'string')
                coq.options.inspect.filename = opts.inspect;
            if (opts.requires.length > 0)
                coq.options.inspect.modules = opts.requires.slice();
        }

        await coq.start();

        // `--require-pkg`s can only be handled after package manifests
        // have been loaded
        for (let pkg of opts.require_pkgs) {
            for (let mod of coq.packages.listModules(pkg)) {
                coq.require(mod);
                if (coq.options.inspect)
                    (coq.options.inspect.modules ??= []).push(mod);
            }
        }

        try {
            await coq.when_done.promise;
        }
        catch (e) { console.log("Aborted."); return 1; }

        return 0;
    }

}


export { HeadlessCLI }