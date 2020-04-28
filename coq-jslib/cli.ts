// Build with
//  parcel watch --target node src/cli.ts

import path from 'path';
import commander from 'commander';
//import { FormatPrettyPrint } from '../ui-js/format-pprint';
import { JsCoqCompat } from './build/project';
import { Workspace } from './build/workspace';
import { Batch, CompileTask, BuildError } from './build/batch';



class CLI {

    opts: any
    workspace: Workspace

    progress: (msg: string, done?: boolean) => void
    errors = false;

    constructor(opts) {
        this.opts = opts;

        function progressTTY(msg: string, done: boolean = true) {
            process.stdout.write('\r' + msg + (done ? '\n' : ''));
        }
        function progressLog(msg: string, done: boolean = true) {
            if (done) console.log(msg);
        }
        this.progress = process.stdout.isTTY ? progressTTY : progressLog;
    }

    async prepare(opts = this.opts) {
        var workspace = new Workspace();
        if (opts.outdir)
            workspace.outDir = opts.outdir;
        if (!opts.nostdlib) {
            workspace.pkgDir = CLI.stdlibPkgDir();
            opts.loads.splice(0, 0, ...CLI.stdlibLoads());
        }
        if (!opts.compile)
            await workspace.loadDeps(opts.loads);
        if (opts.workspace)
            workspace.open(opts.workspace, opts.rootdir);
        else if (opts.rootdir)
            workspace.openProjectDirect(opts.package || path.basename(opts.rootdir),
                                        opts.rootdir, opts.top,
                                        opts.dirpaths.split(/[, ]/));
        else {
            console.error('what to build? specify either project or workspace.');
            throw new BuildError();
        }
        this.workspace = workspace;
    }

    async compile(opts = this.opts) {
        /* @todo
        var outdir = this.workspace.outDir;

        // Fire up the pod
        var icoq = new IcoqPodCLI();
        await icoq.boot();
        await icoq.loadPackages(opts.loads);
    
        for (let [pkgname, inproj] of Object.entries(this.workspace.projs)) {
            var task = new CompileTask(new BatchPod(icoq), inproj, <any>opts);

            await task.run(pkgname);
            var out = await out.toPackage(
                            opts.package || path.join(outdir, pkgname)),
                {pkg} = await out.save();
                
            this.progress(`wrote ${pkg.filename}.`, true);
        }
        */
    }

    async package(opts = this.opts) {
        var outdir = this.workspace.outDir,
            prep  = JsCoqCompat.transpilePluginsJs,
            postp = JsCoqCompat.backportManifest;

        this.workspace.searchPath.createIndex();  // to speed up coqdep

        for (let pkgname in this.workspace.projs) {
            this.progress(`[${pkgname}] `, false);
            var p = await this.workspace.projs[pkgname]
                    .toPackage(opts.package || path.join(outdir, pkgname),
                               undefined, prep, postp);
            try{
                await p.save();    
                this.progress(`wrote ${p.pkg.filename}.`, true);
            }
            catch (e) {
                this.progress(`error writing ${p.pkg.filename}:\n    ` + e);
                this.errors = true;
            }
        }
    }

    static stdlib() {
        return require('./metadata/coq-pkgs.json');
    }

    static stdlibLoads() {
        return [...Object.keys(this.stdlib().projects)].map(pkg => `+${pkg}`);
    }

    static stdlibPkgDir() {
        // assumes cli is run from `dist/` directory.
        return path.join(__dirname, 'coq-pkgs');
    }

}



async function main() {

    var loads: string[] = [];

    var opts = commander
        .name('wacoq')
        .version(require('../package.json').version, '-v, --version')
        .option('--workspace <w.json>',       'build projects from specified workspace')
        .option('--rootdir <dir>',            'toplevel directory for finding `.v` and `.vo` files')
        .option('--top <name>',               'logical name of toplevel directory')
        .option('--dirpaths <a.b.c>',         'logical paths containing modules (comma separated)', '')
        .option('--package <f.coq-pkg>',      'create a package (default extension is `.coq-pkg`)')
        .option('-d,--outdir <dir>',          'set default output directory')
        .option('--load <f.coq-pkg>',         'load package(s) for compilation and for module dependencies (comma separated, may repeat)')
        .option('--compile',                  'compile `.v` files to `.vo`')
        .option('--continue',                 'pick up from previous build')
        .option('--nostdlib',                 'skip loading the standard Coq packages')
        .on('option:load', pkg => loads.push(...pkg.split(',')))
        .parse(process.argv);

    if (opts.args[0] === 'build') opts.args.shift();

    if (opts.args.length > 0) {
        if (!opts.workspace && opts.args[0].endsWith('.json'))
            opts.workspace = opts.args.shift();
        else if (!opts.rootdir)
            opts.rootdir = opts.args.shift();

        if (opts.args.length > 0) {
            console.error('extraneous arguments: ', opts.args);
            return 1;
        }
    }

    opts.loads = loads;

    var cli = new CLI(opts);

    try {
        await cli.prepare();
        if (opts.compile)
            await cli.compile();
        else
            await cli.package();

        return cli.errors ? 1 : 0;
    }
    catch (e) {
        if (e instanceof BuildError) return 1;
        else throw e;
    }
}



main().then(rc => process.exit(rc || 0));