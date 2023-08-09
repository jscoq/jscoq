import path from 'path';

import { Workspace } from "../cli/build/workspace";
import { JsCoqCompat } from '../cli/build/project';

export class BuildError { }

export interface Opts extends Workspace.Options {

    args: string[];
    nostdlib?: boolean
    workspace?: string;
    rootdir?: string;
    dirpaths?: string;
    loads?: string[];
}

export class Driver {

    opts: Opts;
    workspace: Workspace;

    progress: (msg: string, done?: boolean) => void
    errors = false;

    constructor(opts: Opts) {
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
        let topname = "";

        var workspace = new Workspace();
        
        // if (opts.outdir)
        //     workspace.outDir = opts.outdir;

        if (!opts.nostdlib) {
            workspace.pkgDir = Driver.stdlibPkgDir();
            opts.loads.splice(0, 0, ...Driver.stdlibLoads());
        }
        
        if(opts.loads) await workspace.loadDeps(opts.loads);

        if (opts.workspace)
            workspace.open(opts.workspace, opts.rootdir, opts);
        else if (opts.rootdir) {
            var dirpaths = opts.dirpaths.split(/[, ]/) as any[];
            dirpaths = dirpaths.map(d => ({logical: d, rec: false}));
            workspace.openProjectDirect(path.basename(opts.rootdir),
                                        opts.rootdir, topname, dirpaths);
        }
        else {
            console.error('what to build? specify either rootdir or workspace.');
            throw new BuildError();
        }
        this.workspace = workspace;
    }

    async package(opts = this.opts) {
        var outdir = this.workspace.outDir,
            prep  = JsCoqCompat.transpilePluginsJs;

        this.workspace.searchPath.createIndex();  // to speed up coqdep

        var bundle = this.bundle();

        for (let pkgname in this.workspace.projs) {
            var time_start = Date.now();
            this.progress(`[${pkgname}] `, false);

            var p = await this.workspace.projs[pkgname]
                    .toPackage(path.join(outdir, pkgname),
                               undefined, prep);

            try {
                await p.save(bundle && bundle.manifest);
                var time_elapsed = Date.now() - time_start;
                this.progress(`wrote ${p.pkg.filename} in ${time_elapsed} ms.`, true);
            }
            catch (e) {
                this.progress(`error writing ${p.pkg.filename}:\n    ` + e);
                this.errors = true;
            }
        }

        if (bundle) {
            bundle.save();
            this.progress(`wrote ${bundle.filename}.`, true);
        }
    }

    bundle() {
        if (this.workspace.bundleName)
            return this.workspace.createBundle(path.join(this.workspace.outDir, this.workspace.bundleName));

    }

    static stdlib() {
        return require('../../etc/pkg-metadata/coq-pkgs.json');
    }

    static stdlibLoads() {
        return [...Object.keys(this.stdlib().projects)].map(pkg => `+${pkg}`);
    }

    static stdlibPkgDir() {
        // assumes cli is run from `dist/` directory.
        return path.join(__dirname, '../coq-pkgs');
    }

}
