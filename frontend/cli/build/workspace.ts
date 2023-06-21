import fs from 'fs';
import path from 'path';
import { neatJSON } from 'neatjson';
import { CoqProject, SearchPath, SearchPathElement, ZipVolume } from './project';
import { BuildError } from './batch';

class Workspace {

    projs: {[name: string]: CoqProject} = {}
    searchPath = new SearchPath()
    bundleName: string
    pkgDir = "bin/coq"
    outDir = ""

    open(jsonFilename: string, rootdir?: string, opts: Workspace.Options = {}) {
        try {
            var json = JSON.parse(<any>fs.readFileSync(jsonFilename));
            if (json.builddir) this.outDir = json.builddir;
            if (json.bundle) this.bundleName = json.bundle
            this.openProjects(json.projects, rootdir || json.rootdir, opts);
        }
        catch (e) {
            console.warn(`cannot open workspace '${jsonFilename}': ${e}`);
            throw new BuildError();
        }
    }

    async loadDeps(pkgs: string[], baseDir = '') {
        for (let pkg of pkgs) {
            pkg = pkg.replace(/^[+]/, this.pkgDir.replace(/([^/])$/, '$1/'));
            if (!pkg.match(/[.][^./]+$/)) pkg += '.coq-pkg';

            var proj = new CoqProject(pkg).fromDirectory('',
                       await ZipVolume.fromFile(path.join(baseDir, pkg)));
            this.searchPath.addFrom(proj);
        }
    }

    addProject(proj: CoqProject) {
        this.projs[proj.name] = proj;
        this.searchPath.addFrom(proj);
        proj.searchPath = this.searchPath;
    }

    openProjects(pkgs: any, baseDir: string, opts: Workspace.Options = {}) {
        var errs = [], ok = false;;
        for (let pkg in pkgs) {
            try {
                var proj = new CoqProject(pkg).fromJson(pkgs[pkg], baseDir);
                this.addProject(proj);
                ok = true;
            }
            catch (e) {
                if (opts.ignoreMissing) errs.push([pkg, e]);
                else throw e;
            }
        }

        if (!ok) {
            for (let [pkg, e] of errs) {
                console.warn(`in project '${pkg}': ${e}`);
            }
            throw new Error('no valid projects found');
        }
    }

    openProjectDirect(nameOrPackage: string,
                      baseDir: string, prefix: string, dirPaths: string[]) {
        var name = path.basename(nameOrPackage).replace(/[.][^.]*$/, '');
        let proj = new CoqProject(name).fromJson({
            "": { prefix, 'dirpaths': dirPaths }
        }, baseDir);
        this.addProject(proj);
    }

    createBundle(filename: string) {
        var name = path.basename(filename).replace(/[.]json$/, '');
        if (!filename.match(/[.]json$/)) filename += '.json';

        return {
            manifest: {name, deps: [], pkgs: [], chunks: []},
            filename,
            save() {
                fs.writeFileSync(this.filename, neatJSON(this.manifest, null));
            }
        };
    }

    listPackageContents(nameFilter?: string | RegExp): Workspace.PackagesAndContents {
        var pkgs: Workspace.PackagesAndContents = {},
            pred = this._filt(nameFilter);
        for (let mod of this.searchPath.modulesByExt('.vo')) {
            var k = mod.pkg;
            if (k && pred(k)) (pkgs[k] ??= []).push(mod);
        }
        return pkgs;
    }

    _filt(e: undefined | string | RegExp): (s: string) => boolean {
        return e ? (typeof e === 'string' ? ((s: string) => s === e)
                                          : ((s: string) => !!s.match(e)))
                 : (() => true);
    }
}

namespace Workspace {
    export type Options = {
        ignoreMissing?: boolean
    };

    export type PackagesAndContents = {[pkg: string]: SearchPathElement[]};
}

export { Workspace }
