import fs from 'fs';
import path from 'path';
import { neatJSON } from 'neatjson';
import { CoqProject, SearchPath, ZipVolume } from './project';



class Workspace {

    projs: {[name: string]: CoqProject} = {}
    searchPath = new SearchPath()
    pkgDir = "bin/coq"
    outDir = ""

    open(jsonFilename: string, rootdir?: string) {
        try {
            var json = JSON.parse(<any>fs.readFileSync(jsonFilename));
            if (json.builddir) this.outDir = json.builddir;
            this.openProjects(json.projects, rootdir || json.rootdir);
        }
        catch (e) {
            console.warn(`cannot open workspace '${jsonFilename}': ${e}`);
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

    openProjects(pkgs: any, baseDir: string) {
        for (let pkg in pkgs) {
            var proj = new CoqProject(pkg).fromJson(pkgs[pkg], baseDir);
            this.addProject(proj);
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
        var desc = path.basename(filename).replace(/[.]json$/, '');
        if (!filename.match(/[.]json$/)) filename += '.json';

        return {
            manifest: {desc, deps: [], pkgs: [], chunks: []},
            filename,
            save() {
                fs.writeFileSync(this.filename, neatJSON(this.manifest));
            }
        };        
    }

}



export { Workspace }
