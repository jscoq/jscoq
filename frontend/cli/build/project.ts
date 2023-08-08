import path from 'path';
import { FSInterface, fsif_native } from './fsif';
import { CoqDep } from './coqdep';
import arreq from 'array-equal';
import type JSZip from 'jszip';
import { zipSync, ZipOptions } from 'fflate';
import { neatJSON } from 'neatjson';
import DEFLATE from 'jszip/lib/compressions';
import { inflateRaw } from 'pako';
import child_process from 'child_process';
import { inspect } from 'util';
const mkdirp = require('mkdirp').sync;
const fs = fsif_native.fs;

class CoqProject {

    volume: FSInterface
    name: string
    deps: string[]
    searchPath: SearchPath
    opts: PackageOptions

    _modules: SearchPathElement[]

    constructor(name?: string, volume: FSInterface = fsif_native) {
        this.volume = volume;
        this.name = name;
        this.deps = [];
        this.searchPath = new SearchPath(volume);

        this.opts = {
            json: { padding: 1, afterColon: 1, afterComma: 1, wrap: 80 },
            zip: { }
        };
    }

    fromJson(json: {[root: string]: {prefix?: string, dirpaths?: DirPathFlag[]}},
             baseDir: string = '', volume: FSInterface = this.volume) {
        for (let root in json) {
            var prefix = this.toDirPath(json[root].prefix || "");

            for (let sub of json[root].dirpaths || [""]) {
                var dirpath = this.toDirPath(sub),
                    physical = volume.path.join(baseDir, root, ...dirpath),
                    logical = prefix.concat(dirpath),
                    pel = {volume, physical, logical, pkg: this.name};

                if (typeof sub === 'string' || sub.rec)
                    this.searchPath.addRecursive(pel);
                else
                    this.searchPath.add(pel);
            }
        }
        return this;
    }

    fromDirectory(dir: string = '', volume = this.volume) {
        try {
            var coqmf = volume.fs.readFileSync(volume.path.join(dir, '_CoqProject'), 'utf-8');
        } catch (e) { }

        if (coqmf) return this.fromCoqMF(coqmf, dir, volume)
        else {
            this.searchPath.addRecursive({volume,
                        physical: dir, logical: '', pkg: this.name});
            return this;
        }
    }

    /**
     * Configures a project from flags in _CoqProject format, i.e. -R ..., -Q ...,
     * and list of .v files.
     * @param {string} coqProjectText content of _CoqProject definition file
     * @param {string} baseDir project root directory (usually the one containing _CoqProject)
     * @param {FSInterface} volume containing volume
     */
    fromCoqMF(coqProjectText: string, baseDir: string = '', volume: FSInterface = this.volume) {
        var pkg = this.name, modules = [];
        for (let line of coqProjectText.split(/\n+/)) {
            var mo = /^\s*(-[RQ])\s+(\S+)\s+(\S+)/.exec(line);
            if (mo) {
                var [flag, physical, logical] = [mo[1], mo[2], mo[3]];
                physical = volume.path.join(baseDir, physical);
                if (flag === '-R')
                    this.searchPath.addRecursive({volume, physical, logical, pkg});
                else
                    this.searchPath.add({volume, physical, logical, pkg});
            }
            else {
                for (let mo of line.matchAll(/\S+[.]v/g)) modules.push(mo[0]);
            }
        }
        if (modules.length > 0) this.setModules(modules);
        return this;
    }

    setModules(mods: (string | SearchPathElement)[]) {
        this._modules = mods.map(mod =>
            typeof mod === 'string'
                ? {volume: this.volume, physical: mod, 
                   logical: this.searchPath.toLogical(mod), pkg: this.name}
                : mod
        );
    }

    computeDeps() {
        var coqdep = new CoqDep();
        coqdep.searchPath = this.searchPath;

        coqdep.processModules(this.modules());
        return coqdep;
    }

    modules() {
        return this._modules || this.searchPath.modulesOf(this.name);
    }

    modulesByExt(ext: string) {
        return this.modulesByExts([ext]);
    }

    *modulesByExts(exts: string[]) {
        for (let mod of this.modules())
            if (exts.some(ext => mod.physical.endsWith(ext))) yield mod;
    }
    
    listModules(exts?: string | string[]) {
        if (typeof exts === 'string') exts = [exts];
        return this.searchPath._listNames(
            exts ? [...this.modulesByExts(exts)] : this.modules());
    }

    createManifest() {
        var mdeps = this.computeDeps().depsToJson(),
            modules:any = {};
        for (let k of this.listModules())
            modules[k] = mdeps[k] ? {deps: mdeps[k]} : {};
        return {name: this.name, deps: this.deps, modules};
    }

    toDirPath(flag: DirPathFlag) {
        return this.searchPath.toDirPath(
            (typeof flag === 'string') ? flag : flag.logical);
    }

    /**
     *  Read project file and store all .v files in transient folders
     * according to their logical paths.
     */
    copyLogical(store = new InMemoryVolume()) {
        for (let {volume, physical, logical} of this.modulesByExt('.v')) {
            store.fs.writeFileSync(
                `/${logical.join('/')}.v`, volume.fs.readFileSync(physical));
        }

        return new CoqProject(this.name, store).fromDirectory('/');
    }
  
    async toZip(withManifest?: string, extensions = ['.vo', '.cma'],
                prep: PackagePreprocess = (x=>[x])) {
        var z = new Zipped(this.opts.zip);

        if (withManifest) z.writeFileSync('coq-pkg.json', withManifest);

        for (let emod of this.modulesByExts(extensions)) {
            for (let mod of prep(emod)) {
                var ext = mod.ext || mod.physical.match(/[.][^.]+$/)[0];
                try {
                    z.writeFileSync(mod.logical.join('/') + ext,
                        mod.payload || mod.volume.fs.readFileSync(mod.physical));
                }
                catch (e) {
                    console.warn(`skipped ${mod.physical} (${e})`);
                }
            }
        }
        return z;
    }

    async toPackage(filename: string = this.name, extensions?: string[],
                    prep: PackagePreprocess = (x=>[x]),
                    postp: PackagePostprocess = (x=>x))
            : Promise<PackageResult> {

        if (!filename.match(/[.][^./]+$/)) filename += '.coq-pkg';
        
        var manifest = postp(this.createManifest(), filename),
            manifest_fn = filename.replace(/[.][^./]+$/, '.json'),
            manifest_json = neatJSON(manifest, this.opts.json);

        return new PackageResult(
                {filename, zip: await this.toZip(manifest_json, extensions, prep)},
                {filename: manifest_fn, json: manifest_json, object: manifest}
        );
    }

}

type DirPathFlag = string | {logical: string, rec?: boolean};

type PackageOptions = {
    json: any /* neatjson options */
    zip: ZipOptions
};

class Zipped {
    z: {[filename: string]: Uint8Array} = {}
    opts?: ZipOptions

    constructor(opts?: ZipOptions) { this.opts = opts; }
    writeFileSync(filename: string, content: string | Uint8Array) {
        if (typeof content === 'string')
            content = new TextEncoder().encode(content);
        this.z[filename] = content;
    }
    zipSync() {
        return zipSync(this.z);
    }
}

class PackageResult {
    pkg:      {filename: string, zip: Zipped}
    manifest: {filename: string, json: string, object: any}

    constructor(pkg:      {filename: string, zip: Zipped},
                manifest: {filename: string, json: string, object: any}) {
        this.pkg = pkg;
        this.manifest = manifest;
    }

    async save(bundle?: {chunks?: any[]}): Promise<PackageResult> {
        mkdirp(path.dirname(this.pkg.filename));
        if (bundle) {
            if (!bundle.chunks) bundle.chunks = [];
            bundle.chunks.push(this.manifest.object);
        }
        else {
            mkdirp(path.dirname(this.manifest.filename));
            fs.writeFileSync(this.manifest.filename, this.manifest.json);
        }
        fs.writeFileSync(this.pkg.filename, this.pkg.zip.zipSync());
        return this;
    }
};

type PackagePreprocess = (mod: SearchPathElement) => (SearchPathElement & {ext?: string, payload?: Uint8Array})[];
type PackagePostprocess = (manifest: any, archive?: string) => any;


class SearchPath {

    volume: FSInterface
    path: SearchPathElement[]

    moduleIndex: ModuleIndex
    packageIndex: PackageIndex

    constructor(volume: FSInterface = fsif_native) {
        this.volume = volume;
        this.path = [];
    }

    add({volume, physical, logical, pkg}: SearchPathAddParameters) {
        volume = volume || this.volume;
        logical = this.toDirPath(logical);
        if (!this.has({volume, physical, logical, pkg}))
            this.path.push({volume, logical, physical, pkg});
    }

    addRecursive({volume, physical, logical, pkg}: SearchPathAddParameters) {
        volume = volume || this.volume;
        logical = this.toDirPath(logical);
        this.add({volume, physical, logical, pkg});
        for (let subdir of volume.fs.readdirSync(physical)) {
            var subphysical = volume.path.join(physical, subdir);
            if (volume.fs.statSync(subphysical).isDirectory())
                this.addRecursive({ volume,
                                    physical: subphysical,
                                    logical: logical.concat([subdir]),
                                    pkg });
        }
    }

    addFrom(other: SearchPath | CoqProject) {
        if (other instanceof CoqProject) other = other.searchPath;
        this.path.push(...other.path);
    }

    has({volume, physical, logical, pkg}: SearchPathAddParameters) {
        if (logical !== undefined) logical = this.toDirPath(logical);
        return this.path.find(pel => {
            (volume   === undefined || pel.volume   ===   volume) &&
            (physical === undefined || pel.physical ===   physical) &&
            (logical  === undefined || arreq(pel.logical, logical)) &&
            (pkg      === undefined || pel.pkg      ===   pkg)
        })
    }

    toLogical(filename: string) {
        var dir = this.volume.path.dirname(filename), 
            base = this.volume.path.basename(filename).replace(/[.]vo?$/, '');
        for (let {logical, physical} of this.path) {
            if (physical === dir) return logical.concat([base])
        }
    }

    toDirPath(name: string | string[]) {
        return (typeof name === 'string') ? name.split('.').filter(x => x) : name;
    }

    *modules(): Generator<SearchPathElement> {
        for (let {volume, logical, physical, pkg} of this.path) {
            for (let fn of volume.fs.readdirSync(physical)) {
                if (fn.match(/[.](vo?|cma)$/)) {
                    let base = fn.replace(/[.](vo?|cma)$/, ''),
                        fp = volume.path.join(physical, fn)
                    yield { volume,
                            logical: logical.concat([base]),
                            physical: fp,
                            pkg };
                }
            }
        }
    }

    *modulesOf(pkg: string=undefined) {
        for (let mod of this.modules())
            if (mod.pkg === pkg) yield mod;
    }

    modulesByExt(ext: string) {
        return this.modulesByExts([ext]);
    }

    *modulesByExts(exts: string[]) {
        for (let mod of this.modules())
            if (exts.some(ext => mod.physical.endsWith(ext))) yield mod;
    }

    listModules() {
        return this._listNames(this.modules());
    }

    listModulesOf(pkg: string=undefined) {
        return this._listNames(this.modulesOf(pkg));
    }

    _listNames(modules: Iterable<SearchPathElement>) {
        let s = new Set<string>(),
            key = (mod: SearchPathElement) => mod.logical.join('.')
                    + (mod.physical.endsWith('.cma') ? '@cma' : '');
        for (let mod of modules)
            s.add(key(mod));
        return s;
    }

    *findModules(prefix: string | string[], name: string | string[], exact=false) {
        yield* this.moduleIndex 
            ? this.moduleIndex.findModules(prefix, name, exact)
            : this._findModules(prefix, name, exact);
        yield* this._findExtern(prefix, name, exact);
    }

    *_findModules(prefix: string | string[], name: string | string[], exact=false) {
        var lprefix = this.toDirPath(prefix) || [],
            lsuffix = this.toDirPath(name);

        let startsWith = (arr, prefix) => arreq(arr.slice(0, prefix.length), prefix);
        let endsWith = (arr, suffix) => suffix.length == 0 || arreq(arr.slice(-suffix.length), suffix);

        let matches = exact ? name => arreq(name, lprefix.concat(lsuffix))
                            : name => startsWith(name, lprefix) &&
                                      endsWith(name, lsuffix);

        for (let mod of this.modules())
            if (matches(mod.logical)) yield mod;
    }

    *_findExtern(prefix: string | string[], name: string | string[], exact=false) {
        if (this.packageIndex) {
            for (let k of this.packageIndex.findModules(prefix, name, exact))
                yield {volume: null, physical: null, logical: k.split('.'), pkg: '+'};
        }
    }

    createIndex() {
        this.moduleIndex = new ModuleIndex();
        for (let mod of this.modules())
            this.moduleIndex.add(mod);
        return this.moduleIndex;
    }

}

type SearchPathAddParameters = {
    volume?: FSInterface
    logical: string[] | string
    physical: string
    pkg?: string
};

type SearchPathElement = {
    volume: FSInterface
    logical: string[]
    physical: string
    pkg?: string
};


/**
 * @todo there is some duplication with backend's PackageIndex.
 */
class ModuleIndex {

    index: Map<string, SearchPathElement>

    constructor() {
        this.index = new Map();
    }

    add(mod: SearchPathElement) {
        let key = (mod: SearchPathElement) => mod.logical.join('.');
        this.index.set(key(mod), mod);
    }

    *findModules(prefix: string | string[], suffix: string | string[], exact=false) {
        if (Array.isArray(prefix)) prefix = prefix.join('.');
        if (Array.isArray(suffix)) suffix = suffix.join('.');

        prefix = prefix ? prefix + '.' : '';
        if (exact) {
            var lu = this.index.get(prefix + suffix);
            if (lu) yield lu;
        }
        else {
            var dotsuffix = '.' + suffix;
            for (let [k, mod] of this.index.entries()) {
                if (k.startsWith(prefix) && (k == suffix || k.endsWith(dotsuffix)))
                    yield mod;
            }
        }
    }
}


interface PackageIndex {
    findModules(prefix: string | string[], suffix: string | string[],
                exact?: boolean): Iterable<string>;
    findPackageDeps(prefix: string | string[], suffix: string | string[],
                    exact?: boolean): Set<string>;
}


abstract class StoreVolume implements FSInterface {

    fs: typeof fs
    path: typeof path

    abstract _files: Iterable<string>

    constructor() {
        this.fs = <any>this;
        this.path = fsif_native.path;
    }

    readdirSync(dir: string) {
        let d = [];
        if (dir !== '' && !dir.endsWith('/')) dir = dir + '/';
        for (let fn of this._files) {
            if (fn.startsWith(dir)) {
                var steps = fn.substring(dir.length).split('/').filter(x => x);
                if (steps[0] && !d.includes(steps[0]))
                    d.push(steps[0]);
            }
        }
        return d;
    }

    statSync(fp: string) {
        var fpSlash = fp.replace(/(^|([^/]))$/, '$2/');
        for (let k of this._files) {
            if (k.startsWith(fpSlash)) return {isDirectory: () => true};
        }
        throw new Error(`ENOENT: '${fp}'`);
    }

}


class InMemoryVolume extends StoreVolume {

    fileMap: Map<string, Uint8Array>

    constructor() {
        super();
        this.fileMap = new Map();
    }

    get _files() {
        return this.fileMap.keys();
    }

    writeFileSync(filename: string, content: Uint8Array | string) {
        if (typeof content === 'string') content = new TextEncoder().encode(content);
        this.fileMap.set(filename, content);
    }

    readFileSync(filename: string, encoding?: string) {
        var contents = this.fileMap.get(filename);
        if (contents)
            return encoding ? new TextDecoder().decode(contents) : contents;
        else
            throw new Error(`ENOENT: '${filename}'`);
    }

    statSync(fp: string) {
        var file = this.fileMap.get(fp);
        if (file) return {isDirectory: () => false};
        else return super.statSync(fp);
    }

    renameSync(oldFilename: string, newFilename: string) {
        if (oldFilename !== newFilename) {
            this.fileMap.set(newFilename, this.readFileSync(oldFilename) as Uint8Array);
            this.fileMap.delete(oldFilename);
        }
    }

    unlinkSync(filename: string) {
        this.fileMap.delete(filename);
    }

}


class ZipVolume extends StoreVolume {
    zip: JSZip  /** @todo use fflate */

    _files: string[]

    constructor(zip: JSZip) {
        super();
        this.zip = zip;

        this._files = [];
        this.zip.forEach((fn: string) => this._files.push(fn));
    }

    readFileSync(filename: string, encoding?: string) {
        var entry = this.zip.files[filename];
        if (entry)   return this._inflateSync(entry);
        else         throw new Error(`ENOENT: ${filename}`);
    }

    statSync(fp: string) {
        var entry = this.zip.files[fp] || this.zip.files[fp + '/'];
        if (entry)   return { isDirectory() { return entry && entry.dir; } };
        else         return super.statSync(fp);
    }

    static async fromFile(zipFilename: string) {
        const JSZip = _default(await import('jszip'));
        return new ZipVolume(
            await JSZip.loadAsync((0 || fs.readFileSync)(zipFilename)));
    }

    static async fromBlob(blob: Blob | Promise<Blob>) {
        const JSZip = _default(await import('jszip'));;
        return new ZipVolume(await JSZip.loadAsync(<any>blob));
    }

    _inflateSync(entry: any) {
        if (entry._data.compression == DEFLATE)
            return inflateRaw(entry._data.compressedContent);
        else /* STORE */
            return entry._data.compressedContent;
    }

}

function _default<T>(m: {default: T}): T { // Parcel compat
    return m.default || (<any>m);
}


class JsCoqCompat {

    /**
     * Runs js_of_ocaml to convert .cma bytecode files to .cma.js.
     * @param mod 
     */
    static transpilePluginsJs(mod: SearchPathElement) {
        if (mod.physical.endsWith('.cma')) {
            const infile = mod.physical, outfile = `${infile}.js`,
                  flags = JsCoqCompat.flags();
            // assumes volume is fsif_native...
            child_process.execSync(`js_of_ocaml ${flags} --wrap-with-fun= -o ${outfile} ${infile}`);
            return [mod, /*{...mod, payload: new Uint8Array(*empty*)},*/
                    {...mod, physical: outfile, ext: '.cma.js'}];
        }
        else return [mod];
    }

    static flags() {
        return (process.env['JSCOQ_DEBUG'] !== undefined) ?
            '--pretty --noinline --disable shortvar --debug-info' : '';
    }

    /**
     * Converts a package manifest to (older) jsCoq format.
     * @param manifest original JSON manifest
     * @param pkgfile `.coq-pkg` archive filename
     * @obsolete Package manifest format is now consistent between js/wa.
     */
    static backportManifest(manifest: any, pkgfile: string) {
        var d: {[dp: string]: string[]} = {}
        for (let k in manifest.modules) {
            var [dp, mod] = k.split(/[.]([^.]+)$/); 
            if (!mod) { mod = dp; dp = ""; }
            (d[dp] = d[dp] || []).push(mod); 
        }
        var pkgs = Object.entries(d).map(([k,v]) => ({ 
            pkg_id: k.split('.'),
            vo_files: v.map(x => !x.endsWith('@cma') && [`${x}.vo`, null]).filter(x => x),
            cma_files: v.map(x => x.endsWith('@cma') && [x, null]).filter(x => x)
        }));
        var modDeps = {};
        for (let k in manifest.modules) {
            var deps = manifest.modules[k].deps;
            if (deps) modDeps[k] = deps;
        }
        var archive = manifest.archive || (pkgfile && path.basename(pkgfile));
        return {name: manifest.name, deps: manifest.deps || [],
                archive, pkgs, modDeps};
    }

}

export { CoqProject, SearchPath, SearchPathElement,
         PackageOptions, ModuleIndex, InMemoryVolume, ZipVolume, JsCoqCompat }
