import fs from 'fs';
import os from 'os';
import path from 'path';
import { EventEmitter } from 'events';
import { inspect } from 'util';
import mkdirp from 'mkdirp';
import * as find from 'find';
import glob from 'glob';
// There is some esbuild issue with this package
import unzip from 'fflate-unzip/src/index';

// Backend imports
import { Future } from '../../../backend/future';
import { CoqWorker } from '../../../backend/coq-worker';
import { CoqIdentifier } from '../../../backend/coq-identifier';

// Frontend imports, this seems common to the frontends
import { arreq_deep } from '../../common/etc.js';

// Frontend imports, specific to the layout but we should refactor
import { FormatPrettyPrint } from '../../format-pprint/js';
import { existsDir } from './../../cli/build/sdk/shutil';

// Where to put this?
//
// EJGA: indeed this needs refactoring. I think that the right place
// for both modules is in the backend/ directory, at least the
// CoqProject type is defined canonically by Coq in the OCaml side, so
// while we can allow different implementations, we should make sure
// the interfaces for both are the same.
import { FSInterface, fsif_native } from '../../cli/build/fsif';
import { CoqProject } from '../../cli/build/project';

class HeadlessCoqWorker extends CoqWorker {

    constructor(base_path) {
        var backend : 'js' = 'js'
        super(base_path, null, HeadlessCoqWorker.instance(), backend);
        this.when_created.then(() => {
            this.worker.onmessage = this._handler = evt => {
                process.nextTick(() => this.coq_handler({data: evt}));
            };
        });
    }

    static instance() {
        let workerPath = path.join(__dirname, '../backend/jsoo/jscoq_worker.bc.js'),
            jsCoq = Require.cjs(workerPath).jsCoq;
        /** @oops monkey-patch to make it look like a Worker instance */
        jsCoq.addEventListener = (_: "message", handler: () => void) =>
            jsCoq.onmessage = handler;
        return jsCoq;
    }
}

/** Used to force Node into loading a file as CJS regardless of extension */
namespace Require {

    export function cjs(filename: string) {
        return fromString(fs.readFileSync(filename, 'utf-8'), filename);
    }

    function fromString(content: string, filename: string) {
        // @ts-ignore
        let m = new (module.constructor)();
        m._compile(content, filename);
        return m.exports;
    }
}

/**
 * A manager that handles Coq events without a UI.
 */
class HeadlessCoqManager {
    coq: CoqWorker & { options?: any};
    volume: FSInterface
    provider: any
    pprint: FormatPrettyPrint
    packages: PackageDirectory
    project: CoqProject
    options: any

    doc: any[]
    when_done: Future<void>

    startup_time: number
    startup_timeEnd: number

    static SDK_DIR = '/tmp/jscoq'

    constructor(basePath: string, sdkDir = HeadlessCoqManager.SDK_DIR) {
        this.startup_time = Date.now();
        this.volume = fsif_native;

        this.coq = new HeadlessCoqWorker(basePath);
        this.coq.observers.push(this);
        this.provider = new QueueCoqProvider();
        this.pprint = new FormatPrettyPrint();
        this.packages = new PackageDirectory(sdkDir);
        this.project = new CoqProject(undefined, this.volume);

        this.options = {
            prelude: false,
            top_name: undefined,  /* default: set by worker (JsCoq) */
            implicit_libs: true,
            all_pkgs: ['init', 'coq-base', 'coq-collections', 'coq-arith', 'coq-reals', 'ltac2'],
            pkg_path: this.findPackageDir(),
            inspect: false,
            log_debug: false,
            warn: true
        };

        this.coq.options = this.options;

        this.doc = [];

        this.when_done = new Future();

        this.packages.on('message', ev => {
            if (this.options.log_debug) console.log(ev.data);
        });
    }

    async start() {
        this.packages.clear();
        await this.packages.loadPackages(this.options.all_pkgs.map(pkg =>
            this.getPackagePath(pkg)));

        this.project.searchPath.addRecursive(
            {physical: `${this.packages.dir}`, logical: ''});

        for (let mod of this.project.modulesByExt('.cma')) {
            this.coq.register(mod.physical);
        }

        // Initialize Coq
        let init_opts = {
                top_name: this.options.top_name,
                implicit_libs: this.options.implicit_libs,
                lib_path: this.getLoadPath()
            },
            doc_opts = {
                lib_init: this.options.prelude ? ["Coq.Init.Prelude"] : []
            };

        this.coq.init(init_opts, doc_opts);
    }

    getPackagePath(pkg: string) {
        var filenames = [pkg, `${pkg}.coq-pkg`],
            dirs = ['', this.options.pkg_path];
        for (let d of dirs) {
            for (let fn of filenames) {
                let fp = path.join(d, fn);
                try {
                    if (fs.statSync(fp).isFile()) return fp;
                }
                catch { }
            }
        }
        throw new Error(`package not found: '${pkg}'`);
    }

    getLoadPath() {
        return this.project.searchPath.path.map(
            ({physical, logical}) => [logical, [physical, '.']]);
    }

    goNext() {
        var last_stm = this.doc[this.doc.length - 1],
            stm = this.provider.getNext(last_stm);

        if (stm) {
            var last_sid = (last_stm && last_stm.coq_sid) || 1;
            stm.coq_sid = last_sid + 1;
            this.doc.push(stm);
            this.coq.add(last_sid, stm.coq_sid, stm.text);
            return true;
        }
        else return false;
    }

    eof() {

        this.startup_timeEnd = Date.now();

        var inspect = this.options.inspect;
        if (inspect) this.performInspect(inspect);

        if (this.options.compile) {
            let input = this.options.compile.input,
                output = this.options.compile.output || '._JsCoq.vo';
            if (input)
                this.coq.sendCommand(['Load', input])
            this.coq.sendCommand(['Compile', output]);
        }
        else
            this.when_done.resolve(null);
    }

    require(module_name: string, import_=false) {

        // EJGA: CoqWorker::init has built-in support for this, so no
        // need to hack the document itself.

        this.provider.enqueue(`Require ${import_ ? "Import " : ""}${module_name}.`);
    }

    load(vernac_filename: string) {
        // Relative paths must start with './' for Load command
        if (!this.volume.path.isAbsolute(vernac_filename) && !/^[.][/]/.exec(vernac_filename))
            vernac_filename = `./${vernac_filename}`;
        this.provider.enqueue(`Load "${vernac_filename}".`);
    }

    retract() {
        let first_stm = this.doc[0];
        if (first_stm && first_stm.coq_sid)
            this.coq.cancel(first_stm.coq_sid);
        else
            this.coq.cancel(1);  // XXX
    }

    terminate() {
        this.retract();
        let idx = this.coq.observers.indexOf(this);
        if (idx > -1)
            this.coq.observers.splice(idx, 1);
    }

    performInspect(inspect) {
        var time_start = Date.now();
        var out_fn = inspect.filename || 'inspect.symb',
            query_filter = inspect.modules ?
                (id => inspect.modules.some(m => this._identifierWithin(id, m)))
              : (id => true);
        this.coq.inspectPromise(0, ["All"]).then((results : any []) => {
            var symbols = results.map(fp => CoqIdentifier.ofQualifiedName(fp))
                            .filter(query_filter);
            this.volume.fs.writeFileSync(out_fn, JSON.stringify({lemmas: symbols}));
            var time_elapsed = Date.now() - time_start;
            console.log(`Wrote '${out_fn}' (${symbols.length} symbols) in ${time_elapsed} ms (init: ${this.startup_timeEnd - this.startup_time} ms).`);
        })
        .catch((err: Error) => console.error(err));
    }

    coqCoqInfo() { }

    coqReady() {
        if (this.options.log_debug)
            console.log("Coq worker ready.")

        this.goNext() || process.nextTick(() => this.eof());
    }

    coqLog([lvl], msg) {
        if (lvl != 'Debug' || this.options.log_debug)
            console.log(`[${lvl}] ${this.pprint.pp2Text(msg)}`);
    }

    coqPending(sid) {
        var idx = this.doc.findIndex(stm => stm.coq_sid === sid);
        if (idx >= 0) {
            var stm = this.doc[idx],
                prev_stm = this.doc[idx - 1];
            this.coq.resolve((prev_stm && prev_stm.coq_sid) || 1, sid, stm.text);
        }
    }

    coqAdded(sid) {
        var last_stm = this.doc[this.doc.length - 1];
        if (last_stm && last_stm.coq_sid === sid && !last_stm.added) {
            last_stm.added = true;
            this.coq.exec(sid);
        }
    }

    feedProcessed(sid) {
        if (this.options.log_debug)
            console.log("Processed",sid);

        var last_stm = this.doc[this.doc.length - 1];
        if (last_stm && last_stm.coq_sid === sid && !last_stm.executed) {
            last_stm.executed = true;
            this.goNext() || process.nextTick(() => this.eof());
        }
    }

    coqGot(filename, buf) {
        if (!this.when_done.isFailed()) {
            this.coq.put(filename, buf);
            console.log(` > ${filename}`);
            this.when_done.resolve(null);
        }
    }

    coqCancelled(sid) {
        if (this.options.log_debug)
            console.log('Canceled', sid);
    }

    coqCoqExn({loc, pp: msg}) {
        var loc_repr = this._format_loc(loc);
        console.error(`[Exception] ${this.pprint.pp2Text(msg)}${loc_repr}`);
        this.when_done.reject({loc, error: msg});
    }

    feedFileLoaded() { }
    feedFileDependency() { }

    feedProcessingIn() { }

    feedAddedAxiom() { }

    feedMessage(sid, [lvl], loc, msg) {
        console.log('-'.repeat(60));
        console.log(`[${lvl}] ${this.pprint.pp2Text(msg).replace('\n', '\n         ')}`);
        console.log('-'.repeat(60) + this._format_loc(loc));
    }

    findPackageDir(dirname = 'coq-pkgs') {
        var searchPath = ['.', '..', '../..']
                         .map(rel => path.join(__dirname, rel));

        for (let path_el of searchPath) {
            for (let dirpat of ['.', '_build/jscoq+*']) {
                for (let rel of glob.sync(dirpat, {cwd: path_el})) {
                    var dir = path.join(path_el, rel, dirname);
                    if (this._isDirectory(dir))
                        return dir;
                }
            }
        }
        return dirname; // fallback
    }

    _isDirectory(path) {
        try { return this.volume.fs.statSync(path).isDirectory(); }
        catch { return false; }
    }

    _identifierWithin(id, modpath) {
        var prefix = (typeof modpath === 'string') ? modpath.split('.') : modpath;
        return arreq_deep(id.prefix.slice(0, prefix.length),prefix);
    }

    _format_loc(loc) {
        return loc ?
            (loc.fname && loc.fname[0] === 'InFile' ?
                `\n\t(at ${loc.fname[1]}:${loc.line_nb})` :
                `\n${JSON.stringify(loc)}`) : '';
    }

}

/**
 * A provider stub that just holds a list of sentences to execute.
 */
class QueueCoqProvider {
    queue: any[]

    constructor() {
        this.queue = [];
    }

    enqueue(...sentences) {
        for (let s of sentences) {
            if (typeof s === 'string') s = {text: s};
            this.queue.push(s);
        }
    }

    getNext(prev) {
        if (!prev) return this.queue[0];

        for (let i = 0; i < this.queue.length; i++) {
            if (this.queue[i] === prev) return this.queue[i+1];
        }

        return undefined;
    }

    clone() {
        var c = new QueueCoqProvider();
        c.queue = this.queue.slice();
        return c;
    }
}

class PackageDirectory extends EventEmitter {
    dir: string
    packages_by_name: {[name: string]: PackageManifest}
    packages_by_uri: {[name: string]: PackageManifest}
    _plugins: Promise<void>

    constructor(dir) {
        super();

        this.dir = dir;
        this.packages_by_name = {};
        this.packages_by_uri = {};
    }

    clear() {
        if (existsDir(this.dir)) {
            fs.rmSync(this.dir, {recursive: true});
            fs.mkdirSync(this.dir, {recursive: true});
        }
    }

    async loadPackages(uris: string | string[]) {

        await this._plugins;
        if (!Array.isArray(uris)) uris = [uris];
        var loaded = [];
        for (let uri of uris) {
            try {
                let info = await this.unzip(uri);  // must not run async; no much use of it anyway
                this.packages_by_name[info.name] = info;
                this.packages_by_uri[uri] = info;
                loaded.push(uri);
                this.emit('message', {data: ['LibProgress', {uri, done: true}]});
            }
            catch (e) {
                console.log(`Failed to load pkg uri: ${uri} (${e})`);
                this.emit('message', {data: ['LibError', uri, '' + e]});
            }
        }
        this.emit('message', {data: ['LoadedPkg', loaded]});
    }

    async unzip(uri: string) {
        /** @todo `typeof fetch` is not a good way to detect env */
        var data = /*typeof fetch !== 'undefined' ?
            await (await fetch(uri)).arrayBuffer() :*/ fs.readFileSync(uri);
        await unzip(data, {to: {directory: this.dir}});
        /** @oops not reentrant (`coq-pkg.json` is overwritten every time) */
        return JSON.parse(
            fs.readFileSync(path.join(this.dir, 'coq-pkg.json'), 'utf-8'));
    }

    listModules(pkg: string | PackageManifest) {
        if (typeof pkg === 'string')
            pkg = this.packages_by_uri[pkg] ?? this.packages_by_name[pkg]
                ?? (() => { throw new Error(`package '${pkg}' not loaded`)})();

        return Object.keys(pkg.modules).filter(k => !k.endsWith('@cma'));
    }

    /**
     * Copy native plugin libraries (`.cmxs`; only for native mode).
     * @param binDir
     */
    appropriatePlugins(binDir: string) {
        var fromDir = path.join(binDir, 'coqlib', 'plugins');
        mkdirp.sync(this.dir);
        return this._plugins = new Promise((resolve, reject) =>
            find.eachfile(/\.cmxs$/, fromDir, (filename) => {
                try {
                    this.ln_sf(filename,
                        path.join(this.dir, path.basename(filename)));
                }
                catch (e) {
                    this.emit('message', {data: ['LibError', '<native>', '' + e]});
                }
            })
            .end(resolve));
    }

    ln_sf(target: string, source: string) {
        try { fs.unlinkSync(source); }
        catch { }
        fs.symlinkSync(target, source);
    }
}

type PackageManifest = {
    name: string
    modules: {
        [name: string]: {deps?: string[]}
    }
}

export { HeadlessCoqWorker, HeadlessCoqManager, PackageDirectory }

// Local Variables:
// js-indent-level: 4
// End:
