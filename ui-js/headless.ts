import fs from 'fs';
import path from 'path';
import { EventEmitter } from 'events';
import mkdirp from 'mkdirp';
import unzip from 'fflate-unzip';
import * as find from 'find';
import glob from 'glob';

import { Future } from './future.js';
import { CoqWorker } from './jscoq-worker-interface';
import { CoqIdentifier } from './contextual-info';
import { FormatPrettyPrint } from './format-pprint';
import { arreq_deep } from '../ui-js/etc';

import { FSInterface, fsif_native } from '../coq-jslib/build/fsif';
import { CoqProject } from '../coq-jslib/build/project';


class HeadlessCoqWorker extends CoqWorker {
    when_created: Promise<any>
    worker: any
    observers: any[]
    _handler: any
    coq_handler: any
    options: any

    constructor() {
        var backend = 'js', is_npm = 'false';
        super(null, HeadlessCoqWorker.instance(), backend, is_npm);
        this.when_created.then(() => {
            this.worker.onmessage = this._handler = evt => {
                process.nextTick(() => this.coq_handler({data: evt}));
            };
        });
    }

    spawn() { return new HeadlessCoqWorker(); }

    static instance() {
        global.FormData = undefined; /* prevent a silly warning about experimental fetch API */
        var jscoq = require('../coq-js/jscoq_worker.bc.cjs').jsCoq;
        /** @oops monkey-patch to make it look like a Worker instance */
        jscoq.addEventListener = (_: "message", handler: () => void) =>
            jscoq.onmessage = handler;
        return jscoq;
    }
}

/**
 * A manager that handles Coq events without a UI.
 */
class HeadlessCoqManager {
    coq: any
    volume: FSInterface
    provider: any
    pprint: FormatPrettyPrint
    packages: PackageDirectory
    project: CoqProject
    options: any

    doc: any[]
    when_done: Future

    constructor(worker=undefined, volume=fsif_native) {
        this.coq = worker || new HeadlessCoqWorker();
        this.coq.observers.push(this);
        this.volume = volume;
        this.provider = new QueueCoqProvider();
        this.pprint = new FormatPrettyPrint();
        this.packages = new PackageDirectory('/tmp/jscoq/lib');

        this.project = new CoqProject(undefined, volume);

        this.options = {
            prelude: false,
            top_name: undefined,  /* default: set by worker (JsCoq) */
            implicit_libs: true,
            all_pkgs: ['init', 'coq-base', 'coq-collections', 'coq-arith', 'coq-reals', 'ltac2'],
            pkg_path: undefined,  /* default: automatic */
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
        // Configure load path
        this.options.pkg_path = this.options.pkg_path || this.findPackageDir();
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
                if (fs.existsSync(fp)) return fp;
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
            this.when_done.resolve();
    }

    require(module_name: string, import_=false) {
        this.provider.enqueue(`Require ${import_ ? "Import " : ""}${module_name}.`);
    }

    load(vernac_filename: string) {
        // Relative paths must start with './' for Load command
        if (!this.volume.path.isAbsolute(vernac_filename) && !/^[.][/]/.exec(vernac_filename))
            vernac_filename = `./${vernac_filename}`;
        this.provider.enqueue(`Load "${vernac_filename}".`);
    }

    spawn() {
        var c = new HeadlessCoqManager(this.coq.spawn(), this.volume);
        c.provider = this.provider.clone();
        c.project = this.project;
        Object.assign(c.options, this.options);
        return c;
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
        var out_fn = inspect.filename || 'inspect.symb',
            query_filter = inspect.modules ?
                (id => inspect.modules.some(m => this._identifierWithin(id, m)))
              : (id => true);
        this.coq.inspectPromise(0, ["All"]).then(results => {
            var symbols = results.map(fp => CoqIdentifier.ofQualifiedName(fp))
                            .filter(query_filter);
            this.volume.fs.writeFileSync(out_fn, JSON.stringify({lemmas: symbols}));
            console.log(`Wrote '${out_fn}' (${symbols.length} symbols).`);
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
            this.when_done.resolve();
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
        var searchPath = ['.', '..', '../..', '../../..']
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

    constructor(dir: string) {
        super();
        this.dir = dir;
        this.packages_by_name = {};
        this.packages_by_uri = {};
    }

    async loadPackages(uris: string | string[]) {
        await this._plugins;
        if (!Array.isArray(uris)) uris = [uris];
        var loaded = [];
        for (let uri of uris) {
            try {
                let info = await this.unzip(uri);   // must not run async; no much use of it anyway
                this.packages_by_name[info.name] = info;
                this.packages_by_uri[uri] = info;
                loaded.push(uri);
                this.emit('message', {data: ['LibProgress', {uri, done: true}]});
            }
            catch (e) {
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

        return [].concat(...pkg.pkgs.map(({pkg_id, vo_files}) =>
            vo_files.map(([fn]) =>
                [...pkg_id, fn.replace(/[.].*/, '')].join('.'))));
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
    pkgs: {
        pkg_id: string[]
        vo_files: [string, null][]
    }[]
}

export { HeadlessCoqWorker, HeadlessCoqManager, PackageDirectory }
