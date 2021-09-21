import fs from 'fs';
import path from 'path';
import { EventEmitter } from 'events';
import mkdirp from 'mkdirp';
import unzip from 'fflate-unzip';
import * as find from 'find';
import glob from 'glob';


import { CoqWorker, Future } from './jscoq';
import { CoqIdentifier } from './coq-manager';
import { FormatPrettyPrint } from './format-pprint';

import { FSInterface, fsif_native } from '../coq-jslib/build/fsif';
import { CoqProject } from '../coq-jslib/build/project';


(<any>global).JsCoq = {backend: 'js'};  /** @oops this is usually defined in `jscoq-loader.js` */


class HeadlessCoqWorker extends CoqWorker {
    when_created: Promise<any>
    worker: any
    observers: any[]
    _handler: any
    coq_handler: any
    options: any

    constructor() {
        super(null, HeadlessCoqWorker.instance());
        this.when_created.then(() => {
            this.worker.onmessage = this._handler = evt => {
                process.nextTick(() => this.coq_handler({data: evt}));
            };
        });
    }

    spawn() { return new HeadlessCoqWorker(); }

    static instance() {
        var jscoq = require('../coq-js/jscoq_worker.bc.js').jsCoq;
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
            all_pkgs: ['init', 'coq-base', 'coq-collections', 'coq-arith', 'coq-reals'],
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
            `${this.options.pkg_path}/${pkg}.coq-pkg`));

        this.project.searchPath.addRecursive(
            {physical: `${this.packages.dir}/Coq`, logical: 'Coq'});
        
        for (let mod of this.project.modulesByExt('.cma')) {
            this.coq.register(mod.physical);
        }

        // Initialize Coq
        let init_opts = {top_name: this.options.top_name,
                         implicit_libs: this.options.implicit_libs},
            lib_init = this.options.prelude ? ["Coq.Init.Prelude"] : [];

        this.coq.init(init_opts, {lib_init, lib_path: this.getLoadPath()});
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
              : (id =>true);
        this.coq.inspectPromise(0, ["All"]).then(results => {
            var symbols = results.map(fp => CoqIdentifier.ofFullPath(fp))
                            .filter(query_filter);
            this.volume.fs.writeFileSync(out_fn, JSON.stringify({lemmas: symbols}));
            console.log(`Wrote '${out_fn}' (${symbols.length} symbols).`);
        });
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

    coqCoqExn(exn) {

        let msg = exn.pp;
        let loc = exn.loc;

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
            for (let dirpat of ['..', '../_build/jscoq+*']) {
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
        return id.prefix.slice(0, prefix.length).equals(prefix);
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
    _plugins: Promise<void>

    constructor(dir: string) {
        super();
        this.dir = dir;
    }

    async loadPackages(uris: string | string[]) {
        await this._plugins;
        if (!Array.isArray(uris)) uris = [uris];
        var loaded = [];
        for (let uri of uris) {
            try {
                await this.unzip(uri);   // not much use running async
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
        var data = typeof fetch !== 'undefined' ? 
            await (await fetch(uri)).arrayBuffer() : fs.readFileSync(uri);
        return unzip(data, {to: {directory: this.dir}});
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


export { HeadlessCoqWorker, HeadlessCoqManager, PackageDirectory }
