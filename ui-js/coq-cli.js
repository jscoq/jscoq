const fs = require('fs'),
      find = require('find'),
      path = require('path'),
      jscoq = require('../coq-js/jscoq'),
      jscoq_worker = require('../coq-js/jscoq_worker'),
      coq_manager = require('./coq-manager'),
      format_pprint = require('./format-pprint'),
      mkpkg = require('../coq-tools/mkpkg');



class HeadlessCoqWorker extends jscoq.CoqWorker {
    constructor() {
        super(null, jscoq_worker.jsCoq);
        this.worker.onmessage = evt => {
            process.nextTick(() => this.coq_handler({data: evt}));
        };
    }
}

/**
 * List package directories and .cmo files for configuring the load path.
 */
class CoqProject {
    constructor() {
        this.path = [];
        this.cmos = [];
    }
    add(base_dir, base_name) {
        this.path.push([this._prefix(base_name), [base_dir, '.']]);
        this.cmos.push(...this._cmoFiles(base_dir));
    }
    addRecursive(base_dir, base_name) {
        var prefix = this._prefix(base_name);
        for (let dir of find.dirSync(base_dir)) {
            var pkg = prefix.concat(path.relative(base_dir, dir).split('/'));
            this.add(dir, pkg);
        }
    }
    _cmoFiles(dir) {
        return fs.readdirSync(dir).map(fn => /[.]cmo$/.exec(fn) && path.join(dir, fn))
            .filter(x => x);
    }
    _prefix(name) {
        return (typeof name === 'string') ? name.split('.') : name;
    }
}

/**
 * A manager that handles Coq events without a UI.
 */
class HeadlessCoqManager {

    constructor() {
        this.coq = new HeadlessCoqWorker();
        this.coq.observers.push(this);
        this.provider = new QueueCoqProvider();
        this.pprint = new format_pprint.FormatPrettyPrint();

        this.options = {
            prelude: false,
            implicit_libs: true,
            pkg_path: undefined,  /* default: automatic */
            inspect: false
        };

        this.doc = [];
    }

    start() {
        // Configure load path
        this.options.pkg_path = this.options.pkg_path || this.findPackageDir();

        this.project = new CoqProject();

        this.project.addRecursive(`${this.options.pkg_path}/Coq`, 'Coq');

        for (let fn of this.project.cmos) {
            this.coq.register(fn);
        }

        // Initialize Coq
        let set_opts = {implicit_libs: this.options.implicit_libs, stm_debug: false},
            init_libs = this.options.prelude ? [["Coq", "Init", "Prelude"]] : [],
            load_path = this.project.path;

        this.coq.init(set_opts, init_libs, load_path);
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

    finished() {
        console.log("Finished.");
        var inspect = this.options.inspect;
        if (inspect) this.performInspect(inspect);
    }

    performInspect(inspect) {
        var out_fn = inspect.filename || 'inspect.symb',
            query_filter = inspect.modules ? 
                (id => inspect.modules.some(m => this._identifierWithin(id, m)))
              : (id =>true);
        this.coq.inspectPromise(0, ["All"]).then(results => {
            var symbols = results.map(kn => coq_manager.CoqIdentifier.ofKerName(kn))
                            .filter(query_filter);
            fs.writeFileSync(out_fn, JSON.stringify({lemmas: symbols}));
            console.log(`Wrote '${out_fn}' (${symbols.length} symbols).`);
        });
    }

    coqReady() {
        console.log("Coq worker ready.")
        this.goNext();
    }

    coqLog([lvl], msg) { 
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
        var last_stm = this.doc[this.doc.length - 1];
        if (last_stm && last_stm.coq_sid === sid && !last_stm.executed) {
            last_stm.executed = true;
            if (!this.goNext(sid)) this.finished();
        }
    }

    coqCoqExn(loc, _, msg) {
        console.error(`[Exception] ${this.pprint.pp2Text(msg)}`);
    }

    feedFileLoaded() { }
    feedFileDependency() { }

    feedProcessingIn() { }

    feedMessage(sid, [lvl], loc, msg) { 
        console.log('-'.repeat(60));
        console.log(`[${lvl}] ${this.pprint.pp2Text(msg).replace('\n', '\n         ')}`); 
        console.log('-'.repeat(60));
    }

    findPackageDir(dirname = 'coq-pkgs') {
        for (let path_el of module.paths) {
            for (let dir of [path.join(path_el, dirname), 
                             path.join(path_el, '..', dirname)])
                if (this._isDirectory(dir))
                    return dir;
        }
        return path.join('.', dirname);
    }

    _isDirectory(path) {
        try { return fs.lstatSync(path).isDirectory(); }
        catch { return false; }
    }

    _identifierWithin(id, modpath) {
        var prefix = (typeof modpath === 'string') ? modpath.split('.') : modpath;
        return id.prefix.slice(0, prefix.length).equals(prefix);
    }

}

/**
 * A provider stub that just holds a list of sentences to execute.
 */
class QueueCoqProvider {

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

}



if (module && module.id == '.') {
    var requires = [], require_pkgs = [],
        opts = require('commander')
        .option('--noinit', 'start without loading the Init library')
        .option('--require <path>', 'load Coq library path and import it (Require Import path.)')
        .option('--require-pkg <json>', 'load a package and Require all modules included in it')
        .option('--inspect [filename]', 'Inspect global symbols and serialize to file')
        .option('-e [command]', 'Run a vernacular command')
        .on('option:require',     path => { requires.push(path); })
        .on('option:require-pkg', json => { require_pkgs.push(json); })
        .parse(process.argv);

    var coq = new HeadlessCoqManager();

    var modules = requires.slice();

    for (let modul of requires)
        coq.provider.enqueue(`Require ${modul}.`);

    for (let json_fn of require_pkgs) {
        var bundle = mkpkg.PackageDefinition.fromFile(json_fn);

        for (let modul of bundle.listModules()) {
            coq.provider.enqueue(`Require ${modul}.`);
            modules.push(modul);
        }
    }

    if (!opts.noinit) coq.options.prelude = true;

    if (opts.E) coq.provider.enqueue(...opts.E.split(/(?<=\.)\s+/));

    if (opts.inspect) {
        coq.options.inspect = {};
        if (typeof opts.inspect === 'string')
            coq.options.inspect.filename = opts.inspect;
        if (modules.length > 0)
            coq.options.inspect.modules = modules;
    }

    coq.start();
}

