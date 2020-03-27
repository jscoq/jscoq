
const {fsif_native} = require('./fs-interface'),
      {CoqWorker, Future} = require('./jscoq'),
      {CoqIdentifier} = require('./coq-manager'),
      {CoqProject, CoqDep, CoqC} = require('./coq-build'),
      {FormatPrettyPrint} = require('./format-pprint');



class HeadlessCoqWorker extends CoqWorker {
    constructor() {
        var node_require = require;  /* bypass browserify */
        super(null, node_require('../coq-js/jscoq_worker').jsCoq);
        this.worker.onmessage = this._handler = evt => {
            process.nextTick(() => this.coq_handler({data: evt}));
        };
    }

    spawn() { return new HeadlessCoqWorker(); }
}

/**
 * A manager that handles Coq events without a UI.
 */
class HeadlessCoqManager {

    constructor(worker=undefined, fsif=fsif_native) {
        this.coq = worker || new HeadlessCoqWorker();
        this.coq.observers.push(this);
        this.fsif = fsif;
        this.provider = new QueueCoqProvider();
        this.pprint = new FormatPrettyPrint();

        this.project = new CoqProject(fsif);

        this.options = {
            prelude: false,
            top_name: undefined,  /* default: set by worker (JsCoq) */
            implicit_libs: true,
            pkg_path: undefined,  /* default: automatic */
            inspect: false,
            log_debug: false
        };

        this.coq.options = this.options;

        this.doc = [];

        this.when_done = new Future();
    }

    start() {
        // Configure load path
        this.options.pkg_path = this.options.pkg_path || this.findPackageDir();

        this.project.addRecursive(`${this.options.pkg_path}/Coq`, 'Coq');

        for (let fn of this.project.cmos) {
            this.coq.register(fn);
        }

        // Initialize Coq
        let set_opts = {top_name: this.options.top_name,
                        implicit_libs: this.options.implicit_libs,
                        stm_debug: false},
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

    require(module_name) {
        this.provider.enqueue(`Require ${module_name}.`);
    }

    load(vernac_filename) {
        // Relative paths must start with './' for Load command
        if (!this.fsif.path.isAbsolute(vernac_filename) && !/^[.][/]/.exec(vernac_filename))
            vernac_filename = `./${vernac_filename}`;
        this.provider.enqueue(`Load "${vernac_filename}".`);
    }

    spawn() {
        var c = new HeadlessCoqManager(this.coq.spawn(), this.fsif);
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
            this.fsif.fs.writeFileSync(out_fn, JSON.stringify({lemmas: symbols}));
            console.log(`Wrote '${out_fn}' (${symbols.length} symbols).`);
        });
    }

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
        if (this.log_debug)
            console.log("Processed",sid);

        var last_stm = this.doc[this.doc.length - 1];
        if (last_stm && last_stm.coq_sid === sid && !last_stm.executed) {
            last_stm.executed = true;
            this.goNext(sid) || process.nextTick(() => this.eof());
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

    coqCoqExn(loc, _, msg) {
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
        for (let path_el of module.paths || []) {
            for (let dir of [this.fsif.path.join(path_el, dirname), 
                             this.fsif.path.join(path_el, '..', dirname)])
                if (this._isDirectory(dir))
                    return dir;
        }
        return this.fsif.path.join('.', dirname);
    }

    _isDirectory(path) {
        try { return this.fsif.fs.statSync(path).isDirectory(); }
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



module.exports = {HeadlessCoqManager, HeadlessCoqWorker}



if (module && module.id == '.') {
    var requires = [], require_pkgs = [],
        opts = require('commander')
        .version('0.11.0', '-v, --version')
        .option('--noinit',                                 'start without loading the Init library')
        .option('--require <path>',                         'load Coq library path and import it (Require Import path.)')
        .option('--require-pkg <json>',                     'load a package and Require all modules included in it')
        .option('-l, --load-vernac-source <f.v>',           'load Coq file f.v.')
        .option('--compile <f.v>',                          'compile Coq file f.v')
        .option('-o <f.vo>',                                'use f.vo as output file name')
        .option('--inspect <f.symb.json>',                  'inspect global symbols and serialize to file')
        .option('-e <command>',                             'run a vernacular command')
        .option('--project <dir>',                          'build project at dir (must contain a _CoqProject file)')
        .option('--continue',                               'continue a previous project compilation from where it was stopped')
        .on('option:require',     path => { requires.push(path); })
        .on('option:require-pkg', json => { require_pkgs.push(json); })
        .parse(process.argv);

    const path = require('path'),
          mkpkg = require('../coq-jslib/mkpkg');

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

    if (opts.loadVernacSource) coq.load(opts.loadVernacSource);
    if (opts.compile) { 
        coq.options.compile = {input:  opts.compile,
                               output: opts.O || `${opts.compile}o`}; 
    }

    if (opts.E) coq.provider.enqueue(...opts.E.split(/(?<=\.)\s+/));

    if (opts.inspect) {
        coq.options.inspect = {};
        if (typeof opts.inspect === 'string')
            coq.options.inspect.filename = opts.inspect;
        if (modules.length > 0)
            coq.options.inspect.modules = modules;
    }

    if (opts.project) {
        let proj = CoqProject.fromFile(path.join(opts.project, '_CoqProject')),
            out_pkg = opts.O || 'a.coq-pkg',
            build_plan = new CoqDep().processProject(proj).buildPlan(proj);

        let coqc = new CoqC(coq);

        let starting_point = opts.continue ? coqc.continueFrom(out_pkg) 
                                           : Promise.resolve();

        starting_point.then(() => 
            coqc.batchCompile(build_plan)
            .catch(()   => console.log("Aborted."))
            .finally(() => coqc.toZip(out_pkg)))
        .catch((e)      => { console.error(e); console.log("Aborted.") });
    }
    else {
        coq.start()
        coq.when_done.promise.catch(() => console.log("Aborted."));
    }
}

