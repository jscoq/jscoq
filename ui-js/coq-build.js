const {fsif_native, FileStore} = require('./fs-interface'),
      neatjson = require('neatjson'),
      Vue = require('vue/dist/vue');

require('./coq-manager'); // needed for Array.equals :\



/**
 * List package directories and .cmo files for configuring the load path.
 */
class CoqProject {
    constructor(fsif=fsif_native) {
        this.fsif = fsif;
        this.path = [];  /* [[logical, physical], ...] */
        this.cmos = [];
        this.vfiles = [];

        this.json_format_opts = 
            { padding: 1, afterColon: 1, afterComma: 1, wrap: 80 };

        this.zip_file_opts = 
            { date: new Date("1/1/2000 UTC"), // dummy date (otherwise, zip changes every time it is created...)
              createFolders: false };
    }

    add(base_dir, base_name) {
        var path_element = [this._prefix(base_name), [base_dir, '.']];
        if (!this.path.some(pel => pel.equals(path_element))) {
            this.path.push(path_element);
            this.cmos.push(...this._cmoFiles(base_dir));
        }
    }
    addRecursive(base_dir, base_name) {
        if (this._isDirectory(base_dir)) {
            var prefix = this._prefix(base_name);
            this.add(base_dir, prefix);
            for (let dir of this.fsif.glob.sync('**/', {cwd: base_dir})) {
                dir = dir.replace(/[/]$/,'');
                var pkg = prefix.concat(dir.split('/').filter(x => x));
                this.add(this.fsif.path.join(base_dir, dir), pkg);
            }
        }
    }
    _vFiles(dir) {
        return this.fsif.glob.sync('*.v', {cwd: dir}).map(fn => this.fsif.path.join(dir, fn));
    }
    _cmoFiles(dir) {
        return this.fsif.glob.sync('*.cm[oa]', {cwd: dir}).map(fn => this.fsif.path.join(dir, fn));
    }
    _prefix(name) { return this._module_name(name); }

    _module_name(name) {
        return (typeof name === 'string') ? name.split('.') : name;
    }

    /**
     * Merges another project into the current one.
     * @param {CoqProject} other the other project
     */
    join(other) {
        this.path.push(...other.path);
        this.cmos.push(...other.cmos);
        this.vfiles.push(...other.vfiles);
        return this;
    }

    toLogicalName(filename) {
        var dir = this.fsif.path.dirname(filename), 
            base = this.fsif.path.basename(filename).replace(/[.]v$/, '');
        for (let [logical, [physical]] of this.path) {
            if (physical === dir) return logical.concat([base])
        }
    }

    /**
     * Finds all .v files in physical directories of the project
     * and adds them to `this.vfiles`.
     */
    collectModules() {
        for (let [_, [dir]] of this.path) {
            this.vfiles.push(...this._vFiles(dir));
        }
    }

    searchModule(prefix, module_name, exact=false) {
        prefix = this._prefix(prefix);
        module_name = this._module_name(module_name);

        let startsWith = (arr, prefix) => arr.slice(0, prefix.length).equals(prefix);
        let endsWith = (arr, suffix) => suffix.length == 0 || arr.slice(-suffix.length).equals(suffix);

        let module_matches = exact ? name => name.equals(prefix.concat(module_name))
                                   : name => startsWith(name, prefix) &&
                                             endsWith(name, module_name);

        for (let vfile of this.vfiles) {
            let logical_name = this.toLogicalName(vfile);
            if (module_matches(logical_name)) {
                return logical_name;
            }
        }
    }

    createManifest(name=undefined, props={}) {
        var manifest = Object.assign({desc: name || '', deps: [], pkgs: []}, props),
            vo_files_logical = this.vfiles.map(vf => this.toLogicalName(vf)),
            pkgs = [];

        var vo_files_of_pkg = (pkg_id) => vo_files_logical.filter(vf => 
                vf.length === pkg_id.length + 1 && vf.slice(0, pkg_id.length).equals(pkg_id))
                .map(vf => `${vf[vf.length - 1]}.vo`);

        for (let [logical, _] of this.path) {
            pkgs.push({pkg_id: logical,
                vo_files: vo_files_of_pkg(logical).map(x => [x, '']),   // TODO digest
                cma_files: []});
        }

        manifest.pkgs = pkgs;

        return manifest;
    }

    createManifestJSON(name=undefined, props={}) {
        return neatjson.neatJSON(this.createManifest(name, props), 
                                 this.json_format_opts);
    }

    writeManifest(to_file, name=undefined, props={}) {
        name = name || this._guessName(to_file);
        this.fsif.fs.writeFileSync(to_file, this.createManifestJSON(name, props));
    }

    toZip(save_as, name=undefined, props={}) {
        const JSZip = require('jszip');
              
        if (save_as) name = name || this._guessName(save_as);

        var z = new JSZip();
        z.file('coq-pkg.json', this.createManifestJSON(name, props));
        for (let fn of this.vfiles) {
            let logical_name = this.toLogicalName(fn);
            if (logical_name) {
                var lfile = this._localFile(`${fn}o`);
                if (lfile)
                    z.file(`${this.fsif.path.join(...logical_name)}.vo`, lfile,
                           this.zip_file_opts);
            }
            else
                console.warn(`skipped '${fn}' (not in path).`);
        }
        if (save_as) {
            return z.generateNodeStream({compression: 'DEFLATE'})
                .pipe(this.fsif.fs.createWriteStream(save_as))
                .on('finish', () => { console.log(`wrote '${save_as}'.`); return z; });
        }
        else
            return Promise.resolve(z);
    }

    _localFile(filename) {
        try {
            this.fsif.fs.statSync(filename);
            return this.fsif.fs.createReadStream(filename);
        }
        catch (e) {
            console.error(`skipped '${filename}' (not found).`);
        }
    }

    _guessName(filename) {
        return this.fsif.path.basename(filename).replace(/[.][^.]*$/,'');  // base sans extension
    }

    _isDirectory(p) {
        try {
            return this.fsif.fs.statSync(p).isDirectory();
        }
        catch (e) { return false; }
    }

    /**
     * Configures a project from flags in _CoqProject format, i.e. -R ..., -Q ...,
     * and list of .v files.
     * @param {string} coq_project_text content of _CoqProject definition file
     * @param {string} project_root location of _CoqProject file
     */
    static fromFileText(coq_project_text, project_root, fsif=fsif_native) {
        var proj = new CoqProject(fsif);

        for (let line of coq_project_text.split(/\n+/)) {
            var mo;
            if (mo = /\s*(-[RQ])\s+(\S+)\s+(\S+)/.exec(line)) {
                var [flag, physical, logical] = [mo[1], mo[2], mo[3]];
                physical = fsif.path.join(project_root, physical);
                if (flag === '-R')
                    proj.addRecursive(physical, logical);
                else
                    proj.add(physical, logical);
            }
            else
                proj.vfiles.push(...line.split(/\s+/).filter(w => /[.]v$/.exec(w))
                    .map(fn => fsif.path.join(project_root, fn)));
        }

        if (proj.vfiles.length === 0)
            proj.collectModules();

        return proj;
    }

    /**
     * Configures a project from a _CoqProject file.
     * @param {string} coq_project_filename file in _CoqProject format
     * @param {string?} project_root base directory for project;
     *   if omitted, the directory part of `coq_project_filename` is used.
     * @param {object} fsif file-system interface to use
     */
    static fromFile(coq_project_filename, project_root=null, fsif=fsif_native) {
        return CoqProject.fromFileText(
            fsif.fs.readFileSync(coq_project_filename, 'utf-8'),
            project_root || fsif.path.dirname(coq_project_filename),
            fsif);
    }

    /**
     * Configures a project from a directory containing a _CoqProject file.
     * @param {string} dir directory
     * @param {string?} project_root base directory for project;
     *   if omitted, `dir` is used as root as well.
     * @param {object} fsif file-system interface to use
     */
    static fromDirectory(dir, project_root=null, fsif=fsif_native) {
        return CoqProject.fromFile(
            fsif.path.join(dir, '_CoqProject'),
            project_root || dir, fsif);
    }

    static fromFileOrDirectory(coq_project_dir_or_filename, project_root=null, fsif=fsif_native) {
        var is_dir;
        try {
            is_dir = fsif.fs.statSync(coq_project_dir_or_filename).isDirectory();
        }
        catch (e) { throw new Error(`not found: '${coq_project_dir_or_filename}'`); }

        return (is_dir ? CoqProject.fromDirectory : CoqProject.fromFile)(
            coq_project_dir_or_filename, project_root, fsif);
    }
    
}


class SearchPath {
    constructor(packages=[]) {
        this.packages = packages;
    }

    toLogicalName(filename) {
        for (let pkg of this.packages) {
            let lu = pkg.toLogicalName(filename);
            if (lu) return {pkg: pkg, dirpath: lu};
        }
    }

    searchModule(prefix, module_name, exact=false) {
        for (let pkg of this.packages) {
            let lu = pkg.searchModule(prefix, module_name, exact);
            if (lu) return {pkg: pkg, dirpath: lu};
        }
    }

    prepend(pkg) {
        var idx = this.packages.indexOf(pkg);
        if (idx != 0) {
            if (idx > 0) this.packages.splice(idx, 1);
            this.packages.splice(0, 0, pkg);
        }
    }
}

class CoqDep {
    constructor(fsif=fsif_native) {
        this.fsif = fsif;
        this.search_path = new SearchPath();
        this.deps = new Map();
    }

    processVernacFile(filename) {
        var mod = this.search_path.toLogicalName(filename);
        if (mod) {
            this.processVernac(this.fsif.fs.readFileSync(filename, 'utf-8'), 
                               mod.dirpath);
        }
    }

    processVernac(v_text, logical_name) {
        var key = logical_name.join('.');

        // Strip comments
        v_text = v_text.replace(/\(\*([^*]|[*][^)])*?\*\)/g, ' ');

        // Split sentences
        for (let sentence of v_text.split(/[.](?:\s|$)/)) {
            var mo = /^\s*(?:From\s+(.*?)\s+)?Require(\s+(?:Import|Export))*\s+(.*)/
                     .exec(sentence);
            if (mo) {
                var [_, prefix, import_export, modnames] = mo;
                modnames = modnames.split(/\s+/);

                for (let modname of modnames) {
                    let lu = this.search_path.searchModule(prefix || [], modname);
                    if (lu) 
                        this.deps.set(key,
                            (this.deps.get(key) || []).concat([lu]));
                }
            }
        }
    }

    processProject(proj) {
        this.search_path.prepend(proj);

        for (let vfile of proj.vfiles) {
            this.processVernacFile(vfile);
        }

        return this;
    }

    /**
     * Basically, topological sort.
     * (TODO: allow parallel builds?)
     * @param {CoqProject} proj a project with vfiles to compile
     */
    buildPlan(proj) {
        var plan = [],
            worklist = proj.vfiles.map(fn => 
                [fn, proj.toLogicalName(fn)]).filter(x => x[1]);

        while (worklist.length > 0) {
            var progress = new Set();
            for (let [fn, logical_name] of worklist) {
                let deps = (this.deps.get(logical_name.join('.')) || [])
                    .filter(entry => entry.pkg === proj && 
                            worklist.some(x => x[1].equals(entry.dirpath)));
                if (deps.length === 0) {
                    plan.push({input: fn, dirpath: logical_name});
                    progress.add(fn);
                }
            }
            if (progress.size === 0)
                throw new Error('cyclic dependency detected');
            worklist = worklist.filter(x => !progress.has(x[0]));
        }

        return plan;
    }
}


class CoqC {

    constructor(coq, fsif=fsif_native) {
        this.fsif = fsif;
        this.coq = coq || new HeadlessCoqManager();

        this.output = {root: '/lib', vo: {}, errors: {}};

        this.onprogress = () => {};

        var dummy = {
            coqCancelled: () => { },
            coqLog:       () => { }        
        };

        this.coq.coq.observers.push(this, dummy);

        this.json_format_opts = 
            { padding: 1, afterColon: 1, afterComma: 1, wrap: 80 };
        this.zip_file_opts = 
            { createFolders: false };
    }

    spawn() {
        var c = new CoqC(this.coq.spawn(), this.fsif);
        c.output = this.output;  /* tie child's output to parent's */
        c.onprogress = this.onprogress;
        return c;
    }

    /**
     * Causes compilation to continue from a previous checkpoint, using .vo
     * files stored in a Zip archive.
     * @param {JSZip or string} zip a Zip containing previous compilation
     *   artifacts, or a filename to load the Zip from.
     */
    continueFrom(zip) {
        if (typeof zip === 'string') {
            var load = this.fsif.fs.readFileSync(zip);
            return require('jszip').loadAsync(load).then(z => this.continueFrom(z));
        }
        else {
            var upload = [], root = this.output.root;
            zip.forEach((fn, content) => {
                if (/[.]vo$/.exec(fn)) {
                    var put_fn = this.fsif.path.join(root, fn);
                    upload.push(
                        content.async('arraybuffer').then(data => {
                            this.output.vo[fn] = data;
                            this.coq.coq.put(put_fn, data);
                            this.coq.project.add(this.fsif.path.dirname(put_fn),
                                this.fsif.path.dirname(fn).split('/'));
                        })
                    );
                }
            });
            return Promise.all(upload);
        }
    }

    /**
     * Compiles a .v file, producing a .vo file and placing it in the worker's
     * pseudo-filesystem under `this.output.root`.
     * Multiple jobs are processed sequentially.
     * @param {array or object} entries a compilation job with fields 
     *   {input, dirpath}, or an array of them.
     * @param {boolean} upload when true, copies the source files to Worker
     *   space using Put commands.
     */
    batchCompile(entries, upload=false) {
        if (Array.isArray(entries)) {
            var jobs = entries.map(entry => () => this.spawn().batchCompile(entry, upload));
            return jobs.reduce(
                (promise, job) => promise.then(job),
                Promise.resolve());
        }
        else {
            var entry = entries, pkg_id = entry.dirpath.slice(0, -1),
                root = this.output.root,
                in_fn = upload ? `/static/_build/${entry.dirpath.join('/')}.v` : entry.input,
                out_fn = `${this.fsif.path.join(...entry.dirpath)}.vo`,
                out_fn_abs = this.fsif.path.join(root, out_fn);

            if (this.output.vo.hasOwnProperty(out_fn)) return Promise.resolve();

            this.onprogress({type: 'start', entry, state: this.output});
            console.log("Compiling: ", entry.input);

            this.coq.options.top_name = entry.dirpath.join('.');
            this.coq.options.compile = {input: in_fn, output: out_fn_abs};
            if (upload)
                this.coq.coq.put(in_fn, this.fsif.fs.readFileSync(entry.input));
            this.coq.start();
            // Handle success/failure status from manager
            return this.coq.when_done.promise.then(() => {
                this.coq.project.add(this.fsif.path.join(root, ...pkg_id), pkg_id);
            })
            .catch(e => {
                this.output.errors[entry.input] = [this.decorateError(e, entry)]; 
                return Promise.reject(e); 
            })
            .finally(() => {
                this.cleanup();
                this.onprogress({type: 'end', entry, state: this.output})
            });
        }
    }

    cleanup() {
        this.coq.terminate();
        let idx = this.coq.coq.observers.indexOf(this);
        if (idx > -1) this.coq.coq.observers.splice(idx, 1);
    }

    coqGot(filename, buf) {
        if (!this.coq.when_done.isFailed()) {
            var rel = this.fsif.path.relative(this.output.root, filename);
            this.output.vo[rel] = buf;
        }
    }

    toZip(save_as) {
        const JSZip = require('jszip'), path = this.fsif.path,
              name = save_as ? path.basename(save_as).replace(/[.][^.]*$/,'') : undefined;
        var z = new JSZip();
        z.file('coq-pkg.json', neatjson.neatJSON(this.createManifest(name), 
                                                 this.json_format_opts));
        for (let fn in this.output.vo) {
            z.file(fn, this.output.vo[fn], this.zip_file_opts);
        }
        if (save_as) {
            return z.generateNodeStream()
                .pipe(this.fsif.fs.createWriteStream(save_as))
                .on('finish', () => {
                    console.log(`wrote '${save_as}'.`); return z;
                });
        }
        else
            return Promise.resolve(z);
    }

    createManifest(name) {
        const path = this.fsif.path;
        var dirs = new Map(), pkgs = [];
        for (let fn in this.output.vo) {
            var dir = path.dirname(fn), base = path.basename(fn);
            if (dirs.has(dir)) dirs.get(dir).push(base);
            else dirs.set(dir, [base]);
        }
        for (let dir of dirs.keys()) {
            pkgs.push({
                pkg_id: dir.split('/'),
                vo_files: dirs.get(dir).map(x => this._voEntry(x))
             });
        }
        return {desc: name || '', deps: [], pkgs: pkgs};
    }

    _voEntry(x) {
        return [x, ''];  // TODO: digest
    }

    decorateError(err, entry) {
        err.entry = entry;
        // Convert character positions to {line, ch}
        if (err.loc) {
            var source;
            try {
                source = this.fsif.fs.readFileSync(entry.input, 'utf-8');
            }
            catch (e) { console.warn(e); return; }
            err.loc.start = CoqC.posToLineCh(source, err.loc.bp);
            err.loc.end =   CoqC.posToLineCh(source, err.loc.ep);
        }
        return err;
    }

    /**
     * Translates a character index to a {line, ch} location indicator.
     * @param {string} source_text document being referenced
     * @param {integer} pos character offset from beginning of string 
     *   (zero-based)
     * @return {object} a {line, ch} object with (zero-based) line and 
     *   character location
     */
    static posToLineCh(source_text, pos) {
        var offset = 0, line = 0, ch = pos;
        do {
            var eol = source_text.indexOf('\n', offset);
            if (eol === -1 || eol >= pos) break;
            line++; 
            ch -= (eol - offset + 1);
            offset = eol + 1;
        } while (true);

        return {line, ch};
    }
}


/**
 * Main build task entry point.
 * Orchestrates the different build stages and backs UI for displaying
 * build progress and outcome.
 */
class CoqBuild {

    constructor() {
        this.store = new FileStore();
        this.view = undefined;

        this.options = {
            upload: true
        };

        this._ongoing = new Set();
    }

    startNew() {
        if (this.view) this.view.$refs.file_list.clear();
        this.store = new FileStore();
        this._ongoing.clear();
        return this;
    }

    ofDirectory(dir, fsif=fsif_native) {
        // Read project file and store all .v files in transient folders
        // according to their logical paths
        var physical = CoqProject.fromFileOrDirectory(dir, null, fsif);

        for (let vfile of physical.vfiles) {
            var logical = physical.toLogicalName(vfile);
            if (logical) {
                this.store.create(`/${logical.join('/')}.v`,
                                  fsif.fs.readFileSync(vfile));
            }
        }

        this._openProject();
        return Promise.resolve(this);
    }

    ofZip(zip) {
        if (zip instanceof Blob)
            return JSZip.loadAsync(zip).then(z => this.ofZip(z));

        var zip_store = new FileStore(), scan = [];
        zip.forEach((fn, content) => {
            scan.push(
                content.async('arraybuffer').then(data =>
                    zip_store.create(`/${fn}`, data)));
        });
        return Promise.all(scan).then(() =>
            this.ofDirectory('/', zip_store.fsif));
    }

    prepare(coq) {
        const {HeadlessCoqManager} = require('./coq-cli');

        // Compute module dependencies with CoqDep
        if (this.project) {
            var coqdep = new CoqDep(this.store.fsif);
            coqdep.processProject(this.project);
            this.plan = coqdep.buildPlan(this.project);
        }

        // Create a worker and a compiler instance
        this.coq = coq || this.coq || new HeadlessCoqManager(
            (typeof CoqWorker !== 'undefined') ? new CoqWorker : undefined,
            this.store.fsif);
        Object.assign(this.coq.options, this.options);

        this.coqc = new CoqC(this.coq, this.store.fsif);
        this.coqc.onprogress = ev => this._onProgress(ev);

        this._ongoing.clear();
        this._updateView();

        return this.coq.coq.when_created;
    }

    async start() {
        if (this.editor_provider && this.editor_provider.dirty)
            await this.editor_provider.saveLocal();

        this.coqc.batchCompile(this.plan, this.options.upload);
    }

    restart() {
        this.coqc.output.vo = {};
        this.coqc.output.errors = {};

        return this.start();
    }

    _openProject(dir="/") {
        this.project = new CoqProject(this.store.fsif);
        this.project.addRecursive(dir, []);
        this.project.collectModules();

        this._ongoing.clear();
        this._updateView();
    }

    _onProgress(ev) {
        if (ev.type == 'start') {
            this._ongoing.add(ev.entry.input);
        }
        else if (ev.type == 'end') {
            this._ongoing.delete(ev.entry.input);
        }
        this._updateView();
        this._updateMarks();
    }

    // =======
    // UI Part
    // =======

    withUI(project_dom, report_dom=null) {
        require('./components/file-list');
        require('./components/problem-list');

        this.view = new Vue({
            el: project_dom,
            data: {
                files: []
            }
        });

        this.view.$on('action', ev => this.onAction(ev));

        if (report_dom) {
            this.report = new Vue({
                el: report_dom,
                data: {
                    errors: []
                }
            });

            this.report.$refs.problem_list.pprint = new FormatPrettyPrint();
        }

        this._updateView();
        return this;
    }

    withEditor(editor_provider) {
        this.editor_provider = editor_provider;

        // Only one editor store can exist at any given time :/
        const store = this.store;
        CmCoqProvider.file_store = {
            async getItem(filename) { return store.readFileSync(filename, 'utf-8'); },
            async setItem(filename, content) { store.file_map.set(filename, content); }
        };
    }

    onAction(ev) {
        if (this.editor_provider 
              && ev.type === 'select' && ev.kind === 'file') {
            this._openSourceFile(`/${ev.path.join('/')}`);
        }
    }

    _updateView() {
        // TODO might be better to use a Vue computed property instead
        if (this.view) {
            for (let fn of this.store.file_map.keys()) {
                var e = this.view.$refs.file_list.create(fn),
                    status = this._fileStatus(fn);
                e.tags = status ? [CoqBuild.BULLETS[status]] : [];
            }
        }

        if (this.report && this.coqc) {
            this.report.errors = Object.values(this.coqc.output.errors);
        }
    }

    _fileStatus(fn) {
        if (this._ongoing.has(fn)) return 'compiling';

        var vo_fn = `${fn.replace(/^[/]*/, '')}o`;
        if (this.coqc && this.coqc.output.vo.hasOwnProperty(vo_fn))
            return 'compiled';
        else if (this.coqc.output.errors.hasOwnProperty(fn))
            return 'error';
    }

    async _openSourceFile(filename) {
        await this.editor_provider.openLocal(filename);
        this._updateMarks();
    }

    _updateMarks() {
        if (this.editor_provider) {
            var filename = this.editor_provider.filename;

            for (let stm of this._active_marks || []) stm.mark.clear();
            this._active_marks = [];

            if (filename && this.coqc.output.errors.hasOwnProperty(filename)) {
                for (let e of this.coqc.output.errors[filename]) {
                    if (e.loc && e.loc.start && e.loc.end) {
                        var stm = {start: e.loc.start, end: e.loc.end};
                        this._active_marks.push(stm);
                        this.editor_provider.mark(stm, 'error');
                    }
                }
            }
        }
    }

}

CoqBuild.BULLETS = {
    compiling: {text: '◎', class: 'compiling'},
    compiled: {text: '✓', class: 'compiled'},
    error: {text: '✗', class: 'error'}
};



module.exports = {CoqProject, CoqDep, CoqC, CoqBuild, FileStore}



if (module && module.id == '.') {
    var opts = require('commander')
        .option('--create-package <pkg>',        'write a .coq-pkg archive (requires --project)')
        .option('--create-manifest <json>',      'write a .json package definition (requires --project)')
        .option('--project <dir>',               'use project at dir (must contain a _CoqProject file)')
        .option('--projects <dir,...>',          'use a comma-separated list of project directories')
        .option('--name <name>',                 'set package name; if unspecified, inferred from output filename')
        .option('--deps <pkg,...>',              'set package dependencies; defaults to none')
        .parse(process.argv);

    const path = require('path');

    var proj, pkg, props = {};

    if (typeof opts.name !== 'string') opts.name = undefined; // name is a function otherwise :/

    if (opts.project) {
        proj = CoqProject.fromFileOrDirectory(opts.project);
    }

    if (opts.projects) {
        var projs = opts.projects.split(',').map(fn => CoqProject.fromFileOrDirectory(fn));

        if (proj) projs.splice(0, 0, proj);

        proj = projs.reduce((proj1, proj2) => proj1.join(proj2));
    }

    if (opts.deps) {
        props.deps = opts.deps.split(/,/).map(s => s.trim());
    }

    if (opts.createPackage) {
        pkg = opts.createPackage;
        if (proj)
            proj.toZip(opts.createPackage, opts.name, props);
        else
            console.error("Create package from what? Use --project to specify source.");
    }

    if (opts.createManifest) {
        if (proj) {
            if (pkg) props.archive = path.basename(pkg);
            proj.writeManifest(opts.createManifest, opts.name, props);
        }
        else
            console.error("Create manifest of what? Use --project to specify source.");
    }
}
