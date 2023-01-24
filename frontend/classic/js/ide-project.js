//@ts-check
import './public-path.js';

import assert from 'assert';
import Vue from 'vue';

// import { JsCoq } from './index.js';  // @todo later; right now it will duplicate it :/

import { BatchWorker, CompileTask } from '../../cli/build/batch.ts';
import { CoqProject, InMemoryVolume, ZipVolume } from '../../cli/build/project.ts';
import '../css/project.css';

class ProjectPanel {

    constructor() {
        this.view = new (Vue.component('project-panel-default-layout'))();
        this.view.$mount();

        this.view.$watch('status', v => this._update(v), {deep: true});
        this.view.$on('action', ev => this.onAction(ev));
        this.view.$on('new', () => this.clear());
        this.view.$on('build', () => this.buildAction());
        this.view.$on('download', () => this.download());

        this.view.$on('menu:new', () => this.clear());
        this.view.$on('menu:open', (entry) => this.openRecent(entry));
        this.view.$on('menu:download-v', () => this.downloadSources());
        this.view.$on('menu:download-vo', () => this.downloadCompiled());

        this.view.$on('file:create', ev => this.createFile(ev));

        this.editor_provider = undefined;
        this.package_index = undefined;
        this.config = new ProjectPanelConfig();
    }

    get $el() { return this.view.$el; }

    clear() {
        this.open(new CoqProject('untitled', new LogicalVolume()));
    }

    open(project) {
        this.project = project;
        this.view.status = {};
        let fv = this.view.$refs.file_list;
        fv.populate([...project.modulesByExt('.v')].map(mod => mod.physical));
        fv.collapseAll();
        requestAnimationFrame(() => { fv.collapseAll(); fv.expandAll(1); });

        if (this.editor_provider) this._associateStore();
    }

    async openZip(zip, filename=undefined) {
        let vol = (zip instanceof Promise || zip instanceof Blob) ?
                    await ZipVolume.fromBlob(zip)
                  : new ZipVolume(zip);
        this.open(new CoqProject(filename && filename.replace(/[.]zip$/, ''), vol)
                  .fromDirectory('').copyLogical(new LogicalVolume()));
    }

    async openDirectory(entries /* string | (File | FileEntry | DirectoryEntry)[] */) {
        if (typeof entries === string) return this.openDirectoryPhys(entries);

        let vol = new LogicalVolume();
        for (let entry of entries) {
            await vol.fromWebKitEntry(entry);
        }
        let name = entries.length == 1 ? entries[0].name : undefined;
        this.open(new CoqProject(name, vol).fromDirectory('/'));
    }

    /**
     * Open a physical disk path (Node.js/Electron only).
     * @param {string} path
     */
    openDirectoryPhys(path) {
        this.config.setLastProject(path);

        var phys = new CoqProject('untitled', fsif_native).fromDirectory(path);
        this.open(LogicalVolume.project(phys));
        this.project.uri = path;
    }

    openURI(uri) {
        this.openDirectoryPhys(uri); /** @todo */
    }

    async openDialog() {
        var input = $('<input>').attr('type', 'file');
        input.on('change', () => {
            var fl = input[0].files[0];
            if (fl) this.openZip(fl, fl.name);
        });
        input[0].click();
    }

    async openUI(uri) {
        try {
            if (uri) this.openURI(uri);
            else await this.openDialog();  /** @todo this returns immediately right now */
            return true;
        }
        catch (e) {
            alert(`Cannot open '${uri || '<project>'}': ${e}`);
            return false;
        }
    }

    async openRecent(entry) {
        console.log(entry.uri, entry.lastFile);
        if (this.openUI(entry.uri)) {
            if (entry.lastFile) this.openFileUI(entry.lastFile)
        }
    }

    async restore(reopenLast = true) {
        var recent = (await this.config.restore()).recent;
        this.view.recent = recent;
        if (reopenLast && recent && recent[0]) {
            this.openRecent(recent[0]);
        }
    }

    async addFile(filename, content) {
        if (content instanceof Blob) content = await content.text();
        this.project.volume.writeFileSync(filename, content);
        this.project.searchPath.add(
            {physical: "/", logical: [], pkg: this.project.name});
    }

    openFile(filename) {
        this.config.setLastFile(this.project, filename);
        requestAnimationFrame(() =>
            this.view.$refs.file_list.select(filename));
        if (this.editor_provider)
            this.editor_provider.openLocal(filename);
        if (this.report)
            requestAnimationFrame(() => this.report._updateMarks());
    }

    openFileUI(filename) {
        try {
            if (filename) this.openFile(filename)
        }
        catch (e) {
            alert(`Cannot open '${filename}': ${e}`);
        }
    }

    withEditor(editor_provider /* CmCoqProvider */) {
        this.editor_provider = editor_provider;
        if (this.project) this._associateStore();
        if (this.report) this.report.editor = this.editor_provider;
        return this;
    }

    withCoqManager(coq) {
        this.coq = coq;
        return this.withEditor(coq.provider.snippets[0]);
    }

    async build(coqw) {
        this.view.building = true;
        this.view.stopping = false;
        this.view.status = {};

        if (this.report) this.report.clear();
        this.report = new BuildReport();
        this.report.editor = this.editor_provider;
        this.report.pprint = this.coq && this.coq.pprint;

        try {
            if (this.editor_provider && this.editor_provider.dirty)
                this.editor_provider.saveLocal();

            if (this.package_index || this.coq)
                this.project.searchPath.packageIndex = this.package_index || this.coq.packages.index;

            coqw = coqw || this._createBuildWorker();
            await coqw.when_created;

            var task = this.buildTask = this._createBuildTask(coqw);

            task.on('progress', files => this._progress(files));
            task.on('report', (e, mod) => this.report.add(e, mod));
            return this.out = await task.run();
        }
        finally {
            this.buildTask = null;
            this.view.building = false;
            this.view.stopping = false;
            this.view.compiled = !!this.out;
            coqw.end();
        }
    }

    deploy() {
        if (this.out && this.coq) {
            for (let vo of this.out.modulesByExt('.vo')) {
                console.log(`> ${vo.physical}`);
                this.coq.coq.put(vo.physical, vo.volume.fs.readFileSync(vo.physical));
            }
        }
    }

    async buildDeploy(coq) {
        await this.build(coq);
        this.deploy();
    }

    buildAction() {
        if (this.buildTask) {
            this.view.stopping = true;
            this.buildTask.stop();
        }
        else {
            this.buildDeploy()
            .catch(e => { if (e[0] != 'CoqExn') throw e; });
        }
    }

    getLoadPath() {
        return this.out ?
            this.out.searchPath.path.map(pel => [pel.logical, ['/lib']]) : [];
    }

    _createBuildWorker() {
        var coqw = (this.coq && this.coq.options.subproc)
              ? new CoqSubprocessAdapter()
              : new CoqWorker();
        coqw.options.warn = false;
        coqw.observers.push(this);
        return coqw;
    }

    _createBuildTask(coqw) {
        var pkgr = this.coq && this.coq.packages,
            buildDir = (this.coq && this.coq.options.subproc) ? '/tmp/build' : '/lib';

        return new CompileTask({
                'js': () => new JsCoqBatchWorker(coqw, pkgr),
                'wa': () => new WacoqBatchWorker(coqw, pkgr)
            }[JsCoq.backend](), this.project, {buildDir});
    }

    feedMessage(sid, lvl, loc, msg) {
        /** @todo */
        console.log('feedback', sid, lvl, loc, msg);
    }

    async downloadCompiled() {
        var fn = `${this.out.name || 'project'}.coq-pkg`,
        {pkg} = await this.out.toPackage(fn, ['.v', '.vo', '.cma']);
        await this._download(pkg.zip, fn);
    }

    async downloadSources() {
        var fn = `${this.project.name || 'project'}.zip`,
            zip = await this.project.toZip(undefined, ['.v', '.vo', '.cma']);
        await this._download(zip, fn);
    }

    async _download(zip, fn) {
        var blob = new Blob([zip.zipSync()], {type: 'application/octet-stream'}),
            a = $('<a>').attr({'href': URL.createObjectURL(blob),
                               'download': fn});
        a[0].click();
    }

    _update(status) {
        var flist = this.view.$refs.file_list;
        for (let fe of flist.iter()) {
            var filename = `/${fe.path.join('/')}`,
                fstatus = status[filename];
            fe.entry.tags = fstatus ? [ProjectPanel.BULLETS[fstatus]] : [];
        }
    }

    _progress(files) {
        for (let {filename, status} of files)
            Vue.set(this.view.status, filename, status);
    }

    _associateStore() {
        // Only one editor store can exist at any given time :/
        const volume = this.project.volume;
        CmCoqProvider.file_store = {
            async getItem(filename) { return volume.readFileSync(filename, 'utf-8'); },
            async setItem(filename, content) { volume.writeFileSync(filename, content); },
            async keys() { return []; /** @todo */ }
        };
    }

    onAction(ev) {
        switch (ev.type) {
        case 'select':
            if (ev.kind === 'file') {
                this.openFile(`/${ev.path.join('/')}`);
            };
            break;
        case 'move':
            var target = [...ev.to, ...ev.from.slice(-1)];
            this.project.volume.renameSync(
                `/${ev.from.join('/')}`, `/${target.join('/')}`);
            break;
        case 'rename':
            var src = [...ev.path, ev.from], target = [...ev.path, ev.to];
            this.project.volume.renameSync(
                `/${src.join('/')}`, `/${target.join('/')}`);
            break;
        case 'create':
            if (ev.kind === 'file')
                return this.addFile(`/${ev.path.join('/')}`, '')
            break;
        }
    }

    static attach(coq, container, name) {
        var panel = new ProjectPanel().withCoqManager(coq);
        container.append(panel.$el);

        if (name == 'sample')
            panel.open(ProjectPanel.sample());

        panel.restore(!name);
        return panel;
    }

    /**
     * This is here temporarily for quick testing.
     */
    static sample() {
        // sample project
        var vol = new LogicalVolume();
        vol.fs.writeFileSync('/simple/_CoqProject', '-R . simple\n\nOne.v Two.v Three.v\n');
        vol.fs.writeFileSync('/simple/One.v', 'Check 1.\nFrom simple Require Import Two.');
        vol.fs.writeFileSync('/simple/Two.v', 'From Coq Require Import List.\n\nDefinition two_of π := π + π.\n');
        vol.fs.writeFileSync('/simple/Three.v', 'From simple Require Import One Two.');

        return new CoqProject('sample', vol).fromDirectory('/');
    }

    static localDir(dir) {
        return new CoqProject('untitled', fsif_native).fromDirectory(dir);
    }
}


ProjectPanel.BULLETS = {
    compiling: {text: '◎', class: 'compiling'},
    compiled: {text: '✓', class: 'compiled'},
    error: {text: '✗', class: 'error'}
};


class ProjectPanelConfig {

    constructor() {
        this._store = localforage.createInstance({'name': 'ProjectPanel.config'});
        this.restore();
    }

    store() {
        if (this.recent)
            this._store.setItem('recent', JSON.stringify(this.recent));
    }

    async restore() {
        var recent = await this._store.getItem('recent');
        this.recent = recent && JSON.parse(recent);
        return this;
    }

    setLastProject(uri) {
        this.recent = [{uri}];  // TODO
        this.store();
    }

    setLastFile(project, filename) {
        var puri = project && project.uri;
        if (puri) {
            var r = (this.recent || []).find(p => p.uri === puri);
            if (r) r.lastFile = filename;
            this.store();
        }
    }
}


Vue.component('project-panel-default-layout', require('./components/project-panel-default-layout.vue').default);
Vue.component('project-build-status', require('./components/project-build-status.vue').default);
Vue.component('project-context-menu', require('./components/project-context-menu.vue').default);
Vue.component('project-file-context-menu', require('./components/project-file-context-menu.vue').default);


class LogicalVolume extends InMemoryVolume {

    async fromWebKitEntry(entry /* DirectoryEntry | FileEntry */) {
        await new Promise(resolve => {
            if (entry.isFile) {
                entry.file(async b => {
                    let content = new Uint8Array(await b.arrayBuffer());
                    this.writeFileSync(entry.fullPath, content);
                    resolve();
                });
            }
            else if (entry.isDirectory) {
                let readdir = entry.createReader();
                readdir.readEntries(async entries => {
                    for (let e of entries) await this.fromWebKitEntry(e);
                    resolve();
                });
            }
        });
        return this;
    }

    static project(proj) {
        return proj.copyLogical(new LogicalVolume());
    }
}


class JsCoqBatchWorker extends BatchWorker {
    constructor(coqw, pkgr) {
        super(coqw.worker);
        this.coqw = coqw;     this.pkgr = pkgr;
    }

    async loadPackages(pkgs) {
        var loadpath = [];
        if (pkgs.size > 0) {
            if (!this.pkgr) throw new Error('no PackageManager to load dependencies');
            await this.coqw.when_created;
            for (let pkg of pkgs) {
                var pkgi = this.pkgr.getPackage(pkg);
                await pkgi.archive.unpack(this.coqw);
                loadpath.push(...this.loadpathFor(pkgi));
                // Loading of non-archive pkgs currently not implemented
            }
        }
        this.loadpath = loadpath;
    }

    loadpathFor(pkg) {
        return pkg.info.pkgs.map(pkg => [pkg.pkg_id, ['/lib']]);
    }

    docOpts(mod, outfn) {
        this.loadpath.push([mod.logical.slice(0, -1), ['/lib']]);
        return super.docOpts(mod, outfn);
    }

    async install(mod, volume, root, outfn, compiledfn, content) {
        if (volume !== this.volume)
            volume.fs.writeFileSync(outfn, content);
    }
}

import { fsif_native } from '../../cli/build/fsif.ts';

class WacoqBatchWorker extends BatchWorker {
    constructor(coqw, pkgr) {
        super(coqw.worker);
        this.coqw = coqw;     this.pkgr = pkgr;
        if (this.coqw instanceof CoqSubprocessAdapter)
            this.volume = fsif_native;
    }

    async loadPackages(pkgs) {
        await this.coqw.when_created;
        await this.do(
            ['LoadPkg', this.getURIs([...pkgs])],
            msg => msg[0] == 'LoadedPkg'
        );
        this.loadpath = [this.coqw.worker.packages ? this.coqw.worker.packages.dir : '/lib'];
    }

    getURIs(pkgs) {
        return pkgs.map(pkg => {
            var p = this.pkgr.getPackage(pkg);  /**/ assert(p); /**/
            return p.getDownloadURL().href;
        });
    }

    docOpts(mod, outfn) {
        return { top_name: outfn, mode: ['Vo'],
                 lib_init: ["Coq.Init.Prelude"], lib_path: this.loadpath };
    }

    async install(mod, volume, root, outfn, compiledfn, content) {
        if (volume !== this.volume) {
            /* wacoq worker does not return file content */
            [[, , content]] = await this.do(
                ['Get', compiledfn],   msg => msg[0] == 'Got');
            volume.fs.writeFileSync(outfn, content);
        }
    }
}

class BuildReport {

    constructor() {
        this.errors = new Map();
        this.editor = undefined;
        this.pprint = undefined;
    }

    add(e, mod) {
        switch (e[0]) {
        case 'CoqExn':
            var err = this.decorateError(e[1], mod),
                item = coq.layout.log(err.msg, 'Error');   // oops
            this.pprint.adjustBreaks(item);
            if (mod) {
                this.errors.set(mod.physical,
                    (this.errors.get(mod.physical) || []).concat([err]));
                this._updateMarks();
            }
            break;
        }
    }

    clear() {
        this.errors = new Map();
        this._updateMarks();
    }

    decorateError(exn, mod) {

        let msg = exn.pp;
        let loc = exn.loc;

        let err = {loc: {filename: mod.physical.replace(/^[/]/, '')}};

        // Convert character positions to {line, ch}
        if (loc) {
            try {
                var source = mod.volume.fs.readFileSync(mod.physical);
                err.loc.start = BuildReport.posToLineCh(source, loc.bp);
                err.loc.end =   BuildReport.posToLineCh(source, loc.ep);
            }
            catch (e) { console.warn('cannot get code location for', loc, e); }
        }
        var at =
            `${err.loc.filename}:${err.loc.start ? err.loc.start.line + 1 : '?'}`
        err.msg = $('<p>').text(`at ${at}:`).addClass('error-location')
                  .add(this.pprint.pp2DOM(msg));  // oops
        return err;
    }

    /**
     * Translates a character index to a {line, ch} location indicator.
     * @param {Uint8Array} source_bytes document being referenced
     * @param {integer} pos character offset from beginning of string
     *   (zero-based)
     * @return {object} a {line, ch} object with (zero-based) line and
     *   character location
     */
    static posToLineCh(source_bytes, pos) {
        var offset = 0, line = 0, ch = pos, EOL = "\n".charCodeAt(0);
        do {
            var eol = source_bytes.indexOf(EOL, offset);
            if (eol === -1 || eol >= pos) break;
            line++;
            ch -= (eol - offset + 1);
            offset = eol + 1;
        } while (true);

        // Convert to character offset in UTF-8 string
        ch = new TextDecoder().decode(source_bytes.slice(offset, offset + ch))
             .length;

        return {line, ch};
    }

    _updateMarks() {
        if (this.editor) {
            var filename = this.editor.filename;

            for (let stm of this._active_marks || []) stm.mark.clear();
            this._active_marks = [];

            if (filename && this.errors.has(filename)) {
                for (let e of this.errors.get(filename)) {
                    if (e.loc && e.loc.start && e.loc.end) {
                        var stm = {start: e.loc.start, end: e.loc.end};
                        this._active_marks.push(stm);
                        this.editor.mark(stm, 'error');
                    }
                }
            }
        }
    }
}

export { ProjectPanel, CoqProject }
