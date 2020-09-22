// Build with
//  parcel watch ui-js/ide-project.js -d _build/jscoq+64bit/ui-js -o ide-project.browser.js --global ideProject

import assert from 'assert';
import Vue from 'vue/dist/vue';
import { VueContext } from 'vue-context';
import 'vue-context/src/sass/vue-context.scss';

import { BatchWorker, CompileTask } from '../coq-jslib/build/batch';
import { CoqProject, InMemoryVolume, ZipVolume } from '../coq-jslib/build/project';
import '../ui-css/project.css';



class ProjectPanel {

    constructor() {
        require('./components/file-list');

        this.view = new (Vue.component('project-panel-default-layout'))();
        this.view.$mount();
        
        this.view.$watch('status', v => this._update(v), {deep: true});
        this.view.$on('action', ev => this.onAction(ev));
        this.view.$on('new', () => this.clear());
        this.view.$on('build', () => this.buildAction());
        this.view.$on('download', () => this.download());

        this.view.$on('menu:new', () => this.clear());
        this.view.$on('menu:open', () => this.openDialog());
        this.view.$on('menu:download-v', () => this.downloadSources());
        this.view.$on('menu:download-vo', () => this.downloadCompiled());

        this.view.$on('file:create', ev => this.createFile(ev));

        this.editor_provider = undefined;
        this.package_index = undefined;
    }
   
    get $el() { return this.view.$el; }

    clear() {
        this.open(new CoqProject('untitled', new LogicalVolume()));
    }

    open(project) {
        this.project = project;
        this.view.status = {};
        this.view.$refs.file_list.populate(
            [...project.modulesByExt('.v')].map(mod => mod.physical));

        this.report = new BuildReport(this.project);
        this.report.editor = this.editor_provider;

        if (this.editor_provider) this._associateStore();
    }

    async openZip(zip, filename=undefined) {
        let vol = (zip instanceof Promise || zip instanceof Blob) ?
                    await ZipVolume.fromBlob(zip)
                  : new ZipVolume(zip);
        this.open(new CoqProject(filename && filename.replace(/[.]zip$/, ''), vol)
                  .fromDirectory('').copyLogical(new LogicalVolume()));
    }

    async openDirectory(entries /* (File | FileEntry | DirectoryEntry)[] */) {
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
        var phys = new CoqProject('untitled', fsif_native).fromDirectory(path);
        this.open(LogicalVolume.project(phys));
    }

    async openDialog() {
        var input = $('<input>').attr('type', 'file');
        input.change(() => {
            var fl = input[0].files[0];
            if (fl) this.openZip(fl, fl.name);
        });
        input[0].click();
    }

    async addFile(filename, content) {
        if (content instanceof Blob) content = await content.text();
        this.project.volume.writeFileSync(filename, content);
        this.project.searchPath.add(
            {physical: "/", logical: [], pkg: this.project.name});
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
        this.report.clear();

        var pkgr = this.coq && this.coq.packages;

        try {
            if (this.editor_provider && this.editor_provider.dirty)
                this.editor_provider.saveLocal();

            if (this.package_index || this.coq)
                this.project.searchPath.packageIndex = this.package_index || this.coq.packages.index;

            coqw = coqw || this._createBuildWorker();
            await coqw.when_created;

            var task = new CompileTask(new WacoqBatchWorker(coqw, pkgr),
                                       this.project);
            this.buildTask = task;
            task.on('progress', files => this._progress(files));
            task.on('report', e => this.report.add(e));
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
        var coqw =  (this.coq && this.coq.options.subproc)
              ? new CoqSubprocessAdapter()
              : new CoqWorker();
        coqw.options.warn = false;
        coqw.observers.push(this);
        return coqw;
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
        var blob = await zip.generateAsync({type: 'blob'}),
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
            if (this.editor_provider && ev.kind === 'file') {
                this.editor_provider.openLocal(`/${ev.path.join('/')}`);
                if (this.report)
                    requestAnimationFrame(() => this.report._updateMarks());
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
        else
            panel.clear();
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


Vue.component('project-panel-default-layout', {
    data: () => ({
        files: [], status: {}, building: false, compiled: false,
        stopping: false
    }),
    template: `
    <div class="project-panel vertical-pane">
        <div class="toolbar">
            <project-context-menu ref="menu"
                @action="$emit('menu:'+$event.type, $event)"/>
            <button @click="$emit('build')" :disabled="stopping">
                {{building ? 'stop' : 'build'}}</button>
            <project-build-status :building="building"/>
        </div>
        <file-list ref="file_list" :files="files" @action="fileAction"/>
        <project-file-context-menu ref="fileMenu"
            @action="fileMenuAction"/>
    </div>`,
    methods: {
        fileAction(action) {
            switch (action.type) {
            case 'menu':
                action.$event.preventDefault();
                this.$refs.fileMenu.open(action.$event, action);
                break;
            }
            this.$emit('action', action);
        },
        fileMenuAction(action) {
            const at = () => this._folderOf(action.for);
            switch (action.type) {
            case 'new-file':   this.create(at(), 'new-file#.v', 'file');    break;
            case 'new-folder': this.create(at(), 'new-folder#', 'folder');  break;
            case 'rename':     this.renameStart(action.for.path);           break;
            }
        },
        create(at, name, kind) {
            var newPath = this.$refs.file_list.freshName(at, name);
            this.$refs.file_list.create(newPath, kind);
            setTimeout(() => {
                this.$refs.file_list.renameStart(newPath);
            });
            this.$emit('action', {type: 'create', path: newPath, kind});
        },
        renameStart(path) {
            this.$refs.file_list.renameStart(path);
        },
        _folderOf(action) {
            return action.kind === 'folder' ? 
                       action.path : action.path.slice(0, -1);
        }
    }
});

Vue.component('project-build-status', {
    props: ['building'],
    data: () => ({anim: ''}),
    template: `<span class="build-status">{{anim}}</span>`,
    mounted() {
        this.$watch('building', flag => 
            flag ? this.setStatusAnimation() : this.clearStatusAnimation());
    },
    methods: {
        setStatusAnimation() {
            const l = [0,0,1,2,3].map(i => '∙'.repeat(i));
            var i = 2;
            this.anim = l[i];
            this._animInterval = setInterval(() => 
                this.anim = l[++i % l.length], 250);
        },
        clearStatusAnimation() {
            if (this._animInterval) clearInterval(this._animInterval);
            delete this._animInterval;
            this.anim = '';
        }
    }
});

Vue.component('project-context-menu', {
    data: () => ({isOpen: false}),
    template: `
    <span class="project-context-menu" :class="{open: isOpen}">
        <button @click.stop.prevent="open"><hamburger-svg/></button>
        <vue-context ref="m" @open="isOpen = true" @close="isOpen = false">
            <li><a name="new" @click="action" :disabled="$root.building">New Project</a></li>
            <li><a name="open" @click="action" :disabled="$root.building">Open Project...</a></li>
            <li><a name="download-v" @click="action">Download sources</a></li>
            <li><a name="download-vo" @click="action" :disabled="$root.building || !$root.compiled">Download compiled</a></li>
        </vue-context>
    </span>`,
    components: {VueContext},
    methods: {
        open() {
            if (this.$refs.m.show) this.$refs.m.close();
            else {
                vueContextCleanup();
                this.$refs.m.open({clientX: this.$parent.$el.clientWidth, clientY: 0}); 
            }
        },
        action(ev) {
            if (!$(ev.currentTarget).is('[disabled]'))
                this.$emit('action', {type: ev.currentTarget.name});
        }
    }
});

Vue.component('hamburger-svg', {
    template: `
    <svg viewBox="0 0 80 80">
        <rect y="5" width="80" height="12"></rect>
        <rect y="34" width="80" height="12"></rect>
        <rect y="63" width="80" height="12"></rect>
    </svg>`
});

Vue.component('project-file-context-menu', {
    template: `
    <vue-context ref="m">
        <li><a name="new-file" @click="action">New file</a></li>
        <li><a name="new-folder" @click="action">New foler</a></li>
        <li><a name="rename" @click="action">Rename</a></li>
    </vue-context>`,
    components: {VueContext},
    methods: {
        open(ev, action) {
            vueContextCleanup();
            this._for = action;
            this.$refs.m.open(ev); 
        },
        action(ev) {
            if (!$(ev.currentTarget).is('[disabled]'))
                this.$emit('action', {type: ev.currentTarget.name, for: this._for});
        }
    }
});

function vueContextCleanup() {
    if ($('.v-context').is(':visible')) $(document.body).click();
}


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


import { fsif_native } from '../coq-jslib/build/fsif';


class WacoqBatchWorker extends BatchWorker {
    constructor(coqw, pkgr) {
        super(coqw.worker);
        this.coqw = coqw;     this.pkgr = pkgr;
        if (this.coqw instanceof CoqSubprocessAdapter)
            this.volume = fsif_native;
    }

    async loadPackages(pkgs) {
        if (this.coqw instanceof CoqSubprocessAdapter)
            return [this.coqw.worker.packages.dir];

        await this.coqw.when_created;
        await this.do(
            ['LoadPkg', this.getURIs([...pkgs])],
            msg => msg[0] == 'LoadedPkg'
        );
        this.loadpath = ['/lib'];
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

    constructor(inproj) {
        this.inproj = inproj;
        this.errors = new Map();
        this.editor = undefined;
    }

    add(e) {
        switch (e[0]) {
        case 'CoqExn':
            var err = this.decorateError(e);
            coq.layout.log(err.msg, 'Error');   // oops
            if (err.loc) {
                this.errors.set(err.loc.filename,
                    (this.errors.get(err.loc.filename) || []).concat([err]));
                this._updateMarks();
            }
            break;
        }
    }

    clear() {
        this.errors = new Map();
        this._updateMarks();
    }

    decorateError(coqexn) {
        let [, loc, , msg] = coqexn, err = {};
        // Convert character positions to {line, ch}
        if (loc) {
            err.loc = {filename: loc.fname[1].replace(/^(\/tmp)?\/lib\//, '/')};  // @@@ this is ugly
            try {
                var fn = err.loc.filename,
                    source = this.inproj.volume.fs.readFileSync(fn);
                err.loc.start = BuildReport.posToLineCh(source, loc.bp);
                err.loc.end =   BuildReport.posToLineCh(source, loc.ep);
            }
            catch (e) { console.warn('cannot get code location for', loc, e); }
        }
        var at = err.loc &&
            `${err.loc.filename}:${err.loc.start ? err.loc.start.line + 1 : '?'}`
        err.msg = $('<p>').text(`at ${at || '<unknown>'}:`).addClass('error-location')
                  .add(coq.pprint.pp2DOM(msg));  // oops
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
