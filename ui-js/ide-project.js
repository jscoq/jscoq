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
        require('./components/problem-list');

        this.view = new (Vue.component('project-panel-default-layout'))();
        this.view.$mount();
        
        this.view.$watch('files', v => this._update(v, this.view.status));
        this.view.$watch('status', v => this._update(this.view.files, v), {deep: true});
        this.view.$on('action', ev => this.onAction(ev));
        this.view.$on('new', () => this.clear());
        this.view.$on('build', () => this.buildTask ? (this.buildTask.stop())
             : this.buildDeploy().catch(e => { if (e[0] != 'CoqExn') throw e; }));
        this.view.$on('download', () => this.download());

        this.view.$on('menu:new', () => this.clear());
        this.view.$on('menu:open', () => this.openDialog());
        this.view.$on('menu:download-v', () => this.downloadSources());
        this.view.$on('menu:download-vo', () => this.downloadCompiled());

        this.editor_provider = undefined;
        this.package_index = undefined;
    }

    get $el() { return this.view.$el; }

    clear() {
        this.open(new CoqProject('untitled', new LogicalVolume()));
    }

    open(project) {
        this.project = project;
        this.view.root = [];
        this.view.files = [...project.modulesByExt('.v')]
                          .map(mod => mod.physical);
        this.view.status = {};

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
        //this.view.files.push(filename);
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

    async build(coq) {
        this.view.building = true;
        this.view.status = {};
        this.report.clear();

        try {
            if (this.editor_provider && this.editor_provider.dirty)
                this.editor_provider.saveLocal();

            if (this.package_index || this.coq)
                this.project.searchPath.packageIndex = this.package_index || this.coq.packages.index;

            coq = coq || await this._createBuildWorker();
            coq.options.warn = false;

            var task = new CompileTask(new BatchWorker(coq.worker), this.project,
                {loadpath: this.coq && this.coq.packages.getLoadPath()});
            this.buildTask = task;
            task.on('progress', files => this._progress(files));
            task.on('report', e => this.report.add(e));
            await coq.when_created;
            return this.out = await task.run();
        }
        finally {
            this.buildTask = null;
            this.view.building = false;
            this.view.compiled = !!this.out;
        }
    }

    deploy() {
        if (this.out && this.coq) {
            for (let vo of this.out.modulesByExt('.vo')) {
                console.log(`> ${vo.physical}`);
                this.coq.coq.put(vo.physical, vo.volume.readFileSync(vo.physical));
            }
        }
    }

    async buildDeploy(coq) {
        await this.build(coq);
        this.deploy();
    }

    getLoadPath() {
        return this.out ? 
            this.out.searchPath.path.map(pel => [pel.logical, ['/lib']]) : [];
    }

    async _createBuildWorker() {
        var coq = new CoqWorker();
        if (this.coq) {
            await coq.when_created;
            for (let pkg of this.coq.packages.loaded_pkgs) {
                await this.coq.packages.packages_by_name[pkg].archive.unpack(coq);
            }
        }
        return coq;
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

    _update(files, status) {
        for (let filename of files) {
            var e = this.view.$refs.file_list.create(filename),
                fstatus = status[filename];
            e.tags = fstatus ? [ProjectPanel.BULLETS[fstatus]] : [];
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
            async setItem(filename, content) { volume.writeFileSync(filename, content); }
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
        case 'create':
            this.addFile(`/${ev.path.join('/')}`, ev.content);
            break;
        }
    }

    static attach(coq, container, name) {
        var panel = new ProjectPanel().withCoqManager(coq);
        container.append(panel.$el);

        if (name == 'sample')
            panel.open(ProjectPanel.sample());
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
        vol.fs.writeFileSync('/simple/Two.v', 'From Coq Require Import List.\n\nDefinition two_of a := a + a.\n');
        vol.fs.writeFileSync('/simple/Three.v', 'From simple Require Import One Two.');
    
        var proj = new CoqProject('sample', vol).fromDirectory('/');
        return proj;
    }    

}


ProjectPanel.BULLETS = {
    compiling: {text: '◎', class: 'compiling'},
    compiled: {text: '✓', class: 'compiled'},
    error: {text: '✗', class: 'error'}
};


Vue.component('project-panel-default-layout', {
    data: () => (
        {files: [], status: {}, root: [], building: false, compiled: false}
    ),
    template: `
    <div class="project-panel vertical-pane">
        <div class="toolbar">
            <project-context-menu ref="menu" @action="$emit('menu:'+$event.name, $event)"/>
            <button @click="$emit('build')">{{building ? 'stop' : 'build'}}</button>
        </div>
        <file-list ref="file_list" :files="root"
                   @action="$emit('action', $event)"/>
    </div>
    `
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
    </span>
    `,
    components: {VueContext},
    methods: {
        open() {
            if (this.$refs.m.show) this.$refs.m.close();
            else
            this.$refs.m.open({clientX: this.$parent.$el.clientWidth, clientY: 0}); 
        },
        action(ev) {
            if (!$(ev.currentTarget).is('[disabled]'))
                this.$emit('action', {name: ev.currentTarget.name});
        }
    }
});

Vue.component('hamburger-svg', {
    template: `
    <svg viewBox="0 0 80 80">
        <rect y="5" width="80" height="12"></rect>
        <rect y="34" width="80" height="12"></rect>
        <rect y="63" width="80" height="12"></rect>
    </svg>
    `
})


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
            err.loc = {filename: loc.fname[1].replace(/^\/lib/, '')};
            try {
                var fn = err.loc.filename,
                    source = this.inproj.volume.fs.readFileSync(fn, 'utf-8');
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
