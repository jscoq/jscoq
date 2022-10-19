//@ts-check

// The CoqManager class.
// Copyright (C) 2015-2017 Mines ParisTech/ARMINES
//
// CoqManager manages a document composed of several coq snippets,
// allowing the user to send/retract indivual coq sentences throu
// them. The Coq snippets can be provided by several sources, we just
// require them to be able to list parts and implement marks.

"use strict";

/**
  * @typedef { import("../../../backend").Goals } Goals
  */

// Backend imports
import { Future, CoqWorker, CoqSubprocessAdapter } from '../../../backend';
import { CoqIdentifier } from '../../../backend/coq-identifier.js';

// UI imports
import $ from 'jquery';
import { FormatPrettyPrint } from '../../format-pprint/js';
import { throttle } from 'throttle-debounce';

// Common imports
import { copyOptions, isMac, ArrayFuncs, arreq_deep } from '../../common/etc.js';

// UI Frontend imports
import { PackageManager } from './coq-packages.js';
import { CoqLayoutClassic } from './coq-layout-classic.js';
import { CoqContextualInfo } from './contextual-info.js';

// XXX Port to CM 6.x
// import { CompanyCoq }  from './addon/company-coq.js';

import { CoqCodeMirror5 } from './coq-editor-cm5.js';
import { CoqCodeMirror6 } from './coq-editor-cm6.js';
import { CoqProseMirror } from './coq-editor-pm.js';

/**
 * Coq Document Manager, client-side.
 *
 * CoqManager coordinates the coq code objects, the panel, and the coq
 * js object.
 *
 * CoqManager coordinates the coq code objects, the panel, and the Coq
 * worker.
 *
 * @class CoqManager
 */
export class CoqManager {

    /**
     * Creates an instance of CoqManager.
     * @param {string[]} elems
     * @param {object} options
     * @memberof CoqManager
     */
    constructor(elems, options) {

        options = options ? options : {};

        var pkg_path = PackageManager.defaultPkgPath(options.base_path || './');

        // Default options
        this.options = {
            prelaunch:  false,
            frontend:   'cm5',     // 'pm' | 'cm5' | 'cm6'
            prelude:    true,
            debug:      true,
            show:       true,
            replace:    false,
            wrapper_id: 'ide-wrapper',
            theme:      'light',
            base_path:   "./",
            node_modules_path: "./node_modules/",
            backend: "js",
            content_type: 'plain',  // 'plain' | 'markdown'
            pkg_path,
            implicit_libs: false,
            init_pkgs: ['init'],
            all_pkgs:  ['coq'].concat(PKG_AFFILIATES),
            init_import: [],
            file_dialog: false,
            line_numbers: 'continue',
            coq:       { /* Coq option values */ },
            editor:    { /* codemirror options */ }
        };

        this.options = copyOptions(options, this.options);

        if (Array.isArray(this.options.all_pkgs)) {
            this.options.all_pkgs = {'+': this.options.all_pkgs};
        }

        // Setup the Coq editor.
        var frontend = { 'pm': CoqProseMirror, 'cm5': CoqCodeMirror5, 'cm6': CoqCodeMirror6 };
        var CoqEditor = frontend[this.options.frontend];

        if (!CoqEditor)
            throw new Error(`invalid frontend specification: '${this.options.frontend}'`);

        this.editor = new CoqEditor(elems, this.options.editor, this);
        this.editor.onChangeRev = throttle(200, (newText, version) => {
            this.coq.update(this.preprocess(newText), version);
        });

        // Setup preprocess method for markdown, if needed
        var preprocessFunc = { 'plain': x => x, 'markdown': this.markdownPreprocess };

        this.preprocess = preprocessFunc[this.options.content_type];

        if (!this.preprocess)
            throw new Error(`invalid content type: '${this.options.content_type}'`);

        /** @type {PackageManager} */
        this.packages = null;

        /** @type {CoqContextualInfo} */
        this.contextual_info = null;

        /** @type {CoqWorker} */
        this.coq = null;

        // Setup the Panel UI.
        this.layout = new CoqLayoutClassic(this.options, {kb: this.keyTooltips()});
        this.layout.splash(undefined, undefined, 'wait');
        this.layout.onAction = this.toolbarClickHandler.bind(this);

        this.layout.onToggle = ev => {
            if (ev.shown && !this.coq) this.launch();
            if (this.coq) this.layout.onToggle = () => {};
        };

        this._setupSettings();
        this._setupDragDrop();

        // Setup pretty printer for feedback and goals
        this.pprint = new FormatPrettyPrint();

        // Keybindings setup
        // XXX: This should go in the panel init.
        document.addEventListener('keydown', evt => this.keyHandler(evt), true);
        $(document).on('keydown keyup', evt => this.modifierKeyHandler(evt));

        this.navEnabled = false;
        this.when_ready = new Future();

        // Launch time
        if (this.options.prelaunch)
            this.launch();

        if (this.options.show)
            requestAnimationFrame(() => this.layout.show());
    }

    /**
     * Set up hooks for when user changes settings.
     */
     _setupSettings() {
        const editorThemes = {'light': 'default', 'dark': 'blackboard'};
        this.layout.settings.model.theme.observe(theme => {
            /* this might take some time (do async like renumber?) */
            this.editor.configure({theme: editorThemes[theme]});
        });
        // this.layout.settings.model.company.observe(enable => {
        //     this.provider.configure({mode: {'company-coq': enable}});
        //     this.company_coq = this.contextual_info.company_coq =
        //         enable ? new CompanyCoq() : undefined;
        // });
    }

    _setupDragDrop() {
        $(this.layout.ide).on('dragover', (evt) => {
            evt.preventDefault();
            evt.originalEvent.dataTransfer.dropEffect = 'link';
        });
        $(this.layout.ide).on('drop', async (evt) => {
            evt.preventDefault();
            var src = []
            for (let item of evt.originalEvent.dataTransfer.items) {
                var entry = item.webkitGetAsEntry && item.webkitGetAsEntry(),
                    file = item.getAsFile && item.getAsFile();
                if (file && file.name.match(/[.]coq-pkg$/))
                    this.packages.dropPackage(file);
                else
                    src.push({entry, file});
            }
            // Turn to source files
            let project = () => this.project ||
                                this.openProject().then(() => this.project);
            if (src.length > 0) {
                if (src.length > 1 || src[0].entry && src[0].entry.isDirectory)
                    (await project()).openDirectory(
                            src.map(({entry, file}) => entry || file));
                else if (src[0].file && src[0].file.name.match(/[.]zip$/))
                    (await project()).openZip(src[0].file, src[0].file.name);
                else
                    // TODO better check file type and size before
                    //  opening
                    this.provider.openFile(file);
            }
        });
    }

    /**
     * Reads symbols from a URL and populates CompanyCoq.vocab.
     * @param {string} url address of .symb.json resource
     */
    loadSymbolsFrom(url, scope="globals") {
        $.get({url, dataType: 'json'}).done(data => {
            return;
            // CompanyCoq.loadSymbols(data, scope, /*replace_existing=*/false);
        })
        .fail((_, status, msg) => {
            console.warn(`Symbol resource unavailable: ${url} (${status}, ${msg})`)
        });
    }

    async openProject(name) {
        var pane = this.layout.createOutline();
        await this._load('dist-webpack/ide-project.browser.js');

        this.project = ideProject.ProjectPanel.attach(this, pane, name);
    }

    async openCollab(documentKey) {
        await this._load('dist-webpack/addon/collab.browser.js');
        this.collab = {
            hastebin: addonCollab.Hastebin.attach(this, documentKey?.hastebin),
            p2p: addonCollab.CollabP2P.attach(this, documentKey?.p2p)
        };
    }

    async _load(...hrefs) {
        for (let href of hrefs) {
            var uri = this.options.base_path + href,
                el = href.endsWith('.css') ?
                    $('<link>').attr({rel: 'stylesheet', type: 'text/css', href: uri})
                  : $('<script>').attr({type: 'text/javascript', src: uri});
            document.head.appendChild(el[0]); // jQuery messes with load event
            await new Promise(resolve => el.on('load', resolve));
        }
    }

    getLoadPath() {
        // @ts-ignore
        if (this.options.subproc) return [this.coq.worker.packages.dir];
        else return ArrayFuncs.flatten(
            [this.packages, this.project].map(p => p ? p.getLoadPath() : []));
    }

    /**
     * Starts a Worker and commences loading of packages and initialization of Coq
     */
    async launch() {
        try {
            // Setup the Coq worker.
            this.coq = this.options.subproc
                ? new CoqSubprocessAdapter(this.options.base_path, this.options.backend)
                : new CoqWorker(this.options.base_path, null, null, this.options.backend);
            this.coq.observers.push(this);

            if (this.options.debug) {
                this.coq.config.debug = true;
            }

            // @todo load progress with an egg
            let progressFmt = (pc, ev) =>
                typeof pc === 'number' ? `${Math.round(pc * 100)}%` : `${(ev.loaded / 1e6).toFixed(1)} MB`;
            this.coq.load_progress = (pc, ev) =>
                this.layout.splash(`Loading worker... ${progressFmt(pc, ev)}`, undefined, 'wait');

            // this.provider.wait_for = this.when_ready;

            // Setup package loader
            var pkg_path_aliases = {'+': this.options.pkg_path,
                ...Object.fromEntries(PKG_AFFILIATES.map(ap =>
                    [`+/${ap}`, `${this.options.node_modules_path}@jscoq/${ap}/coq-pkgs`]))
            };

            this.packages = new PackageManager(
                this.layout.packages,
                this.options.all_pkgs,
                pkg_path_aliases,
                this.coq,
                this.options.backend
            );

            this.packages.expand();
            this.packages.populate();

            // Setup autocomplete
            for (let pkg of ['init', 'coq-base', 'coq-collections', 'coq-arith', 'coq-reals'])
                this.loadSymbolsFrom(`${this.options.pkg_path}/${pkg}.symb.json`);

            // Setup contextual info bar
            // this.contextual_info = new CoqContextualInfo($(this.layout.proof).parent(),
            //                                             this.coq, this.pprint, this.company_coq);

            if (this.options.backend !== 'wa') {
                await this.coq.when_created;
                this.coqBoot();  // only the WA backend emits `Boot` events
            }
        }
        catch (err) {
            this.handleLaunchFailure(err);
        }
    }

    async coqBoot() {
        this.coq.interruptSetup();
        try {
            await this.packages.loadDeps(this.options.init_pkgs);
        }
        catch (e) {
            this.layout.systemNotification(
                `===> Failed loading initial packages [${this.options.init_pkgs.join(', ')}]`);
        }
        this.coqInit();
    }

    /**
     * Called when the first state is ready.
     */
    coqReady() {
        this.layout.splash(this.version_info, "Coq worker is ready.", 'ready');
        this.enable();
        this.when_ready.resolve();
    }

    // Coq document diagnostics.
    coqNotification(diags, version) {

        this.editor.clearMarks();

        console.log("Diags received: " + diags.length.toString());
        let suppress = false;
        for (let d of diags.reverse()) {
            for (let extra of d.extra) {
                if (extra[0] === 'FailedRequire' &&
                        this.handleRequires(extra)) {
                    this.editor.markDiagnostic({...d, inProgress: true});
                    suppress = true;
                }
            }
            // d_str = JSON.stringify(d);
            // this.layout.log("Diag", 'Info');
            // this.layout.log(d.message, 'Info');
            // this.layout.log(JSON.stringify(d), 'Info');
            if (d.severity < 4 && !suppress) {
                this.editor.markDiagnostic(d, version);
            }
        }
    }

    coqLog(level, msg) {

        let fmsg = this.pprint.msg2DOM(msg);

        level = level[0];

        // if (this.options.debug) {
        if (false) {
            if (level === 'Debug')
                console.debug(fmsg, level)
            else
                console.log(fmsg, level);
        }

        var item = this.layout.log(fmsg, level);
        this.pprint.adjustBreaks(item);
    }

    coqLibError(bname, msg) {
        this.layout.log(`Package '${bname}' is missing (${msg})`, 'Warning');
    }

    coqJsonExn(msg) {
        console.error('JsonExn', msg);
        this.layout.log(msg, "Error");
    }

    // This is received only after all the info for the packages has
    // been delivered. At first, I purposely avoided to have the
    // package manager implemented in JS due to this, but I've changed
    // the protocol so the JS-side package manager will have the
    // information it needs before we get this event.
    //
    // Usually, writing this stuff in OCaml is quite more compact than
    // the corresponding JS-version (not to speak of types)
    coqCoqInfo(info) {

        this.version_info = info;

        var pkgs = this.options.init_pkgs;

        this.layout.splash(info,
            pkgs.length == 0 ? undefined :
              "Loading libraries. Please wait.\n"
            + "(If you are having trouble, try cleaning your browser's cache.)");
    }

    // Coq Init: At this point, the required libraries are loaded
    // and Coq is ready to be used.
    coqInit() {

        this.packages.collapse();

        this.layout.systemNotification(
            `===> Loaded packages [${this.options.init_pkgs.join(', ')}]`);

        // Set startup parameters
        let init_opts = {
                implicit_libs: this.options.implicit_libs,
                coq_options: this._parseOptions(this.options.coq || {}),
                debug: {coq: true, stm: true}
            };

        this.coq.init(init_opts)
        this.newDoc();
        // Now we wait for the `Ready` event.
    }

    /**
     * Creates a JSON-able version of the startup Coq options.
     * E.g. {'Default Timeout': 10}  -->  [[['Default', 'Timeout'], ['IntValue', 10]]]
     * @param {object} coq_options option name to value dictionary
     */
    _parseOptions(coq_options) {
        function makeValue(value) {
            if      (Array.isArray(value))       return value;
            else if (typeof value === 'number')  return ['IntValue', value];
            else if (typeof value === 'string')  return ['StringValue', value];
            else if (typeof value === 'boolean') return ['BoolValue', value]

            throw new Error(`invalid option value ${value}`);
        }
        return Object.entries(coq_options)
                     .map(([k, v]) => [k.split(/\s+/), makeValue(v)]);
    }


    /**
     * Strip off plain text, leaving the Coq text.
     * @param {string} text 
     */
    markdownPreprocess(text) {
        let wsfill = s => s.replace(/[^\n]/g, ' ');
        return text.split(/```([^]*?)```/g)
                   .map((x, i) => i & 1 ? `   ${x}   ` : wsfill(x))
                   .join('');
    }

    interruptRequest() {
        // Emilio: this needs tweaking in the LSP backend
        this.coq.interrupt();
    }

    newDoc() {
        let doc_opts = {
            lib_path: this.getLoadPath(),
            lib_init: this.options.prelude ? [PKG_ALIASES.prelude] : []
        };

        for (let pkg of this.options.init_import || []) {
            doc_opts.lib_init.push(PKG_ALIASES[pkg] || pkg);
        }

        this.coq.newDoc(doc_opts, this.preprocess(this.editor.getValue()));
    }

    /**
     * Handles a critial error during worker load/launch.
     * Typically, failure to fetch the jscoq_worker script.
     * @param {Error} err load error
     */
    handleLaunchFailure(err) {
        console.error('launch failure', err);
        this.layout.log("Failed to start jsCoq worker.", 'Error');
        if (typeof window !== 'undefined' && window.location.protocol === 'file:') {
            this.layout.log($('<span>').html(
                "(Serving from local file;\n" +
                "has <i>--allow-file-access-from-files</i> been set?)"), 'Info');
        }
    }

    /**
     * Handles a `FailedRequire` diagnostic by looking for missing modules in
     * the package index. 
     * @param {['FailedRequire', {prefix: {v: any[]}, refs: {v: any[]}[]}]} info 
     * @return {boolean} whether additional packages are being loaded
     */
    handleRequires(info) {
        let op = qid => CoqIdentifier.ofQualid(qid).toStrings(),
            prefix = info[1].prefix ? op(info[1].prefix.v) : [],
            pkgDeps = new Set();

        for (let suffix of info[1].refs.map(r => op(r.v))) {
            for (let dep of this.packages.index.findPackageDeps(prefix, suffix))
                pkgDeps.add(dep);
        }

        for (let d of this.packages.loaded_pkgs) pkgDeps.delete(d);

        if (pkgDeps.size > 0) {
            this.handleMissingDeps([...pkgDeps]);  /* do not await; happens async */
            return true;   /* let the document know that loading is now in progress */
        }
        else
            return false;
    }

    /**
     * Loads some packages and re-checks the document.
     * @param {string[]} pkgs packages to load
     */
    async handleMissingDeps(pkgs) {
        this.disable();
        this.packages.expand();
        let loaded = await this.packages.loadDeps(pkgs);
        this.layout.systemNotification(
            `===> Loaded packages [${loaded.map(p => p.name).join(', ')}]`);
        this.enable();
        setTimeout(() => this.packages.collapse(), 500);
        /* need to re-create the document now that the loadpath has changed */
        this.newDoc();
    }

    /**
     * Drops all the state and re-launches the worker.
     * Loaded packages are reloaded (but obviously not Require'd) by the
     * package manager.
     * @returns {Promise} resolves after 'init' command has been issued.
     */
    async reset() {
        this.layout.update_goals($('<b>').text('Coq worker reset.'));
        this.disable();
        this.coq.restart();

        // Reload packages and init
        var pkgs = this.packages.loaded_pkgs.slice();
        this.packages.reset();
        return this.packages.loadDeps(pkgs).then(() => this.coqInit());
    }

    /**
     * Shows the goal at a given location.
     * @param {number?} offset document offset (defaults to current cursor position).
     */
    async setGoalCursor(offset = undefined) {
        offset ??= this.editor.getCursorOffset();
        let resp = await this.coq.sendRequest(offset, ['Goals']);
        if (resp[1])
            this.updateGoals(resp[1]);
    }

    updateGoals(goals) {
        var hgoals = this.goals2DOM(goals);

        if (hgoals) {
            this.layout.update_goals(hgoals);
            this.pprint.adjustBreaks($(this.layout.proof));
            /* Notice: in Pp-formatted text, line breaks are handled by
             * FormatPrettyPrint rather than by the layout.
             */
        }
    }

    keyTooltips() {
        return isMac ? {up: '⌥↑', down: '⌥↓', cursor: '⌥⏎', help: 'F1'} :
            {up: 'Alt-↑/P', down: 'Alt-↓/N', cursor: 'Alt-Enter', help: 'F1'}
    }

    /**
     * Key bindings event handler.
     * @param {KeyboardEvent} e a keydown event
     */
    keyHandler(e) {

        // Poor-man's keymap
        let key = ((isMac ? e.metaKey : e.ctrlKey) ? '^' : '') +
                  (e.altKey ? '_' : '') + (e.shiftKey ? '+' : '') + e.code;

        // Navigation keybindings
        const toggle = () => this.layout.toggle(),
              help   = () => this.layout.toggleHelp(),
              interrupt = () => this.interruptRequest();

        const toCursor  = () => this.setGoalCursor();
        const nav_bindings = {
            '_Enter':     toCursor, '_NumpadEnter': toCursor,
            '^Enter':     toCursor, '^NumpadEnter': toCursor,
            'F8': toggle,
            'F1': help,
            'Escape': interrupt
        };

        var op = nav_bindings[key];
        if (op) {
            e.preventDefault();
            e.stopPropagation();
            if (this.navEnabled) op();
            return true;
        }

        // File keybindings
        if (this.options.file_dialog) {
            const file_bindings = {
                '^KeyO':   () => sp.openLocalDialog(),
                '^_KeyO':  () => sp.openFileDialog(),
                '^KeyS':   () => sp.saveLocal(),
                '^+KeyS':  () => sp.saveLocalDialog(),
                '^_KeyS':  () => sp.saveToFile()
            };

            var op = file_bindings[key];
            if (op) {
                e.preventDefault();
                e.stopPropagation();
                op();
                return true;
            }
        }
    }

    modifierKeyHandler(evt) {
        if (evt.key === 'Control') {
            if (evt.ctrlKey)
                this.layout.ide.classList.add('coq-crosshair');
            else
                this.layout.ide.classList.remove('coq-crosshair');
        }
    }

    // Enable the IDE.
    enable() {
        this.navEnabled = true;
        this.layout.toolbarOn();
    }

    // Disable the IDE.
    disable() {
        this.navEnabled = false;
        this.layout.toolbarOff();
        this.layout.systemNotification(
                "===> Waiting for package(s) to load.");
    }

    toolbarClickHandler(evt) {

        this.editor.focus();

        switch (evt.target.name) {
        case 'to-cursor' :
            console.log('deprecated action');
            break;

        case 'up' :
            console.log('deprecated action');
            break;

        case 'down' :
            console.log('deprecated action');
            break;

        case 'interrupt':
            console.log('deprecated action');
            break;

        case 'reset':
            this.reset();
            break;
        }
    }

    editorActionHandler(action) {
        switch (action.type) {
        case 'share-hastebin':   this.actionShareHastebin(); break;
        case 'share-p2p':        this.actionShareP2P();      break;
        }
    }

    async actionShareHastebin() {
        if (!this.collab) await this.openCollab();
        this.collab.hastebin.save();
    }

    async actionShareP2P() {
        if (!this.collab) await this.openCollab();
        this.collab.p2p.save();
    }

    // Aux function for goals2DOM
    flatLength(l) {
        return Array.isArray(l)
            ? l.map(x => this.flatLength(x)).reduce((x,y) => x + y, 0)
            : 1;
    }

    /**
     * Formats the current proof state.
     * @param {Goals} goals
     */
    goals2DOM(goals) {
        var ngoals = goals.goals.length,
            on_stack = this.flatLength(goals.stack),
            on_shelf = goals.shelf.length,
            given_up = goals.given_up.length;

        function aside(msg) {
            var p = $('<p>').addClass('aside');
            return (typeof msg === 'string') ? p.text(msg) : p.append(msg);
        }

        if (ngoals === 0) {
            /* Empty goals; choose the appropriate message to display */
            let msg = on_stack ? "This subproof is complete, but there are some unfocused goals."
                    : (on_shelf ? "All the remaining goals are on the shelf."
                        : "No more goals."),
                bullet_notice = goals.bullet ? [this.pprint.pp2DOM(goals.bullet)] : [],
                given_up_notice = given_up ?
                    [`(${given_up} goal${given_up > 1 ? 's were' : ' was'} admitted.)`] : [],
                notices = bullet_notice.concat(given_up_notice);

            return $('<div>').append(
                $('<p>').addClass('no-goals').text(msg),
                notices.map(aside)
            );
        }
        else {
            /* Construct a display of all the subgoals (first is focused) */
            let head = ngoals === 1 ? `1 goal` : `${ngoals} goals`,
                notices = on_shelf ? [`(shelved: ${on_shelf})`] : [];

            let focused_goal = this.goal2DOM(goals.goals[0]);

            let pending_goals = goals.goals.slice(1).map((goal, i) =>
                $('<div>').addClass('coq-subgoal-pending')
                    .append($('<label>').text(i + 2))
                    .append(this.pprint.pp2DOM(goal.ty)));

            return $('<div>').append(
                $('<p>').addClass('num-goals').text(head),
                notices.map(aside),
                focused_goal, pending_goals
            );
        }
    }

    /**
     * Formats a single, focused goal.
     * Shows an environment containing hypothesis and goal type.
     * @param {object} goal current goal record ({name, hyp, ty})
     */
    goal2DOM(goal) {
        let mklabel = (id) =>
                $('<label>').text(FormatPrettyPrint._idToString(id)),
            mkdef = (pp) =>
                $('<span>').addClass('def').append(this.pprint.pp2DOM(pp));

        let hyps = goal.hyp.reverse().map(([h_names, h_def, h_type]) =>
            $('<div>').addClass(['coq-hypothesis', h_def && 'coq-has-def'])
                .append(h_names.map(mklabel))
                .append(h_def && mkdef(h_def))
                .append($('<div>').append(this.pprint.pp2DOM(h_type))));
        let ty = this.pprint.pp2DOM(goal.ty);
        return $('<div>').addClass('coq-env').append(hyps, $('<hr/>'), ty);
    }

}

const PKG_ALIASES = {
    prelude: "Coq.Init.Prelude",
    utf8: "Coq.Unicode.Utf8"
};

const PKG_AFFILIATES = [  // Affiliated packages in @jscoq/@wacoq scope
    'mathcomp', 'elpi', 'equations', 'extlib', 'simpleio', 'quickchick',
    'software-foundations',
    'hahn', 'paco', 'snu-sflib',
    'fcsl-pcm', 'htt', 'pnp', 'coqoban', 'stdpp', 'iris'
];

// Local Variables:
// js-indent-level: 4
// End:
