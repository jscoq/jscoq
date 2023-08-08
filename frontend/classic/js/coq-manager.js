//@ts-check

// The CoqManager class.
// Copyright (C) 2015-2017 Mines ParisTech/ARMINES
//
// CoqManager manages a document composed of several coq snippets,
// allowing the user to send/retract indivual coq sentences throu
// them. The Coq snippets can be provided by several sources, we just
// require them to be able to list parts and implement marks.
//

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

// Common imports
import { copyOptions, isMac, ArrayFuncs, arreq_deep } from '../../common/etc.js';

// UI imports
import { PackageManager } from './coq-packages.js';
import { CoqLayoutClassic } from './coq-layout-classic.js';
import { CmCoqProvider } from './cm-provider';
import { ProviderContainer } from './cm-provider-container';
import { CoqContextualInfo } from './contextual-info.js';
import { CompanyCoq }  from './addon/company-coq.js';

/**
 * Coq Document Manager, client-side
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
            prelude:    true,
            debug:      true,
            show:       true,
            focus:      true,
            replace:    false,
            wrapper_id: 'ide-wrapper',
            theme:      'light',
            base_path:   "./",
            node_modules_path: "./node_modules/",
            backend: "js",
            pkg_path,
            implicit_libs: false,
            init_pkgs: ['init'],
            all_pkgs:  ['coq'].concat(PKG_AFFILIATES),
            init_import: [],
            file_dialog: false,
            line_numbers: 'continue',
            coq:       { /* Coq option values */ },
            editor:    { /* codemirror options */ }
            // Disabled on 8.6
            // 'coquelicot', 'flocq', 'tlc', 'sf', 'cpdt', 'color', 'relalg', 'unimath',
            // 'plugin-utils', 'extlib', 'mirrorcore']
        };

        this.options = copyOptions(options, this.options);

        if (Array.isArray(this.options.all_pkgs)) {
            this.options.all_pkgs = {'+': this.options.all_pkgs};
        }

        // Setup the Coq statement provider.
        this.provider = this._setupProvider(elems);

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

        // Setup company-coq
        if (this.options.editor.mode && this.options.editor.mode['company-coq'])
            this.company_coq = new CompanyCoq();

        // Keybindings setup
        // XXX: This should go in the panel init.
        document.addEventListener('keydown', evt => this.keyHandler(evt), true);
        $(document).on('keydown keyup', evt => this.modifierKeyHandler(evt));

        // This is a sid-based index of processed statements.
        /**
         * @typedef {{text: string, coq_sid: number, flags: object, sp: CmCoqProvider, phase: object}} ManagerSentence
         * @type {{fresh_id: number, sentences: ManagerSentence[], stm_id: ManagerSentence[], goals: string[]}}
         */
        this.doc = {
            fresh_id:           2,
            sentences:         [],
            stm_id:            [],
            goals:             []
        };

        // Initial sentence. (It's a hack.)
        /** @type {CmCoqProvider} */
        let dummyProvider = { mark : function() {},
                              getNext: function() { return null; },
                              focus: function() { return null; },
                              cursorToEnd: function() { return null; }
                             };
        this.doc.stm_id[1] = { text: "dummy sentence", coq_sid: 1, flags: {},
                               sp: dummyProvider, phase: Phases.PROCESSED };
        this.doc.sentences = [this.doc.stm_id[1]];

        this.error = [];
        this.navEnabled = false;
        this.when_ready = new Future();

        // Launch time
        if (this.options.prelaunch)
            this.launch();

        if (this.options.show)
            requestAnimationFrame(() => this.layout.show());
    }

    // Provider setup
    _setupProvider(elems) {

        var provider = new ProviderContainer(elems, this.options);

        provider.onInvalidate = stm => {
            this.clearErrors();
            if (stm.coq_sid) {
                this.coq.cancel(stm.coq_sid);
            }
        };

        provider.onMouseEnter = (stm, ev) => {
            if (stm.coq_sid && ev.ctrlKey) {
                if (this.doc.goals[stm.coq_sid] !== undefined)
                    this.updateGoals(this.doc.goals[stm.coq_sid]);
                else
                    this.coq.goals(stm.coq_sid);  // XXX: async
            }
            else {
                this.updateGoals(this.doc.goals[this.lastAdded().coq_sid]);
            }
        };

        provider.onMouseLeave = (stm, ev) => {
            this.updateGoals(this.doc.goals[this.lastAdded().coq_sid]);
        };

        provider.onTipHover = (entries, zoom) => {
            var fullnames = new Set(entries.filter(e => e.kind === 'lemma')
                .map(entry => [...entry.prefix, entry.label].join('.')));
            if (fullnames.size > 0) {
                this.contextual_info.showChecks([...fullnames], /*opaque=*/true);
            }
        };
        provider.onTipOut = () => { if (this.contextual_info) this.contextual_info.hide(); };

        provider.onAction = (action) => this.editorActionHandler(action);

        return provider;
    }

    /**
     * Set up hooks for when user changes settings.
     */
     _setupSettings() {
        const editorThemes = {'light': 'default', 'dark': 'blackboard'};
        this.layout.settings.model.theme.observe(theme => {
            /* this might take some time (do async like renumber?) */
            this.provider.configure({theme: editorThemes[theme]});
        });
        this.layout.settings.model.company.observe(enable => {
            this.provider.configure({mode: {'company-coq': enable}});
            this.company_coq = this.contextual_info.company_coq =
                enable ? new CompanyCoq() : undefined;
        });
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
            CompanyCoq.loadSymbols(data, scope, /*replace_existing=*/false);
        })
        .fail((_, status, msg) => {
            console.warn(`Symbol resource unavailable: ${url} (${status}, ${msg})`)
        });
    }

    updateLocalSymbols() {
        this.coq.inspectPromise(0, ["CurrentFile"])
        .then(bunch => {
            CompanyCoq.loadSymbols(
                { lemmas: bunch.map(fp => CoqIdentifier.ofQualifiedName(fp)) },
                'locals', /*replace_existing=*/true)
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
            p2p: addonCollab.CollabP2P.attach(this, documentKey?.p2p),
            gist: addonCollab.Gist.attach(this, documentKey?.gist)
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
     * Starts a Worker and commences loading of packages and initialization
     * of STM.
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

            this.provider.wait_for = this.when_ready;

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
            this.contextual_info = new CoqContextualInfo($(this.layout.proof).parent(),
                                                        this.coq, this.pprint, this.company_coq);

            if (this.options.backend !== 'wa') {
                await this.coq.when_created;
                this.coqBoot();  // only the WA backend emits `Boot` events
            }
        }
        catch (err) {
            this.handleLaunchFailure(err);
        }
    }

    // Feedback Processing
    feedProcessingIn(sid) {
    }

    feedFileDependency(sid, file, mod) {
        let msg = `${mod} loading....`,
            item = this.layout.log(msg, 'Info', {fast: true});
        item.addClass('loading').data('mod', mod);
    }

    feedFileLoaded(sid, mod, file) {
        let item = ArrayFuncs.findLast([...this.layout.query.getElementsByClassName('loading')],
                                       x => $(x).data('mod') === mod),
            msg = `${mod} loaded.`;

        if (item)
            $(item).removeClass('loading').text(msg);
        else
            this.layout.log(msg, 'Info', {fast: true});
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
     * @param {number} sid
     */
    coqReady(sid) {
        this.layout.splash(this.version_info, "Coq worker is ready.", 'ready');
        this.doc.sentences[0].coq_sid = sid;
        this.doc.fresh_id = sid + 1;
        this.enable();
        this.when_ready.resolve();
    }

    /**
     * @param {number} nsid
     */
    feedProcessed(nsid) {

        if(this.options.debug)
            console.log('State processed', nsid);

        // The semantics of the stm here were a bit inconvenient: it
        // would send `ProcessedReady` feedback message before the
        // `Stm.add` call has returned, thus we were not ready to
        // handle as we didn't know of their existance yet. The
        // typical example is when `Stm.add` forces an observe due to
        // side-effects.
        //
        // The new approach avoids this, but we ignore such feedback
        // just in case.

        var stm = this.doc.stm_id[nsid];

        if (!stm) {
            console.log('ready but cancelled user side?', nsid);
            return;
        }

        if (stm.phase !== Phases.PROCESSED && stm.phase !== Phases.ERROR) {
            stm.phase = Phases.PROCESSED;
            this.provider.mark(stm, 'ok');

            // Get goals and active definitions
            if (nsid == this.lastAdded().coq_sid) {
                this.coq.goals(nsid);
                this.updateLocalSymbols();
            }
            else this.coq.query(nsid, 0, ['Mode']);
        }

        this.work();
    }

    /**
     * @param {number} sid
     * @param {string} lvl
     * @param {any} loc
     * @param {any} msg
     */
    feedMessage(sid, lvl, loc, msg) {

        var fmsg = this.pprint.msg2DOM(msg);

        lvl = lvl[0];  // JSON encoding

        if(this.options.debug)
            console.log('Message', sid, lvl, fmsg);

        // Filter duplicate errors generated by Stm/Jscoq_worker
        if (lvl === 'Error' && this.error.some(stm => stm.coq_sid === sid &&
                                    stm.feedback.some(x => arreq_deep(x.msg, msg))))
            return;

        let stm = this.doc.stm_id[sid];
        if (stm) stm.feedback.push({level: lvl, loc, msg});

        var item = this.layout.log(fmsg, lvl, {'data-coq-sid': sid});
        this.pprint.adjustBreaks(item);

        // XXX: highlight error location.
        if (lvl === 'Error') {
            this.handleError(sid, loc, fmsg);
        }
    }

    // Coq Message processing.
    /**
     * @param {number} nsid
     * @param {any} loc
     */
    coqAdded(nsid,loc) {

        if(this.options.debug)
            console.log('adding: ', nsid, loc);

        let stm = this.doc.stm_id[nsid];

        if (stm)
            stm.phase = Phases.ADDED;

        this.work();
    }

    // Gets a request to load packages
    coqPending(nsid, prefix, module_names) {
        let stm = this.doc.stm_id[nsid];
        let ontop = this.lastAdded(nsid);

        let ontop_finished =    // assumes that exec is harmless if ontop was executed already...
            this.coq.execPromise(ontop.coq_sid);

        var pkg_deps_set = new Set();
        for (let module_name of module_names) {
            let deps = this.packages.index.findPackageDeps(prefix, module_name)
            for (let dep of deps) pkg_deps_set.add(dep);
        }

        for (let d of this.packages.loaded_pkgs) pkg_deps_set.delete(d);

        var pkg_deps = [...pkg_deps_set];

        var cleanup = () => {};

        if (pkg_deps.length > 0) {
            console.log("Pending: loading packages", pkg_deps);
            this.disable();
            this.packages.expand();
            cleanup = () => { this.packages.collapse(); this.enable(); }
        }

        this.packages.loadDeps(pkg_deps).then(pkgs => {
            if (pkgs.length)
                this.layout.systemNotification(
                    `===> Loaded packages [${pkgs.map(p => p.name).join(', ')}]`);

            ontop_finished.then(() => {
                this.coq.refreshLoadPath(this.getLoadPath());
                this.coq.resolve(ontop.coq_sid, nsid, stm.text);
                cleanup();
            });
        });
    }

    // Gets a list of cancelled sids.
    coqCancelled(sids) {

        if(this.options.debug)
            console.log('cancelling', sids);

        for (let sid of sids) {
            let stm_to_cancel = this.doc.stm_id[sid];

            if (stm_to_cancel) {
                this.truncate(stm_to_cancel);
            }
        }

        this.tidy();
        this.refreshGoals();
    }

    coqBackTo(sid) {
        let new_tip = this.doc.stm_id[sid];
        if (new_tip && this.error.length == 0) {
            this.truncate(new_tip, true);
            this.refreshGoals();
        }
    }

    coqModeInfo(sid, in_mode) {
        let stm = this.doc.stm_id[sid];
        if (stm) {
            stm.action = in_mode == 'Proof' ? 'goals' : undefined;
        }
    }

    coqGoalInfo(sid, goals) {

        if (goals) {
            this.coqModeInfo(sid, 'Proof');

            var hgoals = this.goals2DOM(goals);

            // Preprocess pretty-printed output
            if (this.company_coq) {
                this.contextual_info.pinIdentifiers(hgoals);
                this.company_coq.markup.applyToDOM(hgoals[0]);
            }

            this.doc.goals[sid] = hgoals;
            this.updateGoals(hgoals);
        }
    }

    coqLog(level, msg) {

        let fmsg = this.pprint.msg2DOM(msg);

        level = level[0];

        if (this.options.debug) {
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

    coqCoqExn({pp, msg, sids}) {

        console.error('Coq Exception', msg);

        // If error has already been reported by Feedback, bail
        if (this.error.some(stm => stm.feedback.some(x => arreq_deep(x.msg, pp))))
            return;

        var fmsg = this.pprint.msg2DOM(pp);

        var item = this.layout.log(fmsg, 'Error', sids && {'data-coq-sid': sids[0]});
        this.pprint.adjustBreaks(item);
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
                debug: {coq: true, stm: true},
                lib_path: this.getLoadPath()
            },
            doc_opts = {
                lib_init: this.options.prelude ? [PKG_ALIASES.prelude] : []
            };

        for (let pkg of this.options.init_import || []) {
            doc_opts.lib_init.push(PKG_ALIASES[pkg] || pkg);
        }

        this.coq.init(init_opts, doc_opts);
        // Almost done!
        // Now we just wait for the `Ready` event.
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
     * @param {boolean} update_focus
     */
    goPrev(update_focus) {

        // There may be cases where there is more than one sentence with
        // an error, but then we probably want to retract all of them anyway.
        if (this.error.length > 0) {
            this.clearErrors();
            return true;
        }

        var back_to_stm = ArrayFuncs.findLast(this.doc.sentences.slice(0, -1),
            stm => !(stm.flags.is_comment || stm.flags.is_hidden));
        if (!back_to_stm) return false;

        var cancel_stm = this.nextAdded(back_to_stm.coq_sid);
        this.cancel(cancel_stm);

        if(update_focus) this.focus(back_to_stm);

        return true;
    }

    // Return if we had success.
    /**
     * @param {boolean} update_focus
     * @param {{ sp: CmCoqProvider; pos: any; } | undefined} [until]
     */
    goNext(update_focus, until) {

        this.clearErrors();

        let last_stm = ArrayFuncs.last(this.doc.sentences),
            next_stm = this.provider.getNext(last_stm, until),
            queue = [next_stm];

        // Step over comment block and hidden sections
        while (next_stm && (next_stm.flags.is_comment || next_stm.flags.is_hidden) &&
            (next_stm = this.provider.getNext(next_stm, until)))
            queue.push(next_stm);

        if (!next_stm && queue.every(stm => !stm || stm.flags.is_comment))
            return false;    // We have reached the end

        for (next_stm of queue) {
            next_stm.phase = Phases.PENDING;
            this.doc.sentences.push(next_stm);

            this.provider.mark(next_stm, 'processing');
        }

        if (update_focus) this.focus(next_stm);

        this.work();

        return true;
    }

    goCursor() {

        this.clearErrors();

        var cur = this.provider.getAtPoint();

        if (cur) {
            if (!cur.coq_sid) {
                var idx = this.doc.sentences.indexOf(cur);
                cur = this.doc.sentences.slice(idx).find(stm => stm.coq_sid);
            }
            if (cur) {
                this.coq.cancel(cur.coq_sid);
            }
            else {
                console.warn("in goCursor(): stm not registered");
            }
        } else {
            var here = this.provider.getCursor();
            while (this.goNext(false, here));
        }
    }

    interruptRequest() {
        // Avoid spurious interrupts by only requesting an interrupt
        // if there are still sentences being processed
        if (this.doc.sentences.some(x => x.phase == Phases.PROCESSING))
            this.coq.interrupt();
    }

    /**
     * Focus the snippet containing the stm and place the cursor at
     * the end of the sentence.
     */
    focus(stm) {
        this.currentFocus = stm.sp;
        this.currentFocus.focus();
        this.provider.cursorToEnd(stm);
    }

    /**
     * Document processing state machine.
     * Synchronizes the managers document (this.doc) with the Stm document
     * held by the worker.
     * That means, PENDING sentences are added and ADDED sentences are executed.
     */
    work() {
        var tip = null, latest_ready_stm = null,
            skip = stm => { stm.phase = Phases.PROCESSED; this.provider.mark(stm, 'ok'); }

        for (let stm of this.doc.sentences) {
            switch (stm.phase) {
            case Phases.PROCESSED:
                tip = stm.coq_sid; break;
            case Phases.ADDED:
                if (stm.flags.is_comment) {
                    if (!latest_ready_stm) skip(stm);  // all previous stms have been processed
                }
                else {
                    latest_ready_stm = stm;
                    tip = stm.coq_sid;
                }
                break; // only actually execute if nothing else remains to add
            case Phases.ADDING:
            case Phases.PROCESSING:
                return;  // still waiting for worker; can't make progress
            case Phases.PENDING:
                if (!tip) throw new Error('internal error'); // inconsistent
                this.add(stm, tip);
                if (stm.phase != Phases.ADDED) return;
            }
        }

        // TODO Don't queue too many sentences at once in order to avoid
        //   stack overflow in Stm
        if (latest_ready_stm) {
            latest_ready_stm.phase = Phases.PROCESSING;
            this.coq.exec(latest_ready_stm.coq_sid);
        }
    }

    /**
     * Clear dangling marks on comments (in case it was not handled by
     * previous calls to `work()` and `truncate()`).
     */
    tidy() {
        if (this.error.length == 0) {
            while (this.doc.sentences.slice(-1)[0].flags.is_comment) {
                this.cancelled(this.doc.sentences.pop());
            }
        }
    }

    async add(stm, tip) {
        if (stm.flags.is_comment) {
            stm.phase = Phases.ADDED;
            return;
        }

        stm.phase = Phases.ADDING;

        await this.process_special(stm.text);

        stm.coq_sid = this.doc.fresh_id++;
        this.doc.stm_id[stm.coq_sid] = stm;
        this.coq.add(tip, stm.coq_sid, stm.text);

        this.provider.mark(stm, 'processing');  // in case it was un-marked
    }

    cancel(stm) {
        if (stm.coq_sid) {
            switch (stm.phase) {
            case Phases.ADDING:
            case Phases.ADDED:
            case Phases.PROCESSING:
            case Phases.PROCESSED:
                stm.phase = Phases.CANCELLING;
                this.coq.cancel(stm.coq_sid);
                break;
            }
        }

        this.provider.mark(stm, 'clear');
    }

    cancelled(stm) {
        if (stm.coq_sid) {
            delete this.doc.stm_id[stm.coq_sid];
            delete stm.coq_sid;
        }

        this.provider.mark(stm, 'clear');
    }

    lastAdded(before=Infinity) {
        return ArrayFuncs.findLast(this.doc.sentences, stm => stm.coq_sid < before);
    }

    nextAdded(after=0) {
        return this.doc.sentences.find(stm => stm.coq_sid > after);
    }

    /**
     * Removes all the sentences from stm to the end of the document.
     * If stm as an error sentence, leave the sentence itself (so that the
     * error mark remains visible), and remove all following sentences.
     * @param stm a Sentence
     * @param plus_one if `true`, will skip `stm` and start instead from
     *   the *following* sentence.
     */
    truncate(stm, plus_one=false) {
        let stm_index = this.doc.sentences.indexOf(stm);

        if (stm_index === -1) return;

        if (plus_one) {
            stm = this.doc.sentences[++stm_index];
            if (!stm) return;  /* this was the last sentence */
        }

        if (stm.phase === Phases.ERROR) {
            // Do not clear the mark, to keep the error indicator.
            stm_index++;
        }

        for (let follow of this.doc.sentences.slice(stm_index)) {
            this.cancelled(follow);
        }

        // Clear dangling marks on comments
        while (stm_index > 1 && !this.doc.sentences[stm_index - 1].coq_sid) {
            this.cancelled(this.doc.sentences[--stm_index]);
        }

        this.doc.sentences.splice(stm_index);
    }

    // Error handler.
    handleError(sid, loc, msg) {

        let err_stm = this.doc.stm_id[sid];

        // The sentence has already vanished! This can happen for
        // instance if the execution of an erroneous sentence is
        // queued twice, which is hard to avoid due to STM exec
        // forcing on parsing.
        if(!err_stm) return;

        this.clearErrors();   // only display a single error at a time

        // Phases.ERROR will prevent the cancel handler from
        // clearing the mark.
        err_stm.phase = Phases.ERROR;
        this.error.push(err_stm);

        this.provider.mark(err_stm, 'error', loc);

        this.truncate(err_stm);
        this.coq.cancel(sid);
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

    clearErrors() {
        // Cancel all error sentences AND remove them from doc.sentences
        // (yes, it's a filter with side effects)
        this.doc.sentences = this.doc.sentences.filter(stm => {
            if (stm.phase === Phases.ERROR) {
                this.cancelled(stm);
                return false;
            }
            return true;
        });

        this.error = [];
        this.tidy();
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
        this.provider.retract();

        var dummy_sentence = this.doc.sentences[0];
        this.doc.sentences = [dummy_sentence];
        this.doc.stm_id = [, dummy_sentence];

        this.error = [];

        await this.coq.restart();

        // Reload packages and init
        var pkgs = this.packages.loaded_pkgs.slice();
        this.packages.reset();
        return this.packages.loadDeps(pkgs).then(() => this.coqInit());
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
        const goCursor  = () => this.goCursor(),
              goNext    = () => this.goNext(true),
              goPrev    = () => this.goPrev(true),
              toggle    = () => this.layout.toggle(),
              help      = () => this.layout.toggleHelp(),
              interrupt = () => this.interruptRequest();
        const nav_bindings = {
            '_Enter':     goCursor, '_NumpadEnter': goCursor,
            '^Enter':     goCursor, '^NumpadEnter': goCursor,
            '_ArrowDown': goNext,
            '_ArrowUp':   goPrev,
            'F8': toggle,
            'F1': help,
            'Escape': interrupt
        };
        if (!isMac) {
            Object.assign(nav_bindings, {
                '_KeyN': goNext,
                '_KeyP': goPrev
            }); /* Alt-N and Alt-P create accent characters on Mac */
        }

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

            var sp = this.provider.currentFocus || this.provider.snippets[0],
                op = file_bindings[key];
            if (sp && op) {
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
        if (this.options.focus) {
            this.provider.focus();
        }
    }

    // Disable the IDE.
    disable() {
        this.navEnabled = false;
        this.layout.toolbarOff();
        this.layout.systemNotification(
                "===> Waiting for package(s) to load.");
    }

    toolbarClickHandler(evt) {

        this.provider.focus();

        switch (evt.target.name) {
        case 'to-cursor' :
            this.goCursor();
            break;

        case 'up' :
            this.goPrev(true);
            break;

        case 'down' :
            this.goNext(true);
            break;

        case 'interrupt':
            this.interruptRequest();
            break;

        case 'reset':
            this.reset();
            break;
        }
    }

    updateGoals(html) {
        if (html) {
            this.layout.update_goals(html);
            this.pprint.adjustBreaks($(this.layout.proof));
            /* Notice: in Pp-formatted text, line breaks are handled by
             * FormatPrettyPrint rather than by the layout.
             */
        }
    }

    updateGoalsFor(stm) {
        var hgoals = this.doc.goals[stm.coq_sid];
        if (hgoals) {
            this.updateGoals(hgoals);
        }
        else if (stm.phase === Phases.PROCESSED) {
            // no goals fetched for current sentence, ask worker
            this.coq.goals(stm.coq_sid);
        }
        // otherwise: do nothing until this sentence is eventually executed,
        //   at which points its goals will be shown.
    }

    /**
     * Show the proof state for the latest non-error sentence.
     */
    refreshGoals() {
        var s = ArrayFuncs.findLast(this.doc.sentences, stm => stm.phase !== Phases.ERROR);
        if (s)
            this.updateGoalsFor(s);
    }

    editorActionHandler(action) {
        switch (action.type) {
        case 'share-hastebin':   this.actionShareHastebin(); break;
        case 'share-p2p':        this.actionShareP2P();      break;
        case 'share-gist':       this.actionShareGist();      break;
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

    async actionShareGist() {
        if (!this.collab) await this.openCollab();
        this.collab.gist.save();
    }

    /**
     * Process special comments that are used as directives to jsCoq itself.
     *
     * E.g.
     *   Comments "pkgs: space-delimited list of packages".
     *
     * Loads packages using the package manager and only then continues to
     * process the document.
     *
     * @param {string} text sentence text
     */
    process_special(text) {

        var special;

        if (special = text.match(/Comments \"(.*): (.+)\"./)) {
            let cmd  = special[1];
            let args = special[2];

            switch (cmd) {

            case 'pkgs':
                let pkgs = args.split(/\s+/);
                console.log('Requested pkgs: ', pkgs);

                this.packages.expand();
                this.disable();

                return this.packages.loadDeps(pkgs).then(pkgs => {
                    this.packages.collapse();
                    this.enable();
                    console.warn(pkgs);
                });

            default:
                console.log("Unrecognized jscoq command");
                return false;
            }
        }
        return false;
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

// enum
const Phases = {
    PENDING: 'pending',
    ADDING: 'adding',         ADDED: 'added',
    PROCESSING: 'processing', PROCESSED: 'processed',
    CANCELLING: 'cancelling',
    ERROR: 'error'
};

const PKG_ALIASES = {
    prelude: "Coq.Init.Prelude",
    utf8: "Coq.Unicode.Utf8"
};

const PKG_AFFILIATES = [  // Affiliated packages in @jscoq/@wacoq scope
    'mathcomp', 'elpi', 'equations', 'extlib', 'simpleio', 'quickchick',
    'software-foundations',
    'paco', 'snu-sflib',
    'fcsl-pcm', 'htt', 'pnp', 'coqoban', 'stdpp', 'iris'
];

// Local Variables:
// js-indent-level: 4
// End:
