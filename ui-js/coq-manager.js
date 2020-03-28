// The CoqManager class.
// Copyright (C) 2015-2017 Mines ParisTech/ARMINES
//
// CoqManager manages a document composed of several coq snippets,
// allowing the user to send/retract indivual coq sentences throu
// them. The Coq snippets can be provided by several sources, we just
// require them to be able to list parts and implement marks.
//

// XXX: use RequireJS or something like that.
"use strict";

// Extra stuff:

Array.prototype.last     = function() { return this[this.length-1]; };
Array.prototype.flatten  = function() { return [].concat.apply([], this); };
Array.prototype.findLast = function(p) { var r; for (let i = this.length; i > 0; )
                                                    if (p(r = this[--i])) return r; }
Array.prototype.equals   = function(other) {
    if (other === this) return true;
    if (!other || this.length != other.length) return false;
    for (var i = 0, l=this.length; i < l; i++) {
        let te = this[i], oe = other[i];
        if (!(te instanceof Array && oe instanceof Array ? te.equals(oe) : te == oe))
            return false;
    }
    return true;
}
Object.defineProperty(Array.prototype, "last",     {enumerable: false});
Object.defineProperty(Array.prototype, "flatten",  {enumerable: false});
Object.defineProperty(Array.prototype, "findLast", {enumerable: false});
Object.defineProperty(Array.prototype, "equals",   {enumerable: false});

if (typeof navigator !== 'undefined')
    navigator.isMac = /Mac/.test(navigator.platform);


/***********************************************************************/
/* A Provider Container aggregates several containers, the main deal   */
/* here is keeping track of focus, as the focused container can be     */
/* different from the "active" one                                     */
/***********************************************************************/
class ProviderContainer {

    constructor(elementRefs, options) {

        this.options = options ? options : {};

        // Code snippets.
        this.snippets = [];

        // Event handlers (to be overridden by CoqManager)
        this.onInvalidate = (mark) => {};
        this.onMouseEnter = (stm, ev) => {};
        this.onMouseLeave = (stm, ev) => {};
        this.onTipHover = (completion, zoom) => {};
        this.onTipOut = () => {};

        // Create sub-providers.
        //   Do this asynchronously to avoid locking the page when there is
        //   a large number of snippets.
        (async () => {
            for (let [idx, element] of this.findElements(elementRefs).entries()) {

                if (this.options.replace)
                    element = Deprettify.trim(element);

                // Init.
                let cm = new CmCoqProvider(element, this.options.editor, this.options.replace);
                cm.idx = idx;
                this.snippets.push(cm);

                // Track focus XXX (make generic)
                cm.editor.on('focus', ev => { this.currentFocus = cm; });

                // Track invalidate
                cm.onInvalidate = stm       => { this.onInvalidate(stm); };
                cm.onMouseEnter = (stm, ev) => { this.onMouseEnter(stm, ev); };
                cm.onMouseLeave = (stm, ev) => { this.onMouseLeave(stm, ev); };

                cm.onTipHover = (entity, zoom) => { this.onTipHover(entity, zoom); };
                cm.onTipOut   = ()             => { this.onTipOut(); }

                // Running line numbers
                if (this.options.line_numbers === 'continue') {
                    if (idx > 0) this.renumber(idx - 1);
                    cm.onResize = () => { this.renumber(idx); }
                }

                await this.yield();
            }
        })();
    }

    findElements(elementRefs) {
        var elements = [];
        for (let e of elementRefs) {
            var els = (typeof e === 'string') ? 
                [document.getElementById(e), ...document.querySelectorAll(e)] : e;
            els = els.filter(x => x);
            if (els.length === 0) {
                console.warn(`[jsCoq] element(s) not found: '${e}'`);
            }
            elements.push(...els);
        }
        return elements;
    }

    /**
     * Readjust line numbering flowing from one editor to the next.
     * @param {number} startIndex index where renumbering should start
     */
    async renumber(startIndex) {
        let snippet = this.snippets[startIndex],
            line = snippet.editor.getOption('firstLineNumber') + snippet.lineCount;

        for (let index = startIndex + 1; index < this.snippets.length; index++) {
            let snippet = this.snippets[index];
            snippet.editor.setOption('firstLineNumber', line);
            line += snippet.lineCount;
            await this.yield();
        }
    }

    yield() {
        return new Promise(resolve => setTimeout(resolve, 0));
    }

    // Get the next candidate and mark it.
    getNext(prev, until) {

        // If we have no previous element start with the first
        // snippet, else continue with the current one.
        var spr = prev ? prev.sp : this.snippets[0];

        if (until && this.snippets.indexOf(spr) > this.snippets.indexOf(until.sp))
            return null;

        var next = spr.getNext(prev, (until && until.sp === spr) ? until.pos : null);

        // We got a snippet!
        if (next) {
            next.sp = spr;
            return next;
        } else if (until && until.sp === spr) {
            return null;
        } else {
            // Try the next snippet.
            var idx = this.snippets.indexOf(spr);
            while (idx < this.snippets.length - 1) {
                spr  = this.snippets[idx+1];
                next = spr.getNext(null);
                if (next) {
                    next.sp = spr;
                    return next;
                } else {
                    idx = this.snippets.indexOf(spr);
                }
            } // while
            // No next snippet :( !
            return null;
        }
    }

    mark(stm, mark) {
        stm.sp.mark(stm, mark);
    }

    highlight(stm, flag) {
        stm.sp.highlight(stm, flag);
    }

    retract() {
        for (let sp of this.snippets) sp.retract();
    }

    // Focus and movement-related operations.

    // Get the point of the current focused element.
    getAtPoint() {
        return this.currentFocus.getAtPoint();
    }

    // Indicates if stm is after the point.
    // XXX: Improve
    afterPoint(stm) {

        var idx_point = this.snippets.indexOf(this.currentFocus);
        var idx_cur   = this.snippets.indexOf(stm.sp);

        return (idx_point < idx_cur);

    }

    getCursor() {
        return {sp: this.currentFocus,
                pos: this.currentFocus.getCursor()}
    }

    cursorToStart(stm) {
        stm.sp.cursorToStart(stm);
    }

    cursorToEnd(stm) {
        stm.sp.cursorToEnd(stm);
    }

    focus() {
        var sp = this.currentFocus || this.snippets[0];
        if (sp) sp.focus();
    }

    openFile(file) {
        var sp = this.currentFocus || this.snippets[0];
        if (sp) sp.openFile(file);
    }

}

/***********************************************************************/
/* CoqManager coordinates the coq code objects, the panel, and the coq */
/* js object.                                                          */
/*                                                                     */
/***********************************************************************/

var copyOptions = function(obj, target) {
    if (typeof obj !== 'object' || obj instanceof Array) return obj;
    if (typeof target !== 'object' || target instanceof Array) target = {};
    for (var prop in obj) {
        if (obj.hasOwnProperty(prop)) {
            target[prop] = copyOptions(obj[prop], target[prop]);
        }
    }
    return target;
}

class CoqManager {

    constructor(elems, options) {

        options = options ? options : {};

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
            pkg_path:    "../coq-pkgs/",  // this is awkward: package path is relative to the worker location (coq-js)
            implicit_libs: false,
            init_pkgs: ['init'],
            all_pkgs:  ['init', 'mathcomp',
                        'coq-base', 'coq-collections', 'coq-arith', 'coq-reals', 'elpi', 'equations',
                        'coquelicot', 'flocq', 'lf', 'plf', 'cpdt', 'color' ],
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
        this.provider = this.setupProvider(elems);

        // Setup the Panel UI.
        this.layout = new CoqLayoutClassic(this.options);
        this.layout.splash();
        this.layout.onAction = this.toolbarClickHandler.bind(this);

        this.layout.onToggle = ev => {
            if (ev.shown && !this.coq) this.launch();
            if (this.coq) this.layout.onToggle = () => {};
        };

        this.setupDragDrop();

        // Setup pretty printer for feedback and goals
        this.pprint = new FormatPrettyPrint();

        // Setup company-coq
        if (this.options.editor.mode && this.options.editor.mode['company-coq'])
            this.company_coq = new CodeMirror.CompanyCoq();

        // Keybindings setup
        // XXX: This should go in the panel init.
        document.addEventListener('keydown', evt => this.keyHandler(evt), true);
        $(document).on('keydown keyup', evt => this.modifierKeyHandler(evt));

        // This is a sid-based index of processed statements.
        this.doc = {
            fresh_id:           2,
            sentences:         [],
            stm_id:            [],
            goals:             []
        };

        // Initial sentence. (It's a hack.)
        let  dummyProvider = { mark : function() {},
                               getNext: function() { return null; },
                               focus: function() { return null; },
                               cursorToEnd: function() { return null; }
                             };
        this.doc.stm_id[1] = { text: "dummy sentence", coq_sid: 1, sp: dummyProvider, phase: Phases.PROCESSED };
        this.doc.sentences = [this.doc.stm_id[1]];

        this.error = [];
        this.navEnabled = false;

        // Launch time
        if (this.options.prelaunch)
            this.launch();

        if (this.options.show)
            requestAnimationFrame(() => this.layout.show());
    }

    // Provider setup
    setupProvider(elems) {

        var provider = new ProviderContainer(elems, this.options);

        provider.onInvalidate = stm => {

            if (stm.phase === Phases.ERROR) {
                this.clearErrors();
            }
            else if (stm.coq_sid) {
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
                this.updateGoals(this.doc.goals[this.doc.sentences.last().coq_sid]);
            }
        };

        provider.onMouseLeave = (stm, ev) => {
            this.updateGoals(this.doc.goals[this.doc.sentences.last().coq_sid]);
        };

        provider.onTipHover = (entry, zoom) => {
            var fullname = [...entry.prefix, entry.label].join('.');
            if (entry.kind == 'lemma')
                this.contextual_info.showCheck(fullname, /*opaque=*/true);
        };
        provider.onTipOut = () => { this.contextual_info.hide(); };

        return provider;
    }

    setupDragDrop() {
        $(this.layout.ide).on('dragover', (evt) => {
            evt.preventDefault();
        });
        $(this.layout.ide).on('drop', (evt) => {
            evt.preventDefault();
            // TODO better check file type and size before
            //  opening
            var file = evt.originalEvent.dataTransfer.files[0];
            if (file) {
                if (file.name.match(/[.](coq-pkg|zip)$/))
                    this.packages.dropPackage(file);
                else
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
            CodeMirror.CompanyCoq.loadSymbols(data, scope, /*replace_existing=*/false);
        })
        .fail((_, status, msg) => {
            console.warn(`Symbol resource unavailable: ${url} (${status}, ${msg})`)
        });
    }

    updateLocalSymbols() {
        this.coq.inspectPromise(0, ["CurrentFile"])
        .then(bunch => {
            CodeMirror.CompanyCoq.loadSymbols(
                { lemmas: bunch.map(fp => CoqIdentifier.ofFullPath(fp)) },
                'locals', /*replace_existing=*/true)
        });
    }

    /**
     * Starts a Worker and commences loading of packages and initialization
     * of STM.
     */
    async launch() {
        try {
            // Setup the Coq worker.
            this.coq           = new CoqWorker(this.options.base_path + 'coq-js/jscoq_worker.bc.js');
            this.coq.options   = this.options;
            this.coq.observers.push(this);

            await this.coq.when_created;
            this.coq.interruptSetup();

            // Setup package loader
            this.packages = new PackageManager(this.layout.packages,
                this.options.all_pkgs, {'+': this.options.pkg_path}, this.coq);
            
            this.packages.expand();

            // Setup autocomplete
            this.loadSymbolsFrom(this.options.base_path + 'ui-js/symbols/init.symb.json');
            this.loadSymbolsFrom(this.options.base_path + 'ui-js/symbols/coq-arith.symb.json');

            // Setup contextual info bar
            this.contextual_info = new CoqContextualInfo($(this.layout.proof).parent(),
                                                        this.coq, this.pprint, this.company_coq);

            // The fun starts: fetch package infos,
            // and load init packages once they are available
            this.packages.populate();

            await this.packages.loadDeps(this.options.init_pkgs);
            this.coqInit();
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
            item = this.layout.log(msg, 'Info');
        item.addClass('loading').data('mod', mod);
    }

    feedFileLoaded(sid, mod, file) {
        let item = [...this.layout.query.getElementsByClassName('loading')]
                    .findLast(x => $(x).data('mod') === mod),
            msg = `${mod} loaded.`;

        if (item)
            $(item).removeClass('loading').text(msg);
        else
            this.layout.log(msg, 'Info');
    }

    /**
     * Called when the first state is ready.
     */
    coqReady(sid) {
        this.layout.splash(this.version_info, "Coq worker is ready.", 'ready');
        this.enable();
    }

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
            if (nsid == this.doc.sentences.last().coq_sid) {
                this.coq.goals(nsid);
                this.updateLocalSymbols();
            }
        }

        this.work();
    }

    feedMessage(sid, lvl, loc, msg) {

        var fmsg = this.pprint.pp2DOM(msg);

        lvl = lvl[0];  // JSON encoding

        if(this.options.debug)
            console.log('Message', sid, lvl, fmsg);

        // Filter duplicate errors generated by Stm/Jscoq_worker
        if (lvl === 'Error' && this.error.some(stm => stm.coq_sid === sid && 
                                    stm.feedback.some(x => x.msg.equals(msg))))
            return;

        let stm = this.doc.stm_id[sid];
        if (stm) stm.feedback.push({level: lvl, loc: loc, msg: msg})

        var item = this.layout.log(fmsg, lvl, {'data-coq-sid': sid});
        this.pprint.adjustBreaks(item);

        // XXX: highlight error location.
        if (lvl === 'Error') {
            this.handleError(sid, loc, fmsg);
        }
    }

    // Coq Message processing.
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
        let ontop = this.doc.sentences[this.doc.sentences.indexOf(stm) - 1];

        let ontop_finished =    // assumes that exec is harmless if ontop was executed already...
            this.coq.execPromise(ontop.coq_sid);

        var pkg_deps = new Set();
        for (let module_name of module_names) {
            let binfo = this.packages.searchModule(prefix, module_name);
            if (binfo)
                for (let d of binfo.deps) pkg_deps.add(d);
        }

        for (let d of this.packages.loaded_pkgs) pkg_deps.delete(d);

        pkg_deps = [...pkg_deps.values()];

        var cleanup = () => {};

        if (pkg_deps.length > 0) {
            console.log("Pending: loading packages", pkg_deps);
            this.disable();
            this.packages.expand();
            cleanup = () => { this.packages.collapse(); this.enable(); }
        }

        this.packages.loadDeps(pkg_deps).then(() => ontop_finished)
            .then(() => {
                this.coq.reassureLoadPath(this.packages.getLoadPath());
                this.coq.resolve(ontop.coq_sid, nsid, stm.text);
                cleanup();
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

        this.refreshGoals();
    }

    coqGoalInfo(sid, goals) {

        if (goals) {

            var hgoals = this.pprint.goals2DOM(goals);

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

        let rmsg = this.pprint.pp2HTML(msg);

        level = level[0];

        if (this.options.debug) {
            if (level === 'Debug')
                console.debug(rmsg, level)
            else
                console.log(rmsg, level);
        }

        this.layout.log(rmsg, level);
    }

    coqLibInfo(bname, bi) {
        this.packages.addBundleInfo(bname, bi);
    }

    coqLibProgress(evt) {
        this.packages.onPkgProgress(evt);
    }

    coqLibLoaded(bname) {
        this.packages.onBundleLoad(bname);
    }

    coqCoqExn(loc, sids, msg) {
        console.error('Coq Exception', msg);

        // If error has already been reported by Feedback, bail
        if (this.error.some(stm => stm.feedback.some(x => x.msg.equals(msg))))
            return;

        var rmsg = this.pprint.pp2HTML(msg);
        this.layout.log(rmsg, 'Error');
    }

    coqJsonExn(msg) {
        // this.layout.log(msg, "Error");
        console.error('jsonExn', msg);
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
            "===> JsCoq filesystem initialized successfully!\n" +
            `===> Loaded packages [${this.options.init_pkgs.join(', ')}]`);

        // Set startup parameters
        let init_opts = {implicit_libs: this.options.implicit_libs, stm_debug: false,
                         coq_options: this._parseOptions(this.options.coq || {})},
            load_path = this.packages.getLoadPath(),
            load_lib = this.options.prelude ? [PKG_ALIASES.prelude] : [];

        for (let pkg of this.options.init_import || []) {
            load_lib.push(PKG_ALIASES[pkg] || pkg.split('.'));
        }

        this.coq.init(init_opts, load_lib, load_path);
        // Almost done!
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

    goPrev(update_focus) {

        // There may be cases where there is more than one sentence with
        // an error, but then we probably want to retract all of them anyway.
        if (this.error.length > 0) {
            this.clearErrors();
            return true;
        }

        // Prevent canceling the init state
        if (this.doc.sentences.length <= 1) { return false; }

        var last_stm = this.doc.sentences.pop();
        this.cancel(last_stm);

        if(update_focus) this.focus(this.doc.sentences.last());

        return true;
    }

    // Return if we had success.
    goNext(update_focus, until) {

        this.clearErrors();

        let last_stm = this.doc.sentences.last(),
            next_stm = this.provider.getNext(last_stm, until);

        // We have reached the end
        if(!next_stm) { return false; }

        next_stm.phase = Phases.PENDING;
        this.doc.sentences.push(next_stm);

        this.provider.mark(next_stm, 'processing');

        if(update_focus) this.focus(next_stm);

        this.work();

        return true;
    }

    goCursor() {

        this.clearErrors();

        var cur = this.provider.getAtPoint();

        if (cur) {
            if (cur.coq_sid) {
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
        var tip = null, latest_ready_stm = null;

        for (let stm of this.doc.sentences) {
            switch (stm.phase) {
            case Phases.PROCESSED:
                tip = stm.coq_sid; break;
            case Phases.ADDED:
                latest_ready_stm = stm;
                tip = stm.coq_sid;
                break; // only actually execute if nothing else remains to add
            case Phases.ADDING:
            case Phases.PROCESSING:
                return;  // still waiting for worker; can't make progress
            case Phases.PENDING:
                if (!tip) throw new Error('internal error'); // inconsistent
                this.add(stm, tip);
                return;
            }
        }

        // TODO Don't queue too many sentences at once in order to avoid
        //   stack overflow in Stm
        if (latest_ready_stm) {
            latest_ready_stm.phase = Phases.PROCESSING;
            this.coq.exec(latest_ready_stm.coq_sid);
        }
    }

    async add(stm, tip) {
        stm.phase = Phases.ADDING;

        await this.process_special(stm.text);

        stm.coq_sid = this.doc.fresh_id++;
        this.doc.stm_id[stm.coq_sid] = stm;
        this.coq.add(tip, stm.coq_sid, stm.text);

        this.provider.mark(stm, 'processing');  // in case it was un-marked
    }

    cancel(stm) {
        switch (stm.phase) {
        case Phases.ADDING:
        case Phases.ADDED:
        case Phases.PROCESSING:
        case Phases.PROCESSED:
            this.coq.cancel(stm.coq_sid);
            break;
        }

        this.cancelled(stm);
    }

    cancelled(stm) {
        delete this.doc.stm_id[stm.coq_sid];
        delete stm.coq_sid;

        this.provider.mark(stm, 'clear');
    }
    
    /**
     * Removes all the sentences from stm to the end of the document.
     * If stm as an error sentence, leave the sentence itself (so that the
     * error mark remains visible), and remove all following sentences.
     */
    truncate(stm) {
        let stm_index = this.doc.sentences.indexOf(stm);

        if (stm.phase === Phases.ERROR) {
            // Do not clear the mark, to keep the error indicator.
            stm_index++;
        }
        
        for (let follow of this.doc.sentences.slice(stm_index)) {
            this.cancelled(follow);
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

        this.provider.mark(err_stm, 'error');

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
                this.cancel(stm);
                return false;
            }
            return true;
        });

        this.error = [];
    }

    /**
     * Drops all the state and re-launches the worker.
     * Loaded packages are reloaded (but obviously not Require'd) by the
     * package manager.
     * @returns {Promise} resolves after 'init' command has been issued.
     */
    reset() {
        this.layout.update_goals($('<b>').text('Coq worker reset.'));
        this.disable();
        this.provider.retract();

        var dummy_sentence = this.doc.sentences[0];
        this.doc.sentences = [dummy_sentence];
        this.doc.stm_id = [, dummy_sentence];

        this.error = [];

        this.coq.restart();

        // Reload packages and init
        var pkgs = this.packages.loaded_pkgs.slice();
        this.packages.reset();
        return this.packages.loadDeps(pkgs).then(() => this.coqInit());
    }

    /**
     * Key bindings event handler.
     * @param {KeyboardEvent} e a keydown event
     */
    keyHandler(e) {

        // Poor-man's keymap
        let key = ((navigator.isMac ? e.metaKey : e.ctrlKey) ? '^' : '') + 
                  (e.altKey ? '_' : '') + (e.shiftKey ? '+' : '') + e.code;

        // Navigation keybindings
        const goCursor  = () => this.goCursor(),
              goNext    = () => this.goNext(true),
              goPrev    = () => this.goPrev(true),
              toggle    = () => this.layout.toggle(),
              interrupt = () => this.interruptRequest();
        const nav_bindings = {
            '_Enter':     goCursor, '_ArrowRight': goCursor,
            '_ArrowDown': goNext,
            '_ArrowUp':   goPrev,
            'F8': toggle,
            'Escape': interrupt
        };
        if (!navigator.isMac) {
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
        var s = this.doc.sentences.findLast(stm => stm.phase !== Phases.ERROR);
        if (s)
            this.updateGoalsFor(s);
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
    
                return this.packages.loadDeps(pkgs).then(() => {
                    this.packages.collapse(); 
                    this.enable();
                });

            default:
                console.log("Unrecognized jscoq command");
                return false;
            }
        }
        return false;
    }
}


// enum
const Phases = {
    PENDING: 'pending',
    ADDING: 'adding',         ADDED: 'added',
    PROCESSING: 'processing', PROCESSED: 'processed',
    ERROR: 'error'
};

const PKG_ALIASES = {
    prelude: ["Coq", "Init", "Prelude"],
    utf8: ["Coq", "Unicode", "Utf8"]
}


class CoqContextualInfo {
    /**
     * @param {jQuery} container <div> element to show info in
     * @param {CoqWorker} coq jsCoq worker for querying types and definitions
     * @param {FormatPrettyPrint} pprint formatter for Pp data
     * @param {CompanyCoq} company_coq (optional) further beautification
     */
    constructor(container, coq, pprint, company_coq) {
        this.container = container;
        this.coq = coq;
        this.pprint = pprint;
        this.company_coq = company_coq;
        this.el = $('<div>').addClass('contextual-info').hide();
        this.is_visible = false;
        this.is_sticky = false;
        this.focus = null;
        this.minimal_exposure = Promise.resolve();

        this.MINIMAL_EXPOSURE_DURATION = 150; // ms

        this.container.append(this.el);

        // Set up mouse events
        var r = String.raw,
            sel = r`.constr\.reference, .constr\.variable, .constr\.type, .constr\.notation`;

        this.contextual_sel = sel;

        container.on('mouseenter', sel,  evt => this.onMouseEnter(evt));
        container.on('mousedown',  sel,  evt => this.onMouseDown(evt, true));
        container.on('mouseleave', sel,  evt => this.onMouseLeave(evt));
        container.on('mouseleave',       evt => this.onMouseLeave(evt));
        container.on('mousedown',        evt => this.hideReq());

        this.el.on('mouseenter',         evt => this.hideCancel());
        this.el.on('mousedown',          evt => { this.hideReq(); evt.stopPropagation(); });
        this.el.on('mouseover mouseout', evt => { evt.stopPropagation(); });

        this._keyHandler = this.keyHandler.bind(this);
        this._key_bound = false;
    }

    onMouseEnter(evt) { if (!this.is_sticky) this.showFor(evt.target, evt.altKey); }
    onMouseLeave(evt) { if (!this.is_sticky) this.hideReq(); }

    onMouseDown(evt)  {
        this.showFor(evt.target, evt.altKey);
        this.stick(evt.target);
        this.is_sticky = true;
        evt.stopPropagation();
    }

    showFor(dom, alt) {
        var jdom = $(dom), name = jdom.attr('data-name') || jdom.text();
        if (jdom.hasClass('constr.variable') ||
            jdom.hasClass('constr.type') || jdom.hasClass('constr.reference')) {
            if (alt) this.showPrint(name);
            else     this.showCheck(name, /*opaque*/false, /*silent_fail*/true);
        }
        else if (jdom.hasClass('constr.notation')) {
            this.showLocate(name);
        }
    }

    showCheck(name, opaque=false, silent_fail=false) {
        this.focus = {identifier: name, info: 'Check', opaque};
        this.showQuery(`Check ${name}.`, silent_fail ? null : this.formatName(name));
    }

    showPrint(name) {
        this.focus = {identifier: name, info: 'Print'};
        this.showQuery(`Print ${name}.`, this.formatName(name));
    }

    showLocate(symbol) {
        this.focus = {symbol: symbol, info: 'Locate'};
        this.showQuery(`Locate "${symbol}".`, `"${symbol}"`);
    }

    showQuery(query, title) {
        this.is_visible = true;
        this.coq.queryPromise(0, query).then(result => {
            if (this.is_visible)
                this.show(this.formatMessages(result));
        })
        .catch(err => {
            if (title)
                this.show(this.formatText(title, "(not available)"));
        });
    }

    show(html) {
        this.el.html(html);
        this.el.show();
        this.is_visible = true;
        this.minimal_exposure = this.elapse(this.MINIMAL_EXPOSURE_DURATION);
        if (!this._key_bound) {
            this._key_bound = true;
            $(document).on('keydown keyup', this._keyHandler);
        }
    }

    hide() {
        this.unstick();
        this.el.hide();
        this.is_visible = false;
        this.is_sticky = false;
        $(document).off('keydown keyup', this._keyHandler);
        this._key_bound = false;
    }

    hideReq() {
        this.request_hide = true;
        this.minimal_exposure.then(() => { if (this.request_hide) this.hide() });
    }

    hideCancel() {
        this.request_hide = false;
    }

    stick(dom) {
        this.unstick();
        $(dom).addClass('contextual-focus');        
    }

    unstick() {
        this.container.find('.contextual-focus').removeClass('contextual-focus');        
    }

    /**
     * Stores current identifier names, esp. before
     * prettifying text with company-coq.
     */
    pinIdentifiers(jdom) {
        if (!jdom) jdom = this.container;
        for (let el of jdom.find(this.contextual_sel)) {
            $(el).attr('data-name', $(el).text());
        }
    }

    keyHandler(evt) {
        var name = this.focus.identifier;
        if (name && !this.focus.opaque) {
            if (evt.altKey) this.showPrint(name);
            else            this.showCheck(name);
        }
    }

    formatMessages(msgs) {
        var ppmsgs = msgs.map(feedback => this.pprint.pp2DOM(feedback.msg)),
            frag = $(document.createDocumentFragment());

        for (let e of ppmsgs) {
            if (frag.children().length > 0) frag.append($('<hr/>'));
            frag.append(e);
        }

        if (this.company_coq) {
            this.company_coq.markup.applyToDOM(frag[0]);
        }

        return frag;
    }

    formatName(name) {
        var comps = name.split('.'),
            span = $('<span>');
        for (let path_el of comps.slice(0, comps.length - 1)) {
            span.append($('<span>').addClass('constr.path').text(path_el));
            span.append(document.createTextNode('.'));
        }
        span.append($('<span>').addClass('constr.reference').text(comps.last()));
        return span;
    }

    formatText(title, msg) {
        return $('<div>')
            .append(typeof title === 'string' ? $('<span>').text(title) : title)
            .append($('<br/>'))
            .append($('<span>').addClass('message').text("  " + msg));
    }

    elapse(duration) {
        return new Promise((resolve, reject) =>
            setTimeout(resolve, duration));
    }
}


class CoqIdentifier {
    constructor(prefix, label) {
        this.prefix = prefix;
        this.label = label;
    }

    toString() { return [...this.prefix, this.label].join('.'); }

    equals(other) {
        return other instanceof CoqIdentifier &&
            this.prefix.equals(other.prefix) && this.label === other.label;
    }

    /**
     * Constructs an identifier from a Coq Names.KerName.t.
     * @param {array} param0 serialized form of KerName.
     */
    static ofKerName([kername, modpath, label]) {
        /**/ console.assert(kername === 'KerName') /**/
        var modsuff = [];
        while (modpath[0] == 'MPdot') {
            modsuff.push(modpath[2]);
            modpath = modpath[1];
        }
        /**/ console.assert(modpath[0] === 'MPfile'); /**/
        /**/ console.assert(modpath[1][0] === 'DirPath'); /**/
        return new CoqIdentifier(
            modpath[1][1].slice().reverse().map(this._idToString).concat(modsuff),
            this._idToString(label));
    }

    /**
     * Constructs an identifier from a Libnames.full_path.
     * @param {array} fp serialized form of full_path (from SearchResults).
     */
    static ofFullPath(fp) {
        /**/ console.assert(fp.dirpath[0] === 'DirPath') /**/
        return new CoqIdentifier(
            fp.dirpath[1].slice().reverse().map(this._idToString),
            this._idToString(fp.basename));
    }

    static _idToString(id) {
        /**/ console.assert(id[0] === 'Id') /**/
        return id[1];
    }

    dequalify(dirpaths) {
        for (let prefix of dirpaths) {
            if (this.prefix.slice(0, prefix.length).equals(prefix))
                return this.ltrunc(prefix.length)
        }
        return this;
    }

    ltrunc(n) {
        var d = new CoqIdentifier(this.prefix.slice(n), this.label);
        d.tags = this.tags;
        return d;
    }
  
}

if (typeof module !== 'undefined')
    module.exports = {CoqManager, CoqIdentifier}

// Local Variables:
// js-indent-level: 4
// End:
