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


/***********************************************************************/
/* A Provider Container aggregates several containers, the main deal   */
/* here is keeping track of focus, as the focused container can be     */
/* different from the "active" one                                     */
/***********************************************************************/
class ProviderContainer {

    constructor(elms, options) {

        this.options = options ? options : {};

        // Code snippets.
        this.snippets = [];

        // Debug variables
        var idx = 0;

        // Event handlers (to be overridden by CoqManager)
        this.onInvalidate = (mark) => {};
        this.onMouseEnter = (stm, ev) => {};
        this.onMouseLeave = (stm, ev) => {};
        this.onTipHover = (completion, zoom) => {};
        this.onTipOut = () => {};

        // for (e of elms) not very covenient here due to the closure.
        elms.forEach(e => {

            // Init.
            var cm = new CmCoqProvider(e, this.options.editor);
            cm.idx = idx++;
            this.snippets.push(cm);

            // Track focus XXX (make generic)
            cm.editor.on('focus', evt => { this.currentFocus = cm; });

            // Track invalidate
            cm.onInvalidate = stm       => { this.onInvalidate(stm); };
            cm.onMouseEnter = (stm, ev) => { this.onMouseEnter(stm, ev); };
            cm.onMouseLeave = (stm, ev) => { this.onMouseLeave(stm, ev); };

            cm.onTipHover = (entity, zoom) => { this.onTipHover(entity, zoom); };
            cm.onTipOut   = ()             => { this.onTipOut(); }
        });
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
            prelude: true,
            debug:   true,
            wrapper_id: 'ide-wrapper',
            base_path:  "./",
            pkg_path: "../coq-pkgs/",  // this is awkward: package path is relative to the worker location (coq-js)
            implicit_libs: false,
            init_pkgs: ['init'],
            all_pkgs:  ['init', 'math-comp',
                        'coq-base', 'coq-collections', 'coq-arith', 'coq-reals', 'elpi', 'equations', 'ltac2',
                        'coquelicot', 'flocq', 'sf', 'cpdt', 'color' ],
            editor: { /* codemirror options */ }
            // Disabled on 8.6
            // 'coquelicot', 'flocq', 'tlc', 'sf', 'cpdt', 'color', 'relalg', 'unimath',
            // 'plugin-utils', 'extlib', 'mirrorcore']
        };

        this.options = copyOptions(options, this.options);

        // Setup the Coq statement provider.
        this.provider = this.setupProvider(elems);

        // Setup the Panel UI.
        this.layout = new CoqLayoutClassic(this.options);
        this.layout.onAction = this.toolbarClickHandler.bind(this);

        this.setupDragDrop();

        // Setup the Coq worker.
        this.coq           = new CoqWorker(this.options.base_path + 'coq-js/jscoq_worker.bc.js');
        this.coq.options   = this.options;
        this.coq.observers.push(this);

        // Setup pretty printer for feedback and goals
        this.pprint = new FormatPrettyPrint();

        // Setup contextual info bar
        this.contextual_info = new CoqContextualInfo($(this.layout.proof).parent(),
                                                     this.coq, this.pprint);

        // Setup company-coq
        if (this.options.editor.mode && this.options.editor.mode['company-coq'])
            this.company_coq = new CodeMirror.CompanyCoq();

        // Setup autocomplete
        this.loadSymbolsFrom(this.options.base_path + 'ui-js/symbols/init.symb.json');
        this.loadSymbolsFrom(this.options.base_path + 'ui-js/symbols/coq-arith.symb.json');

        // Keybindings setup
        // XXX: This should go in the panel init.
        document.addEventListener('keydown', evt => this.keyHandler(evt), true);

        // Panel setup 2: packages panel.
        // XXX: In the future this may also manage the downloads.
        this.packages = new PackageManager(this.layout.packages, this.options.pkg_path,
                                           this.options.all_pkgs,
                                           this.coq);

        // Display packages panel:
        this.packages.expand();

        requestAnimationFrame(() => this.layout.show());

        // This is a sid-based index of processed statements.
        this.doc = {
            number_adds:        0,
            sentences:         [],
            stm_id:            [],
            goals:             []
        };

        // XXX: Initial sentence == hack
        let  dummyProvider = { mark : function() {},
                               getNext: function() { return null; },
                               focus: function() { return null; }
                             };
        this.doc.stm_id[1] = { text: "dummy sentence", coq_sid: 1, sp: dummyProvider, executed: true };
        this.doc.sentences = [this.doc.stm_id[1]];

        this.error = [];
        this.goTarget = null;
        this.navEnabled = false;

        // XXX: Hack
        this.waitForPkgs = [];

        // The fun starts: Load the set of packages.
        this.coq.infoPkg(this.packages.pkg_root_path, this.options.all_pkgs);
    }

    // Provider setup
    setupProvider(elems) {

        var provider = new ProviderContainer(elems, this.options);

        provider.onInvalidate = stm => {

            // If we have an error mark we need to clear it.
            let stm_err_idx = this.error.indexOf(stm);

            if (stm_err_idx >= 0) {
                provider.mark(stm, "clear");
                this.error.splice(stm_err_idx, 1);
                return;
            }
            else if (stm.coq_sid) {
                this.coq.cancel(stm.coq_sid);
            }
        };

        provider.onMouseEnter = (stm, ev) => {
            if (stm.coq_sid && ev.altKey) {
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
            if (file)
                this.provider.openFile(file);
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
                { lemmas: bunch.map(CoqIdentifier.ofKerName) },
                'locals', /*replace_existing=*/true)
        });
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

    // The first state is ready.
    coqReady(sid) {

        this.layout.proof.append(document.createTextNode(
            "\nCoq worker is ready with sid = " + sid.toString() + "\n"));
            /* init libraries have already been loaded by now */

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

        if (!stm.executed) {
            stm.executed = true;
            this.provider.mark(stm, "ok");

            // Get goals and active definitions
            if (nsid == this.doc.sentences.last().coq_sid) {
                this.coq.goals(nsid);
                this.updateLocalSymbols();
            }
        }
    }

    feedMessage(sid, lvl, loc, msg) {

        var fmsg = this.pprint.pp2HTML(msg);

        lvl = lvl[0];  // JSON encoding

        if(this.options.debug)
            console.log('Message', sid, lvl, fmsg);

        let stm = this.doc.stm_id[sid];
        if (stm) stm.feedback.push({level: lvl, loc: loc, msg: msg})

        // XXX: highlight error location.
        if (lvl === 'Error') {
            this.handleError(sid, loc, fmsg);
        } else {
            this.layout.log(fmsg, lvl, {'data-coq-sid': sid});
        }
    }

    // Coq Message processing.
    coqAdded(nsid,loc) {

        if(this.options.debug)
            console.log('adding: ', nsid, loc);

        // XXX Rewrite, the sentence could have vanished...
        let cur_stm = this.doc.stm_id[nsid], exec = false;

        if (this.goTarget) {
            exec = !this.goNext(false, this.goTarget);
            if (exec)
                this.goTarget = null;
        } else {
            exec = true;
        }

        if (exec && !cur_stm.executed) {
            this.coq.exec(nsid);
        }
    }

    // Gets a request to load packages
    coqPending(nsid, prefix, module_names) {
        let stm = this.doc.stm_id[nsid];
        let ontop = this.doc.sentences[this.doc.sentences.indexOf(stm) - 1];

        let ontop_finished =    // assumes that exec is harmless if ontop was executed already...
            this.coq.execPromise(ontop.coq_sid);

        // Collect package dependencies
        var pkg_deps = new Set();
        for (let module_name of module_names) {
            let binfo = this.packages.searchModule(prefix, module_name);
            if (binfo)
                for (let d of binfo.deps) pkg_deps.add(d);
        }

        for (let d of this.packages.loaded_pkgs) pkd_deps.delete(d);

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

        sids.forEach(function (sid) {

            let stm_to_cancel = this.doc.stm_id[sid];
            let stm_err_idx   = this.error.indexOf(stm_to_cancel);

            if (stm_err_idx >= 0) {
                // Do not clear the mark, to keep the error indicator.
            } else {
                let stm_idx = this.doc.sentences.indexOf(stm_to_cancel);

                // Not already cancelled.
                if (stm_idx >= 0) {

                    this.doc.stm_id[sid] = null;
                    this.doc.goals[sid]  = null;
                    stm_to_cancel.coq_sid = null;

                    this.doc.sentences.splice(stm_idx, 1);

                    this.provider.mark(stm_to_cancel, "clear");
                }
            }

        }, this);

        // Update goals
        var stm = this.doc.sentences.last(),
            hgoals = this.doc.goals[stm.coq_sid];
        if (hgoals) {
            this.updateGoals(hgoals);
        }
        else if (stm.executed) {
            this.coq.goals(stm.coq_sid); // no goals fetched for current statement, ask worker
        }
    }

    coqGoalInfo(sid, goals) {

        if (goals) {
            var hgoals = this.pprint.pp2HTML(goals);
            this.doc.goals[sid] = hgoals;

            // XXX optimize!
            // if(!this.goTarget)
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

        var wait_pkgs = this.waitForPkgs,
            loaded_pkgs = this.packages.loaded_pkgs;

        if (wait_pkgs.length > 0) {
            if (wait_pkgs.every(x => loaded_pkgs.indexOf(x) > -1)) {
                this.enable();
                this.packages.collapse();
                this.waitForPkgs = [];
            }
        }
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

        this.layout.proof.textContent = info;

        var pkgs = this.options.init_pkgs;

        if (pkgs.length > 0)
            this.layout.proof.textContent +=
                  "\nPlease wait for the libraries to load, thanks!"
                + "\n(If you are having trouble, try cleaning your browser's cache.)\n";

        this.packages.waitFor(pkgs)
        .then(() => this.packages.loadDeps(pkgs))
        .then(() => { this.coqInit(); });
    }

    // Coq Init: At this point, the required libraries are loaded
    // and Coq is ready to be used.
    coqInit() {

        this.packages.collapse();

        this.layout.proof.append(document.createTextNode(
            "\n===> JsCoq filesystem initialized successfully!\n" +
            "===> Loaded packages [" + this.options.init_pkgs.join(', ') + "] \n"));

        // XXXXXX: Critical point
        var load_lib = [];

        if (this.options.prelude) {
            load_lib.push(["Coq", "Init", "Prelude"]);
        }

        let set_opts = {implicit_libs: this.options.implicit_libs, stm_debug: false},
            load_path = this.packages.getLoadPath();

        this.coq.init(set_opts, load_lib, load_path);
        // Almost done!
    }

    goPrev(update_focus) {

        // XXX: Optimization, in case of error, but incorrect in the
        // new general framework.
        if (this.error.length > 0) {
            this.provider.mark(this.error.pop(), "clear");
            return;
        }

        if (this.goTarget) return;

        // If we didn't load the prelude, prevent unloading it to
        // workaround a bug in Coq.
        if (this.doc.sentences.length <= 1) return;

        var cur_stm  = this.doc.sentences.last();
        var prev_stm = this.doc.sentences[this.doc.sentences.length - 2];

        if(update_focus && prev_stm) {
            this.currentFocus = prev_stm.sp;
            this.currentFocus.focus();
            this.provider.cursorToStart(cur_stm);
        }

        // Cancel the sentence
        let stm_idx       = this.doc.sentences.indexOf(cur_stm);
        this.doc.sentences.splice(stm_idx, 1);

        this.doc.stm_id[cur_stm.coq_sid] = null;
        this.doc.goals[cur_stm.coq_sid]  = null;
        this.provider.mark(cur_stm, "clear");
        this.coq.cancel(cur_stm.coq_sid);
        cur_stm.coq_sid = null;
    }

    // Return if we had success.
    goNext(update_focus, until) {

        if (this.goTarget && !until) return false;

        this.clearErrors();

        let cur_stm = this.doc.sentences.last();
        let cur_sid = cur_stm.coq_sid;

        let next_stm = this.provider.getNext(cur_stm, until);

        // We are the the end
        if(!next_stm) { return false; }

        let next_sid = cur_sid+1;
        next_stm.coq_sid = next_sid;
        next_stm.executed = false;

        this.doc.sentences.push(next_stm);
        this.doc.stm_id[next_sid] = next_stm;

        // XXX: Hack to avoid sending comments. Is this still valid?
        if(next_stm.is_comment) {
            this.provider.mark(next_stm, "ok");
            return true;
        } else {
            this.provider.mark(next_stm, "processing");
        }

        // We focus the new snippet.
        if(update_focus) {
            this.currentFocus = next_stm.sp;
            this.currentFocus.focus();
            this.provider.cursorToEnd(next_stm);
        }

        // process special jscoq commands, for now:
        // Comment "pkg: list" will load packages.
        this.process_special(next_stm.text);
        this.coq.add(cur_sid, next_sid, next_stm.text);

        // Avoid stack overflows by doing a commit every 24
        // sentences, due to the STM co-tail recursive traversal bug?
        let so_threshold = 24;
        if( (++this.doc.number_adds % so_threshold) === 0 )
            this.coq.exec(next_sid);

        return true;
    }

    goCursor() {

        var cur = this.provider.getAtPoint();

        if (cur) {
            if (cur.coq_sid) {
                this.coq.cancel(cur.coq_sid);
            }
            else {
                console.warn("in goCursor(): stm not registered");
            }
        } else {
            this.goTarget = this.provider.getCursor();
            this.goNext(false, this.goTarget);
        }
    }

    // Error handler.
    handleError(sid, loc, msg) {

        this.goTarget = null;  // first of all, stop any pending additions

        let err_stm = this.doc.stm_id[sid];

        // The sentence has already vanished! This can happen for
        // instance if the execution of an erroneous sentence is
        // queued twice, which is hard to avoid due to STM exec
        // forcing on parsing.
        if(!err_stm) return;

        this.layout.log(msg, 'Error');

        // this.error will prevent the cancel handler from
        // clearing the mark.
        this.error.push(err_stm);

        let stm_idx       = this.doc.sentences.indexOf(err_stm);

        // The stm was not deleted!
        if (stm_idx >= 0) {
            this.doc.sentences.splice(stm_idx, 1);

            this.doc.stm_id[sid] = null;
            this.doc.goals[sid]  = null;
            err_stm.coq_sid = null;

            this.provider.mark(err_stm, "error");

            this.coq.cancel(sid);
        }
    }

    clearErrors() {
        for (let err of this.error) {
            this.provider.mark(err, "clear");
        }
        this.error = [];
    }

    // Drops all the state!
    reset() {

        // Reset out sentences
        this.doc.sentences.forEach(function(stm) {
            this.provider.mark(stm, "clear");
        }, this);

        // this.doc.sentences = [];
        // XXX Kill worker
    }

    // Keyboard handling
    keyHandler(e) {

        if (e.keyCode === 119) // F8
            this.layout.toggle();

        // All other keybindings are prefixed by alt.
        if (!e.altKey) return true;

        // When navigation is disabled, suppress keystrokes
        if (!this.navEnabled && [13, 39, 78, 40, 80, 38].indexOf(e.keyCode) > -1) {
            e.preventDefault();
            e.stopPropagation();
            return true;
        }

        switch (e.keyCode) {
            case 13: // ENTER
            case 39: // Right arrow
                this.goCursor();
                e.preventDefault();
                e.stopPropagation();
                break;
            case 78: // N
            case 40: // Down arrow
                this.goNext(true);
                e.preventDefault();
                break;
            case 80: // P
            case 38: // Up arrow
                this.goPrev(true);
                e.preventDefault();
                break;
        }
    }

    // Enable the IDE.
    enable() {
        this.navEnabled = true;
        this.layout.toolbarOn();
        this.provider.focus();
    }

    // Disable the IDE.
    disable() {
        this.navEnabled = false;
        this.layout.toolbarOff();
        this.layout.proof.append(document.createTextNode(
                "\n===> Waiting for Package load!\n"));
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
        }
    }

    updateGoals(html) {
        if (html) {
            this.layout.update_goals(html);
            if (this.company_coq) {
                this.contextual_info.pinIdentifiers();
                this.company_coq.markup.applyToDOM(this.layout.proof);
            }
            this.pprint.adjustBreaks($(this.layout.proof));
            /* Notice: in Pp-formatted text, line breaks are handled by
             * FormatPrettyPrint rather than by the layout.
             */
        }
    }

    process_special(text) {

        var special;

        if (special = text.match(/Comments \"(.*): (.+)\"./)) {
            let cmd  = special[1];
            let args = special[2];

            switch (cmd) {

            case 'pkgs':
                let pkgs = args.split(' ');
                console.log('Requested pkgs '); console.log(pkgs);

                this.packages.expand();

                this.disable();
                this.waitForPkgs = pkgs;

                for (let pkg of pkgs) {
                    this.packages.startPackageDownload(pkg);
                }

                return true;

            default:
                console.log("Unrecognized jscoq command");
                return false;
            }
        }
        return false;
    }
}


class CoqContextualInfo {
    /**
     * @param {jQuery} container <div> element to show info in
     * @param {CoqWorker} coq jsCoq worker for querying types and definitions
     * @param {FormatPrettyPrint} pprint formatter for Pp data
     */
    constructor(container, coq, pprint) {
        this.container = container;
        this.coq = coq;
        this.pprint = pprint;
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
        this.container.find('.contextual-focus').removeClass('contextual-focus');
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
        return msgs.map(feedback => this.pprint.pp2HTML(feedback.msg)).join("<hr/>");
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

    /**
     * Constructs an identifier from a Coq Names.KerName.t.
     * @param {array} param0 serialized form of KerName (from SearchResults).
     */
    static ofKerName([kername, modpath, dirpath, label]) {
        /**/ console.assert(kername === 'KerName') /**/
        var modsuff = [];
        while (modpath[0] == 'MPdot') {
            modsuff.push(modpath[2]);
            modpath = modpath[1];
        }
        /**/ console.assert(modpath[0] === 'MPfile'); /**/
        return new CoqIdentifier(modpath[1].slice().reverse().concat(modsuff), label);
    }
}

if (typeof module !== 'undefined')
    module.exports = {CoqManager, CoqIdentifier}

// Local Variables:
// js-indent-level: 4
// End:
