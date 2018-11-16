// The CoqManager (& CoqPanel) class.
// (c) 2015-2016 Mines ParisTech/ARMINES
//
// CoqManager manages a document composed of several coq snippets,
// allowing the user to send/retract indivual coq sentences throu
// them. The Coq snippets can be provided by several sources, we just
// require them to be able to list parts and implement marks.
//

// XXX: use RequireJS or something like that.
"use strict";

var COQ_LOG_LEVELS = {
    DEBUG : 'debug',
    INFO  : 'info',
    WARN  : 'warn',
    ERROR : 'error'
};

// Extra stuff... we better use jQuery.

Array.prototype.last = function() { return this[this.length-1]; };
String.prototype.trim = function() {
  return this.replace(/^\s+|\s+$/g, "");
};

/***********************************************************************/
/* A Provider Container aggregates several containers, the main deal   */
/* here is keeping track of focus, as the focused container can be     */
/* different from the "active" one                                     */
/***********************************************************************/

class ProviderContainer {

    constructor(elms) {

        // Code snippets.
        this.snippets = [];

        // Debug variables
        var idx = 0;

        // for (e of elms) not very covenient here due to the closure.
        elms.forEach(function (e) {

            // Init.
            var cm = new CmCoqProvider(e);
            cm.idx = idx++;
            this.snippets.push(cm);

            // Track focus XXX (make generic)
            cm.editor.on('focus', evt => { this.currentFocus = cm; });

            // Track invalidate
            cm.onInvalidate = smt => { this.onInvalidate(smt); };
            cm.onMouseEnter = smt => { this.onMouseEnter(smt); };
            cm.onMouseLeave = smt => { this.onMouseLeave(smt); };

            // XXX: We use a strong assumption for now: the cursor is
            // at the invalid region, so we just do goCursor().

            // however, in the future, onInvalidate should provice the
            // concrete invalid statement.
        },this);
    }

    // Get the next candidate and mark it.
    getNext(prev) {

        var spr, next;

        // If we have no previous element start with the first
        // snippet, else get the current one.
        if (!prev) {
            spr  = this.snippets[0];
            next = spr.getNext(null);
        } else {
            spr  = prev.sp;
            next = spr.getNext(prev);
        }

        // We got a snippet!
        if (next) {
            next.sp = spr;
            return next;
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

    cursorToStart(stm) {
        stm.sp.cursorToStart(stm);
    }

    cursorToEnd(stm) {
        stm.sp.cursorToEnd(stm);
    }

    focus() {
        if (this.currentFocus)
            this.currentFocus.focus();
        else
            this.snippets[0].focus();
    }

    // Get the point of the current focused element.
    getAtPoint() {
        return this.currentFocus.getAtPoint();
    }
}


/***********************************************************************/
/* CoqManager coordinates the coq code objects, the panel, and the coq */
/* js object.                                                          */
/*                                                                     */
/***********************************************************************/

var copyOptions = function(obj, target) {
    if (!target) target = {};
    for (var prop in target) {
        if (obj.hasOwnProperty(prop)) {
            target[prop] = obj[prop];
        }
    }
    return target;
}

class CoqManager {

    constructor(elems, options) {

        options = options ? options : {};

        // Default options
        this.options = {
            mock:    false,
            prelude: true,
            wrapper_id: 'ide-wrapper',
            base_path:  "./",
            init_pkgs: ['init'],
            all_pkgs:  ['init', 'math-comp',
                        'coq-base', 'coq-arith', 'coq-reals', 'elpi', 'equations', 'ltac2',
                        'coquelicot', 'flocq', 'sf', 'cpdt', 'color' ]
            // Disabled on 8.6
            // 'coquelicot', 'flocq', 'tlc', 'sf', 'cpdt', 'color', 'relalg', 'unimath',
            // 'plugin-utils', 'extlib', 'mirrorcore']
        };

        this.options = copyOptions(options, this.options);

        // UI setup.
        this.layout = new CoqLayoutClassic(this.options);

        // Setup our providers of Coq statements.
        this.provider = new ProviderContainer(elems);

        this.provider.onInvalidate = stm => {

            // Clear the last error, XXX it is a bit of a hack.
            if (this.error && this.error == stm) {
                this.provider.mark(this.error, "clear");
                this.error = null;
                return;
            } else if (this.error) {
                // Not the one invalidated, clear and go.
                this.provider.mark(this.error, "clear");
                this.error = null;
            }

            setTimeout( () => {
                this.goCursor();
                // We must do one more back, as the one in the cursor is the invalid one!
                this.goPrev(true);
            }, 100);
        };

        this.provider.onMouseEnter = stm => {
            if (stm.coq_sid) {
                console.log("Requested goals info:", this.goals[stm.coq_sid]);
            } else {
                console.log("Weird, info for stm but not coq_sid", stm);
            }
        };

        this.provider.onMouseLeave = stm => {
            console.log("leave");
        };

        this.waitForPkgs = [];

        var coq_script = this.options.base_path +
º            (this.options.mock ? 'coq-js/jsmock' : '_build/default/coq-js/jscoq.bc');

        // Missing Promise.bind from the browsers....
        loadJs(coq_script)().then(() => this.setupCoq());
    }

    setupCoq() {

        this.coq      = jsCoq;

        this.goals    = [];

        // Keybindings setup
        document.addEventListener('keydown', evt => this.keyHandler(evt));

        // XXX: Depends on the layout.
        document.getElementById('hide-panel')
            .addEventListener('click', evt => this.layout.toggle() );

        // XXX: Only done for the adjustWidth
        this.layout.coq = this.coq;

        // Panel setup 2: packages panel.
        // XXX: In the future this may also manage the downloads.
        this.packages = new PackageManager(this.layout.packages, this.options.base_path);

        // Bind jsCoq events 1: error
        this.coq.onError = e => {

            var stm = this.sentences.pop()
            this.provider.mark(stm, "clear");
            this.provider.mark(stm, "error");
            this.error = stm;

            // Tell coq to go back to the old state.
            this.sid.pop();
            this.coq.edit(this.sid.last());

        };

        // Bind jsCoq events: package information
        this.coq.onBundleInfo = bundle_info => {
            this.packages.addBundleInfo(bundle_info);
        };

        this.coq.onBundleStart = bundle_info => {
            this.packages.onBundleStart(bundle_info);
        };

        this.coq.onBundleLoad = bundle_info => {
            this.packages.onBundleLoad(bundle_info);

            // Reenable the IDE
            if (this.waitForPkgs.length > 0) {

                let name  = bundle_info.desc;
                let index = this.waitForPkgs.indexOf(name);

                if (index > -1) {
                    this.waitForPkgs.splice(index, 1);
                }

                if (this.waitForPkgs.length === 0) {
                    this.enable();
                }
            }
        };

        // Bind jsCoq events: package progress download.
        this.coq.onPkgProgress = progress => {
            this.packages.onPkgProgress(progress);
        };

        // Not used for now.
        this.coq.onPkgLoadStart = progress => {
            //
        };

        this.coq.onPkgLoad = progress => {
            //
        };

        // XXX: Use a proper object...
        this.coq.onLog = e => {

            var level = COQ_LOG_LEVELS.DEBUG;
            var msg = e.toString();

            if(msg.indexOf('Msg[Error]:') != -1) {
                level = COQ_LOG_LEVELS.ERROR;
                msg = msg.replace(/^.*Msg\[Error\]:/, '');
            }
            // XXX: This should go away.
            else if (msg.indexOf("pre-loading") != -1) {
                level = COQ_LOG_LEVELS.INFO;
                msg = msg.toString().replace(/^.*stderr:/, '');
            }
            else if (msg.indexOf("stderr:") != -1) {
                level = COQ_LOG_LEVELS.WARN;
                msg = msg.toString().replace(/^.*stderr:/, '');
            }
            else if (msg.indexOf("stdout:") != -1) {
                level = COQ_LOG_LEVELS.INFO;
                msg = msg.toString().replace(/^.*stdout:/, '');
            }
            else if(msg.indexOf("Msg[") != -1) {
                level = COQ_LOG_LEVELS.INFO;
                msg = msg.toString().replace(/^.*Msg\[.*\]:/, '');
            }

            else if(msg.indexOf("FileLoaded:") != -1) {
                level = COQ_LOG_LEVELS.INFO;
                msg = msg.toString().replace(/^.*FileLoaded: /, '');
                msg = msg.toString().replace(/ .*/, '');
                msg = "Loaded Module: " + msg;
            }

            // if(level != COQ_LOG_LEVELS.DEBUG) {
            msg = msg.trim().replace(/(?:\r\n|\r|\n)/g, '<br />');
            this.layout.log(msg, level);
            // }
        };

        // Coq Init: At this point, the required libraries are loaded
        // and Coq is ready to be used.
        this.coq.onInit = e => {

            // Hide the packages panel.
            var pkg_panel = document.getElementById('packages-panel').parentNode;
            pkg_panel.classList.add('collapsed');

            // Enable the IDE.
            this.layout.proof.textContent +=
                "\n===> JsCoq filesystem initalized with success!\n" +
                  "===> Loaded packages [" + this.options.init_pkgs.join(', ') + "] \n";

            if (this.options.prelude) {

                var prelude_command = "Require Import Coq.Init.Prelude. ";
                var pid = this.coq.add(this.sid.last(), -1, prelude_command);

                if (pid) {
                    this.coq.commit(pid);
                    this.sid.push(pid);
                } else {
                    console.log("Critical error: loading prelude");
                }
            }
            this.enable();
        };

        // Initial Coq state.
        this.layout.proof.textContent =
            this.coq.version() + "\nPlease wait for the libraries to load, thanks!"
                               + "\nIf you have trouble try cleaning your browser's cache.";
        this.sid = [];

        // Display packages panel:
        var pkg_panel = document.getElementById('packages-panel').parentNode;
        pkg_panel.classList.remove('collapsed');
        this.layout.show();

        // Initialize Coq! Options must be kept in sync !
        this.sid.push(this.coq.init(this.options));

        // This is a sid-based index of processed statements.
        this.sentences = [];
    }

    // Keyboard handling
    keyHandler(e) {

        // All our keybindings are prefixed by alt.
        if (e.keyCode === 119) // F8
            this.layout.toggle();

        if (!e.altKey && !e.metaKey) return true;
        var btn_name;
        switch (e.keyCode) {
            case 13: // ENTER
                btn_name = 'to-cursor';
                break;
            case 78: // N
            case 40: // flèche en bas
                btn_name = 'down';
                break;
            case 80: // P
            case 38: // flèche en haut
                btn_name = 'up';
                break;
        }

        if(btn_name) {
            this.provider.focus();
            this.raiseButton(btn_name);
            e.preventDefault();
        }
    }

    // Enable the IDE.
    enable() {

        // Set Printing Width
        window.addEventListener('resize', evt => { this.layout.adjustWidth(); } );

        // XXX: Should be the task of the layout.
        this.btnEventHandler = this.toolbarClickHandler.bind(this);
        this.layout.buttons.addEventListener('click', this.btnEventHandler);
        this.layout.buttons.style.display = 'inline-block';
        this.layout.buttons.style.opacity = 1;
        this.provider.focus();
    }

    // Disable the IDE.
    disable() {
        // Disable the buttons.
        this.layout.buttons.removeEventListener('click', this.btnEventHandler);
        this.layout.buttons.style.display = 'none';
        this.layout.buttons.style.opacity = 0;
        this.layout.proof.textContent +=
                "\n===> Waiting for Package load!\n";

    }

    // Drops all the state!
    reset() {

        // Not yet initialized.
        if(!this.sid) return;

        var initial_sid;

        if (this.options.prelude) {
            initial_sid = this.sid[1];
            this.sid    = [this.sid[0], this.sid[1]];
        } else {
            initial_sid = this.sid[0];
            this.sid    = [this.sid[0]];
        }

        // Reset Coq.
        this.coq.edit(initial_sid);

        // Reset out sentences
        this.sentences.forEach(function(stm) {
            this.provider.mark(stm, "clear");
        }, this);

        this.sentences = [];

    }

    toolbarClickHandler(evt) {

        this.provider.focus();

        switch (evt.target.name) {
            case 'to-cursor' :
                this.goCursor();
                break;

            case 'up' :
                this.goPrev(false);
                break;

            case 'down' :
                this.goNext(true);
                break;
        }
    }

    raiseButton(btn_name) {

        // XXX: EG: Here I disagree with the current code, it
        // should be possible to use the coq manager without a toolbar!

        // This is a bit different from most UI indeed.
        var btns = this.layout.buttons.getElementsByTagName('img');
        var btn  = btns.namedItem(btn_name);

        if (btn) {
            btn.dispatchEvent(new MouseEvent('click',
                                             {'view'       : window,
                                              'bubbles'    : true,
                                              'cancelable' : true
                                             }));
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

                let pkg_panel = document.getElementById('packages-panel').parentNode;
                pkg_panel.classList.remove('collapsed');

                this.disable();
                this.waitForPkgs = pkgs;

                pkgs.forEach(this.coq.add_pkg,this);

                return true;

            case 'dump':
                window.dumpCache();
                return true;

            default:
                console.log("Unrecognized jscoq command");
                return false;
            }
        }
        return false;
    }

    goPrev(inPlace) {

        // If we didn't load the prelude, prevent unloading it to
        // workaround a bug in Coq.
        if (!this.options.prelude && this.sentences.length <= 1) return;

        if (this.error) {
            this.provider.mark(this.error, "clear");
            this.error = null;
        }

        var stm = this.sentences.pop()
        this.provider.mark(stm, "clear");

        if(!inPlace)
            this.provider.cursorToStart(stm);

        // Tell coq to go back to the old state.
        let sid_old  = this.sid.pop();
        let sid_last = this.sid.last();

        stm.coq_sid = null;
        this.coq.edit(sid_last);

        this.goals[sid_old]  = null;
        this.goals[sid_last] = this.coq.goals();
        this.layout.update_goals(this.goals[sid_last]);

    }

    // Return if we had success.
    goNext(update_focus) {

        var next = this.provider.getNext(this.sentences.last());

        // We are the the end
        if(!next) { return false; }

        // Hack....
        if(next.is_comment) {
            this.provider.mark(next, "ok");
            return true;
        } else {
            this.provider.mark(next, "processing");
        }

        // We focus the new snippet.
        if(update_focus) {
            this.currentFocus = next.sp;
            this.currentFocus.focus();
        }
        // XXXX: We should be fully event driven here...

        // process special jscoq commands, for now:
        // Comment "pkg: list" will load packages.
        this.process_special(next.text);

        // Two things can happen: a parsing error (thus we will never get a sid),
        // of a succesful parse, we get a sid.

        // EG: For now we use a hack, parsing error returns 0
        var nsid = this.coq.add(this.sid.last(), -1, next.text);

        // Should we hook in the check add to request the commit after
        // the parse feedback?
        if (nsid) {

            // Try to execute it.
            this.sid.push(nsid);
            this.sentences.push(next);

            this.coq.commit(nsid);

            // Commit was successful
            if (nsid == this.sid.last()) {

                this.provider.mark(next, "clear");
                this.provider.mark(next, "ok");

                // We store the coq_sid in the sentence.
                next.coq_sid = nsid;

                // Print goals
                this.goals[nsid] = this.coq.goals();
                this.layout.update_goals(this.goals[nsid]);

                if(update_focus)
                    this.provider.cursorToEnd(next);

                return true;
            } else {
                // Cleanup was done in the onError handler.
                return false;
            }

        } else { // Parse/library loading error.

            this.provider.mark(next, "clear");
            this.provider.mark(next, "error");
            this.error = next;

            // Tell coq to go back to the old state.
            // this.sid.pop(); No need to pop as this is a parsing error!
            // XXX: Is this edit needed?
            this.coq.edit(this.sid.last());
            return false;
        }
    }

    // XXX Not used.
    goSentence(smt) {

        var idx = this.sentences.indexOf(smt);
        if (0 <= idx) {
            console.log("Going back to: " + idx + " " + this.sentences[idx].toString());
            while (this.sentences.length > idx + 1) {
                this.goPrev(false);
            }
        } else {}
    }

    goCursor() {

        var cur = this.provider.getAtPoint();

        if (cur) {
            var idx = this.sentences.indexOf(cur);
            if (0 <= idx) {
                console.log("Going back to: " + idx + " " + this.sentences[idx].toString());
                while (this.sentences.length > idx + 1) {
                    this.goPrev(true);
                }
                this.layout.show();
            } else { // We need to go next!
                console.log("Schedule goNext!");
                if (this.goNext(false)) {
                    setTimeout(() => { this.goCursor(); }, 100);
                }
            }
        } else {
            console.log("No cur at point! Trying a heuristic");
            if (this.goNext(false)) {
                setTimeout(() => { this.goCursor(); }, 50);
            }
        }
    }
}

// Local Variables:
// js-indent-level: 4
// End:
