// The CoqManager (& CoqPanel) class.
// (c) 2015 Mines ParisTech/ARMINES
//
// CoqManager manages a document composed of several coq snippets,
// allowing the user to send/retract indivual coq sentences throu
// them. The Coq snippets can be provided by several sources, we just
// require them to be able to list parts and implement marks.
//
// We also provide a side panel with proof and query buffers.

var CoqPanel;
var CoqManager;
var ProviderContainer;

function dumpCache() {
    "use strict";
    var data = "text/json;charset=utf-8," + encodeURIComponent(JSON.stringify(dumpJsCacheB));
    $('<a href="data:' + data + '" download="data.json">download JSON</a>').appendTo('#ide-wrapper');
}

(function(){
    "use strict";

    Array.prototype.last = function() { return this[this.length-1]; };

    /***********************************************************************/
    /* The CoqPanel object contains the goal and the query buffer          */
    CoqPanel = function(jsCoq) {

        // Our copy of the jsCoq object.
        this.coq = jsCoq;

        // Proof display & query buffer.
        this.proof = document.getElementById("goal-text");
        this.query = document.getElementById("query-panel");
    };

    CoqPanel.prototype.show = function() {
        $("#ide-wrapper").removeClass("toggled");
    };

    CoqPanel.prototype.hide = function() {
        $("#ide-wrapper").addClass("toggled");
    };

    CoqPanel.prototype.toggle = function() {
        $("#ide-wrapper").toggleClass("toggled");
    };

    // Call jsCoq to get the info.
    CoqPanel.prototype.update = function() {

        // TODO: Add diff/history of goals.
        this.proof.textContent = this.coq.goals();
    };

    // Add a log event received from Coq.
    CoqPanel.prototype.log    = function(text) {

        var span = document.createElement('span');
        // Now Coq logs escaped pseudo-xml...
        span.innerHTML = text;
        this.query.insertBefore(span, this.query.firstChild);
    };

    // Execute a query to Coq
    CoqPanel.prototype.query  = function(query) {
        return true;
    };

    /***********************************************************************/
    /* A Provider Container aggregates several containers, the main deal   */
    /* here is keeping track of focus, as the focused container can be     */
    /* different from the "active" one                                     */
    /***********************************************************************/

    ProviderContainer = function(elms) {

        // Code snippets.
        this.snippets = [];

        // Debug variables
        var idx = 0;

        // for (e of elms) not very covenient here due to the closure.
        elms.forEach(function (e) {

            // Init.
            var cm = new CmCoqProvider(document.getElementById(e));
            cm.idx = idx++;
            this.snippets.push(cm);

            // Track focus XXX (make generic)
            cm.editor.on('focus', evt => { this.currentFocus = cm; });

            // Track invalidate
            cm.onInvalidate = (smt) => { this.onInvalidate(smt); };

            // XXX: We use a strong assumption for now: the cursor is
            // at the invalid region, so we just do goCursor().

            // however, in the future, onInvalidate should provice the
            // concrete invalid statement.
        },this);
    };

    // Get the next candidate and mark it.
    ProviderContainer.prototype.getNext = function(prev) {
        var spr, next;
        // First element
        if (!prev) {
            spr  = this.snippets[0];
            next = spr.getNext(null);
            next.sp = spr;
            return next;
        } else {
            // Try next on the current snippet.
            spr  = prev.sp;
            next = spr.getNext(prev);

            if (next) {
                next.sp = spr;
                return next;
            } else {
                // go to next snippet.
                var idx = this.snippets.indexOf(spr);
                if (idx >= this.snippets.length - 1) {
                    // No next snippet.
                    return null;
                } else {
                    spr  = this.snippets[idx+1];
                    next = spr.getNext(null);
                    next.sp = spr;
                    return next;
                }
            }
        }
    };

    ProviderContainer.prototype.mark  = function(stm, mark) {
        stm.sp.mark(stm, mark);
    };

    ProviderContainer.prototype.focus = function() {
        if (this.currentFocus)
            this.currentFocus.focus();
        else
            this.snippets[0].focus();
    };

    // Get the point of the current focused element.
    ProviderContainer.prototype.getAtPoint = function() {
        return this.currentFocus.getAtPoint();
    };

    /***********************************************************************/
    /* CoqManager coordinates the coq code objects, the panel, and the coq */
    /* js object.                                                          */
    /*                                                                     */
    /***********************************************************************/

    // XXX: Rename to Coq Director?
    CoqManager = function(elems, mock) {

        if (typeof(mock) === 'undefined') {
            mock = false;
        }

        this.mock = mock;
        // UI setup.
        this.buttons = document.getElementById('buttons');

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
                this.goPrev();
            }, 100);
        };
        // Coq Setup
        window.addEventListener('load', evt => { this.loadJsCoq(evt); } );
    };

    CoqManager.prototype.loadJsCoq = function(evt) {

        // Load JsCoq
        var jscoqscript    = document.createElement('script');
        jscoqscript.type   = 'text/javascript';
        jscoqscript.src    = this.mock ? 'coq-js/jsmock.js' : 'coq-js/jscoq.js';
        jscoqscript.onload = evt => { this.setupCoq(evt); };
        document.head.appendChild(jscoqscript);
    };

    CoqManager.prototype.setupCoq = function() {

        this.coq   = jsCoq;
        this.panel = new CoqPanel(this.coq);
        // this.panel.show();
        $("#hide-panel").click(evt => this.panel.toggle());

        this.coq.onError = e => {

            var stm = this.sentences.pop()
            this.provider.mark(stm, "clear");
            this.provider.mark(stm, "error");
            this.error = stm;

            // Tell coq to go back to the old state.
            this.sid.pop();
            this.coq.edit(this.sid.last());

        };

        // Hacks, we should refine...
        this.coq.onLog   = e => {

            // console.log("CoqLog: " + e.toString());

            // Error msgs.
            if (e.toString().indexOf("ErrorMsg:") != -1)
                // Sanitize
                this.panel.log(e.toString().replace(/^.*ErrorMsg:/, ""));
            // User queries, usually in the query buffer
            else if (e.toString().indexOf("Msg:") != -1)
                this.panel.log(e.toString().replace(/^.*Msg:/, ""));
            else if (e.toString().indexOf("pre-loading") != -1)
                this.panel.log(e.toString());
        };

        this.coq.onInit = e => {
            // Enable the IDE.
            this.panel.proof.textContent += "\n===> JsCoq filesystem initalized with success!";
            this.enable();
        };

        // Initial coq state.
        this.panel.proof.textContent = this.coq.version() + "\nPlease wait for the libraries to load, thanks!";

        this.sid = [];
        this.sid.push(this.coq.init());

        // This is a sid-based statement index.
        this.sentences = [];
    };


    CoqManager.prototype.keyHandler = function(e) {
        // All our keybinding are prefixed by alt.
        if (!e.altKey) return true;

        // console.log("key alt-code: " + e.keyCode);
        switch (e.keyCode) {
        case 13:
            this.goCursor();
            break;
        // case 38:
        //     this.panel.show();
        //     break;
        case 39:
            this.panel.toggle();
            break;
        case 76:
            // Alt-l, recenter (XXX)k
            break;
        case 78:
            this.goNext();
            break;
        case 80:
            this.goPrev();
            break;
        default:
            console.log("Uncapture alt command: " + e.keyCode);
        }
        this.provider.focus();
        return true;
    };

    CoqManager.prototype.enable = function() {

        this.buttons.addEventListener('click', evt => { this.toolbarClickHandler(evt); } );
        this.buttons.style.display = 'inline-block';
        this.buttons.style.opacity = 1;
        this.provider.focus();

        $(document).keydown(this.keyHandler.bind(this));
    };

    CoqManager.prototype.toolbarClickHandler = function(evt) {

        this.provider.focus();

        switch (evt.target.name) {
            case 'to-cursor' :
                this.goCursor();
                break;

            case 'up' :
                this.goPrev();
                break;

            case 'down' :
                this.goNext();
                break;
        }
    };

    CoqManager.prototype.goPrev = function () {

        if (this.sentences.length <= 1) return;

        if (this.error) {
            this.provider.mark(this.error, "clear");
            this.error = null;
        }

        var stm = this.sentences.pop()
        this.provider.mark(stm, "clear");

        // Tell coq to go back to the old state.
        this.sid.pop();
        this.coq.edit(this.sid.last());
        this.panel.update();

    };

    // Return if we had success.
    CoqManager.prototype.goNext = function () {

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

        // We should be fully event driven here...

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

                // Print goals
                this.panel.update();
                return true;
            } else
                // Cleanup was done in the onError handler.
                return false;
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
    };

    // XXX Not used.
    CoqManager.prototype.goSentence = function (smt) {

        var idx = this.sentences.indexOf(smt);
        if (0 <= idx) {
            console.log("Going back to: " + idx + " " + this.sentences[idx].toString());
            while (this.sentences.length > idx + 1) {
                this.goPrev();
            }
        } else {}
    };

    CoqManager.prototype.goCursor = function () {

        var cur = this.provider.getAtPoint();

        if (cur) {
            var idx = this.sentences.indexOf(cur);
            if (0 <= idx) {
                console.log("Going back to: " + idx + " " + this.sentences[idx].toString());
                while (this.sentences.length > idx + 1) {
                    this.goPrev();
                }
                this.panel.show();
            } else { // We need to go next!
                console.log("Schedule goNext!");
                if (this.goNext()) {
                    setTimeout(100, () => { this.goCursor(); } );
                }
            }
        } else {
            console.log("No cur at point! Trying a heuristic");
            if (this.goNext()) {
                setTimeout(() => { this.goCursor(); }, 50 );
            }
        }
    };
}());

// Local Variables:
// js-indent-level: 4
// End:
