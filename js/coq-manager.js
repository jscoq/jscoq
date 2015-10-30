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

(function(){
    "use strict";

    /***********************************************************************/
    /* The CoqPanel object contains the goal and the query buffer          */
    var CoqPanel = function(jsCoq) {

        // Our copy of the jsCoq object.
        this.coq = jsCoq;

        // Proof display & query buffer.
        this.proof = document.getElementById("goal-text");
        this.query = document.getElementById("query-panel");
    }

    CoqPanel.prototype.show = function() {
        $("#ide-wrapper").removeClass("toggled");
    }

    CoqPanel.prototype.hide = function() {
        $("#ide-wrapper").addClass("toggled");
    }

    CoqPanel.prototype.toggle = function() {
        $("#ide-wrapper").toggleClass("toggled");
    }

    // Call jsCoq to get the info.
    CoqPanel.prototype.update = function() {

        // TODO: Add diff/history of goals.
        this.proof.textContent = this.coq.goals();
    }

    // Add a log event received from Coq.
    CoqPanel.prototype.log    = function(text) {

        var span = document.createElement('span');
        // Now Coq logs escaped pseudo-xml...
        span.innerHTML = text;
        this.query.insertBefore(span, this.query.firstChild);
    }

    // Execute a query to Coq
    CoqPanel.prototype.query  = function(query) {
        return true;
    }

    /***********************************************************************/
    /* CoqManager coordinates the coq code objects, the panel, and the coq */
    /* js object.                                                          */
    /*                                                                     */
    /***********************************************************************/

    CoqManager = function() {

        // UI setup.
        this.buttons       = document.getElementById('buttons');
        this.script_panel  = document.getElementById('script-panel');

        // Setup our provider of Coq statements.
        this.provider      = new CmCoqProvider(this.script_panel.getElementsByTagName('textarea')[0]);

        // Invalidate some previous region.
        // this.provider.onInvalidate = smt => { this.goSentence(smt); };

        // We follow a simpler approach for now XXX.
        this.provider.onInvalidate = () => {
            this.goCursor();
            // We must do one more!
            this.goPrev()
        };

        // Coq Setup
        window.addEventListener('load', evt => { this.loadJsCoq(evt); } );
    };

    CoqManager.prototype.loadJsCoq = function(evt) {

        // XXX: make it a config parameter.
        var jscoq_mock     = false;

        // Load JsCoq
        var jscoqscript    = document.createElement('script');
        jscoqscript.type   = 'text/javascript';
        jscoqscript.src    = jscoq_mock ? 'coq-js/jsmock.js' : 'coq-js/jscoq.js';
        jscoqscript.onload = evt => { this.setupCoq(evt); };
        document.head.appendChild(jscoqscript);
    };

    CoqManager.prototype.setupCoq = function() {

        this.coq   = jsCoq;
        this.panel = new CoqPanel(this.coq);

        this.panel.show();

        this.coq.onError = e => {

            var stm = this.sentences.pop()
            this.provider.mark(stm, "clear");
            this.provider.mark(stm, "error");

            // Tell coq to go back to the old state.
            this.sid.pop();
            this.coq.edit(this.sid.last());

        };

        // Hacks, we should refine...
        this.coq.onLog   = e => {

            console.log("CoqLog: " + e.toString());

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
    }

    CoqManager.prototype.enable = function() {

        this.buttons.addEventListener('click', evt => { this.toolbarClickHandler(evt); } );
        // Trying with a different apporach?
        $("#hide-panel").click(evt => this.panel.toggle());
        this.buttons.style.display = 'table-cell';
        this.buttons.style.opacity = 1;
        this.provider.focus();
    }

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

        var stm = this.sentences.pop()
        this.provider.mark(stm, "clear");

        // Tell coq to go back to the old state.
        this.sid.pop();
        this.coq.edit(this.sid.last());
        this.panel.update();
    }

    // Return if we had success.
    CoqManager.prototype.goNext = function () {

        var next = this.provider.getNext(this.sentences.last());

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

            // Tell coq to go back to the old state.
            this.sid.pop();
            this.coq.edit(this.sid.last());
            return false;
        }
    }

    CoqManager.prototype.goSentence = function (smt) {

        var idx = this.sentences.indexOf(smt);
        if (0 <= idx) {
            console.log("Going back to: " + idx + " " + this.sentences[idx].toString());
            while (this.sentences.length > idx + 1) {
                this.goPrev();
            }
        } else {}
    }

    CoqManager.prototype.goCursor = function () {

        var cur = this.provider.getAtPoint();

        if (cur) {
            var idx = this.sentences.indexOf(cur);
            if (0 <= idx) {
                console.log("Going back to: " + idx + " " + this.sentences[idx].toString());
                while (this.sentences.length > idx + 1) {
                    this.goPrev();
                }
            } else {
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
    }
}());

// Local Variables:
// js-indent-level: 4
// End:
