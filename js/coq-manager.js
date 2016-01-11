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

function dumpCache () {
    "use strict";

    var download = function (text,filename) {
        var element = document.createElement('a');
        element.setAttribute('href', 'data:text/plain;charset=utf-8,' + encodeURIComponent(text));
        element.setAttribute('download', filename);
        element.style.display = 'none';
        document.body.appendChild(element);
        element.click();
        document.body.removeChild(element);
    };

    download(JSON.stringify(dumpJsCacheA), "bc-md5.json");
    download(JSON.stringify(dumpJsCacheB), "bc-js.json");
}

var COQ_LOG_LEVELS = {
    DEBUG : 'debug',
    INFO  : 'info',
    WARN  : 'warn',
    ERROR : 'error'
};

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
        this.log_css_rules = document.styleSheets[0].cssRules;
        var flex_container = document.getElementById('panel-wrapper').getElementsByClassName('flex-container')[0];
        flex_container.addEventListener('click', evt => {this.panelClickHandler(evt);});
        d3.select('select[name=msg_filter]')
            .on('change', () => this.filterLog(d3.event.target));
    };

    CoqPanel.prototype.show = function() {
        document.getElementById('ide-wrapper').classList.remove('toggled');
    };

    CoqPanel.prototype.hide = function() {
        document.getElementById('ide-wrapper').classList.add('toggled');
    };

    CoqPanel.prototype.toggle = function() {
        var ide = document.getElementById('ide-wrapper');
        if (ide.classList.contains('toggled'))
            ide.classList.remove('toggled');
        else
            ide.classList.add('toggled');
    };

    // Call jsCoq to get the info.
    CoqPanel.prototype.update = function() {

        // TODO: Add diff/history of goals.
        this.proof.textContent = this.coq.goals();
    };

    // Add a log event received from Coq.
    CoqPanel.prototype.log = function(text, level) {
        d3.select(this.query)
            .append('div')
            .attr('class', level)
            .html(text)
            .node()
            .scrollIntoView();
    };

    CoqPanel.prototype.filterLog = function(level_select) {
        var length = level_select.getElementsByTagName('option').length;
        var min_log_level = parseInt(level_select.value, 10);
        var i;
        for(i=0 ; i < min_log_level ; i++)
            this.log_css_rules[i].style.display = 'none';
        for(i=min_log_level ; i < length ; i++)
            this.log_css_rules[i].style.display = 'block';
    };

    // Execute a query to Coq
    CoqPanel.prototype.query  = function(query) {
        return true;
    };

    CoqPanel.prototype.panelClickHandler = function(evt) {
        var target = evt.target;
        if(target.classList.contains('caption') &&
            target.parentNode.classList.contains('flex-panel')) {
            var panel = target.parentNode;
            if(panel.classList.contains('collapsed'))
                panel.classList.remove('collapsed');
            else {
                var wrapper = document.getElementById('panel-wrapper');
                var panels_cpt = wrapper.getElementsByClassName('flex-panel').length;
                var collapsed_panels_cpt = wrapper.getElementsByClassName('collapsed').length;
                if(collapsed_panels_cpt + 1 >= panels_cpt) // at least one panel opened
                    return;
                panel.classList.add('collapsed');
            }
        }
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

    var copyOptions = function(obj, target) {
        if (!target) target = {};
        for (var prop in target) {
            if (obj.hasOwnProperty(prop)) {
                target[prop] = obj[prop];
            }
        }
        return target;
    }

    /***********************************************************************/
    /* CoqManager coordinates the coq code objects, the panel, and the coq */
    /* js object.                                                          */
    /*                                                                     */
    /***********************************************************************/

    // XXX: Rename to Coq Director?
    CoqManager = function(elems, options) {

        options = options ? options : {};

        // Default options
        this.options = {
            mock:    false,
            prelude: true,
            coq_packages: ['coq-base', 'math-comp', 'coq-arith', 'coq-reals',
                           'coquelicot', 'flocq', 'tlc', 'sf', 'cpdt']
        };

        this.options = copyOptions(options, this.options);

        // UI setup.
        this.buttons = document.getElementById('buttons');

        // Setup our providers of Coq statements.
        this.provider = new ProviderContainer(elems);

    /*
        this.packages = new PackagesManager(coq_packages,
                                            document.getElementById('packages-panel'));
    */

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
        document.addEventListener('keydown', evt => this.keyHandler(evt));
    };

    CoqManager.prototype.loadJsCoq = function(evt) {

        // Load JsCoq
        var jscoqscript    = document.createElement('script');
        jscoqscript.type   = 'text/javascript';
        jscoqscript.src    = this.options.mock ? 'coq-js/jsmock.js' : 'coq-js/jscoq.js';
        jscoqscript.onload = evt => { this.setupCoq(evt); };
        document.head.appendChild(jscoqscript);
    };

    CoqManager.prototype.setupCoq = function() {

        this.coq   = jsCoq;
        this.panel = new CoqPanel(this.coq);
        // this.panel.show();
        document.getElementById('hide-panel')
            .addEventListener('click', evt => this.panel.toggle());

        this.coq.onError = e => {

            var stm = this.sentences.pop()
            this.provider.mark(stm, "clear");
            this.provider.mark(stm, "error");
            this.error = stm;

            // Tell coq to go back to the old state.
            this.sid.pop();
            this.coq.edit(this.sid.last());

        };

        this.coq.onPkgLoadInfo = pkg_info => {
            console.log("pkg info called for: ");
            console.log(pkg_info);
        };

        this.coq.onPkgLoadStart = pkg => {
            console.log("pkg start called for: " + pkg[1] + " @ " + pkg[2].toString());
        };

        this.coq.onPkgLoad = pkg => {
            console.log("pkg load called for: " + pkg);
        };

        this.coq.onPkgProgress = pkg => {
            console.log("pkg progress called for: " + pkg[1] + " @ " + pkg[2].toString());
        };

        // Hacks, we should refine...
        this.coq.onLog = e => {

            var level = COQ_LOG_LEVELS.DEBUG;
            var msg = e.toString();

            if(msg.indexOf('ErrorMsg:') != -1) {
                level = COQ_LOG_LEVELS.ERROR;
                msg = msg.replace(/^.*ErrorMsg:/, '');
            }
            else if(msg.indexOf("Msg:") != -1) {
                level = COQ_LOG_LEVELS.INFO;
                msg = msg.toString().replace(/^.*Msg:/, '');
            }
            else if (msg.indexOf("pre-loading") != -1) {
                level = COQ_LOG_LEVELS.INFO;
            }

            // if(level != COQ_LOG_LEVELS.DEBUG) {
                msg = msg.replace(/(?:\r\n|\r|\n)/g, '<br />');
                this.panel.log(msg, level);
            // }
        };

        this.coq.onInit = e => {
            // Enable the IDE.
            this.panel.proof.textContent += "\n===> JsCoq filesystem initalized with success!\n===> Loading additional packages in the background...";

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

            for (var pkg in this.options.coq_packages) {
                this.coq.add_pkg(this.options.coq_packages[pkg]);
            }
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
        if (e.keyCode === 119) // F8
            this.panel.toggle();

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
    };

    CoqManager.prototype.enable = function() {
        this.buttons.addEventListener('click', evt => { this.toolbarClickHandler(evt); } );
        this.buttons.style.display = 'inline-block';
        this.buttons.style.opacity = 1;
        this.provider.focus();
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
                this.goNext(true);
                break;
        }
    };

    CoqManager.prototype.raiseButton= function(btn_name) {
        var btns = this.buttons.getElementsByTagName('img');
        var btn  = btns.namedItem(btn_name);

        if (btn) {
            btn.dispatchEvent(new MouseEvent('click',
                                             {'view'       : window,
                                              'bubbles'    : true,
                                              'cancelable' : true}));
        }
    };

    CoqManager.prototype.goPrev = function () {

        // If we didn't load the prelude, prevent unloading it to
        // workaround a bug in Coq.
        if (!this.options.prelude && this.sentences.length <= 1) return;

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
    CoqManager.prototype.goNext = function (update_focus) {

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
    };
}());

// Local Variables:
// js-indent-level: 4
// End:
