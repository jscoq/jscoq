// The CoqManager (& CoqPanel) class.
// (c) 2015-2016 Mines ParisTech/ARMINES
//
// CoqManager manages a document composed of several coq snippets,
// allowing the user to send/retract indivual coq sentences throu
// them. The Coq snippets can be provided by several sources, we just
// require them to be able to list parts and implement marks.
//
// We also provide a side panel with proof and query buffers.

// XXX: use RequireJS or something like that.
"use strict";

function dumpCache () {

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

Array.prototype.last = function() { return this[this.length-1]; };

/***********************************************************************/
/* The CoqPanel class contains the goal and the query buffer           */
/***********************************************************************/
class CoqPanel {

    html(base_path) {
        var html = `
    <div id="toolbar">
      <div style="position:relative; left:-34px; top:2px">
      <div style="position:absolute">
      <svg id="hide-panel" title="Toggle panel (F8)" width="32" height="32">
        <path d="M16.001,0C7.165,0,0,7.164,0,16.001S7.162,32,16.001,32C24.838,32,32,24.835,32,15.999S24.838,0,16.001,0L16.001,0z"/>
        <g>
	  <path fill="#FFFFFF" d="M14,4.212c0-0.895,0.607-1.617,1.501-1.617C16.393,2.595,17,3.317,17,4.212v11.124
		                  c0,0.892-0.607,1.614-1.499,1.614c-0.894,0-1.501-0.722-1.501-1.614V4.212z"/>
	  <path fill="#FFFFFF" d="M16.001,27.817c-6.244,0-11.321-5.08-11.321-11.321c0-4.049,2.188-7.817,5.711-9.831
		                  c0.772-0.441,1.761-0.173,2.203,0.6c0.444,0.775,0.174,1.761-0.6,2.206c-2.519,1.441-4.083,4.133-4.083,7.025
		                  c0,4.462,3.629,8.09,8.09,8.09c4.459,0,8.091-3.628,8.091-8.09c0-2.892-1.567-5.584-4.086-7.025
		                  c-0.773-0.444-1.043-1.431-0.599-2.206c0.444-0.773,1.43-1.044,2.203-0.6c3.523,2.014,5.711,5.782,5.711,9.831
		                  C27.32,22.737,22.243,27.817,16.001,27.817L16.001,27.817z"/>
        </g>
      </svg>
      </div>
      </div>
      <div class="exits">
        <a href="http://feever.fr/" target="_blank">
          <img src="${base_path}/images/feever-logo.png" alt="FEEVER Logo" height="34" width="67"
               style="vertical-align: middle"/>
        </a>
        <a href="https://github.com/ejgallego/jscoq">Readme @ GitHub</a>
      </div> <!-- /#exits -->
      <span id="buttons">
        <img src="${base_path}/images/up.png" width="21" height="24"
             alt="Up (Ctrl-P)" title="Up (Ctrl-P)" name="up"/>
        <img src="${base_path}/images/down.png" width="21" height="25"
             alt="Down (Ctrl-N)" title="Down (Ctrl-N)" name="down"/>
        <img src="${base_path}/images/to-cursor.png" width="38" height="24"
             alt="To cursor (Ctrl-Enter)" title="To cursor (Ctrl-Enter)" name="to-cursor"/>
      </span>
    </div> <!-- /#toolbar -->
    <div class="flex-container">
      <div id="goal-panel" class="flex-panel">
        <div class="caption">Goals</div>
        <div id="goal-text" class="content"></div>
      </div>
      <div class="msg-area flex-panel">
        <div class="caption">
          Messages
          <select name="msg_filter">
            <option value="3">error</option>
            <option value="2">warn</option>
            <option value="1" selected="selected">info</option>
            <option value="0">debug</option>
          </select>
        </div>
        <div class="content" id="query-panel"></div>
      </div>
      <div class="flex-panel collapsed">
        <div class="caption">Packages</div>
        <div id="packages-panel" class="content"></div>
      </div>
    </div>`

        return html;
    }

    // Reference to the jsCoq object.
    constructor(options) {

        // Our reference to the IDE, goal display & query buffer.
        this.ide   = document.getElementById(options.wrapper_id);

        this.panel = document.createElement('div');
        this.panel.id = 'panel-wrapper';
        this.panel.innerHTML = this.html(options.base_path);

        this.ide.appendChild(this.panel);
        this.proof = document.getElementById("goal-text");
        this.query = document.getElementById("query-panel");

        this.log_css_rules = document.styleSheets[0].cssRules;

        var flex_container = document.getElementById('panel-wrapper').getElementsByClassName('flex-container')[0];
        flex_container.addEventListener('click', evt => { this.panelClickHandler(evt); });

        d3.select('select[name=msg_filter]')
            .on('change', () => this.filterLog(d3.event.target));
    }

    adjustWidth() {

        setTimeout(() => {

            // Set Printing Width... Far from perfect (XXX: Update on resize)
            var pxSize  = parseFloat(getComputedStyle(this.query)['font-size']);

            // A correction of almost 2.0 is needed here ... !!!
            var emWidth = Math.floor(this.query.offsetWidth / pxSize * 1.65);
            console.log("Setting printing width to: " + emWidth );

            // XXX: What if the panel is toogled from the start...!
            // Shoud send a message.
            this.coq.set_printing_width(emWidth);
        }, 500);
    }

    show() {
        this.ide.classList.remove('toggled');
        // XXX: This will fail if coq is not loaded...
        this.adjustWidth();
    }

    hide() {
        this.ide.classList.add('toggled');
    }

    toggled() {
        return this.ide.classList.contains('toggled');
    }

    toggle() {

        if (this.toggled()) {
            this.show();
        }
        else {
            this.hide();
        }
    }


    // Call jsCoq to get the info.
    update() {
        // TODO: Add diff/history of goals.
        // XXX: should send a message.
        this.proof.textContent = this.coq.goals();
    }

    // Add a log event received from Coq.
    log(text, level) {

        d3.select(this.query)
            .append('div')
            .attr('class', level)
            .html(text)
            .node()
            .scrollIntoView();
    }

    filterLog(level_select) {

        var length = level_select.getElementsByTagName('option').length;
        var min_log_level = parseInt(level_select.value, 10);
        var i;
        for(i=0 ; i < min_log_level ; i++)
            this.log_css_rules[i].style.display = 'none';
        for(i=min_log_level ; i < length ; i++)
            this.log_css_rules[i].style.display = 'block';
    }

    // Execute a query to Coq
    query(query) {
        return true;
    }

    panelClickHandler(evt) {

        var target = evt.target;

        if(target.classList.contains('caption') &&

            target.parentNode.classList.contains('flex-panel')) {

            var panel = target.parentNode;

            if(panel.classList.contains('collapsed')) {

                panel.classList.remove('collapsed');

            } else {

                var panels_cpt = this.panel.getElementsByClassName('flex-panel').length;
                var collapsed_panels_cpt = this.panel.getElementsByClassName('collapsed').length;

                if(collapsed_panels_cpt + 1 >= panels_cpt) // at least one panel opened
                    return;

                panel.classList.add('collapsed');
            }
        }
    }
}

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
            all_pkgs:  ['init', 'math-comp', 'mtac',
                        'coq-base', 'coq-arith', 'coq-reals',
                        'coquelicot', 'flocq', 'tlc', 'sf', 'cpdt', 'color', 'relalg']
        };

        this.options = copyOptions(options, this.options);

        this.panel = new CoqPanel(this.options);

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
                this.goPrev(true);
            }, 100);
        };

        var coq_script = this.options.base_path +
            (this.options.mock ? 'coq-js/jsmock' : 'coq-js/jscoq');

        // Missing Promise.bind from the browsers....
        loadJs(coq_script)().then(() => this.setupCoq());
    }

    setupCoq() {

        this.coq      = jsCoq;

        // Keybindings setup
        document.addEventListener('keydown', evt => this.keyHandler(evt));
        document.getElementById('hide-panel')
            .addEventListener('click', evt => this.panel.toggle() );

        // Panel setup 1: query panel
        this.panel.coq = this.coq;

        // Panel setup 2: packages panel.
        // XXX: In the future this may also manage the downloads.
        this.packages =
            new PackageManager(document.getElementById('packages-panel'), this.options.base_path);

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
        };

        // Bind jsCoq events: package progress download.
        this.coq.onPkgProgress = progress => {
            this.packages.onPkgProgress(progress);
        };

        // Not used fro now.
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

            if(msg.indexOf('ErrorMsg:') != -1) {
                level = COQ_LOG_LEVELS.ERROR;
                msg = msg.replace(/^.*ErrorMsg:/, '');
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
            else if(msg.indexOf("Msg:") != -1) {
                level = COQ_LOG_LEVELS.INFO;
                msg = msg.toString().replace(/^.*Msg:/, '');
            }

            else if(msg.indexOf("FileLoaded:") != -1) {
                level = COQ_LOG_LEVELS.INFO;
                msg = msg.toString().replace(/^.*FileLoaded: /, '');
                msg = msg.toString().replace(/ .*/, '');
                msg = "Loaded Module: " + msg;
            }

            if(level != COQ_LOG_LEVELS.DEBUG) {
                msg = msg.replace(/(?:\r\n|\r|\n)/g, '<br />');
                this.panel.log(msg, level);
            }
        };

        // Coq Init: At this point, the required libraries are loaded
        // and Coq is ready to be used.
        this.coq.onInit = e => {

            // Hide the packages panel.
            var pkg_panel = document.getElementById('packages-panel').parentNode;
            pkg_panel.classList.add('collapsed');

            // Enable the IDE.
            this.panel.proof.textContent +=
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
        this.panel.proof.textContent =
            this.coq.version() + "\nPlease wait for the libraries to load, thanks!";

        this.sid = [];

        // Display packages panel:
        var pkg_panel = document.getElementById('packages-panel').parentNode;
        pkg_panel.classList.remove('collapsed');
        this.panel.show();

        // Initialize Coq! Options must be kept in sync !
        this.sid.push(this.coq.init(this.options));

        // This is a sid-based index of processed statements.
        this.sentences = [];
    }

    // Keyboard handling
    keyHandler(e) {

        // All our keybindings are prefixed by alt.
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
    }

    // Enable the IDE.
    enable() {

        // Set Printing Width
        window.addEventListener('resize', evt => { this.panel.adjustWidth(); } );

        // Enable the buttons.
        this.buttons.addEventListener('click', evt => { this.toolbarClickHandler(evt); } );
        this.buttons.style.display = 'inline-block';
        this.buttons.style.opacity = 1;
        this.provider.focus();
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

        var btns = this.buttons.getElementsByTagName('img');
        var btn  = btns.namedItem(btn_name);

        if (btn) {
            btn.dispatchEvent(new MouseEvent('click',
                                             {'view'       : window,
                                              'bubbles'    : true,
                                              'cancelable' : true}));
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

                pkgs.forEach(this.coq.add_pkg,this);

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
        this.sid.pop();
        this.coq.edit(this.sid.last());
        this.panel.update();

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

                // Print goals
                this.panel.update();

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
                    this.goPrev(false);
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
    }
}

// Local Variables:
// js-indent-level: 4
// End:
