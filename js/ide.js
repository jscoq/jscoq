var IDELayout;
var Editor;

(function(){

    var SEP_SIZE = 6;
    var DOT_R = /\.$|\.\s/;

    Array.prototype.last = function() { return this[this.length-1]; };

    IDELayout = function() {

        this.left_panel    = document.getElementById('left-panel');
        this.toolsbar      = document.getElementById('toolsbar');
        this.right_panel   = document.getElementById('right-panel');
        this.script_panel  = document.getElementById('script-panel');
        this.goal_panel    = document.getElementById('goal-panel');
        this.goal_text = document.getElementById("goal-text");
        this.message_panel = document.getElementById('message-panel');
        this.vsep          = document.getElementById('vsep');
        this.hsep          = document.getElementById('hsep');
        this.editor        = new Editor('coq', this.script_panel.getElementsByTagName('textarea')[0]);

        var self = this;
        this.toolsbar.addEventListener('click', function(evt){ self.toolbarClickHandler(evt); });
        window.addEventListener('load', function(evt){self.onload(evt);});
    };
    
    IDELayout.prototype.onload = function(evt) {
        var jscoqscript = document.createElement('script');
        jscoqscript.type = 'text/javascript';
        document.head.appendChild(jscoqscript);
        var self = this;
        jscoqscript.onload = function(evt){self.setupCoq(evt);};
        jscoqscript.src = 'coq-js/jscoq.js';
    };
    
    IDELayout.prototype.setupCoq = function() {
        var self = this;
        jsCoq.onError = function(e){self.printCoqEvent(e);};
        jsCoq.onLog = function(e){// Hack
                                  if (e.toString().indexOf("ErrorMsg") != -1)
                                          self.printCoqEvent(e);
                                 };
        // Initial sid.
        jsCoq.sid = [];
        jsCoq.sid.push(jsCoq.init());
        this.goal_text.innerHTML = jsCoq.version();
    };
    
    IDELayout.prototype.printCoqEvent = function(coqevt) {
        var span = document.createElement('span');
        span.innerHTML = coqevt.toString();
        this.message_panel.insertBefore(this.message_panel.firstChild);
    };
    
    IDELayout.prototype.toolbarClickHandler = function(evt) {

        var target = evt.target;

        switch (target.name) {

            case 'ceiling' :
                // EG: Uh uh
                while(this.editor.popStatement());
                break;

            case 'floor' :
                while(this.editor.eatNextStatement());
                break;

            case 'up' :
                this.editor.popStatement();
                break;

            case 'down' :
                this.editor.eatNextStatement();
                break;
        }
    };

    Editor = function(name, element) {

        this.idgen = new IDGen();

        // Statements holds the code already sent to Coq.
        this.statements = [];

        this._editor = CodeMirror.fromTextArea(element,
            {mode : {name : "coq",
                     version: 3,
                     singleLineStringErrors : false
                   },
             lineNumbers   : true,
             indentUnit    : 4,
             matchBrackets : true
            }
        );

        var self = this;
        this._editor.on('change', function(evt){ self.onCMChange(evt); });

    };



    /* EG:
     *
     * I'm not still sure how we want to do it, but I think we want to
     * maintain a richer structure of the Coq's document.
     *
     * Parsing should be done asynchronously (as in Emacs) and the
     * user should get some feedback out of it.
     *
     */

    // Send next statement to Coq.
    Editor.prototype.eatNextStatement = function() {

        var cm    = this._editor;
        var doc   = cm.getDoc();
        var start = {line : 0, ch : 0};

        // Locate the end of the document.
        if (this.statements.length) {

            var lastStm = this.statements.last();
            start = lastStm.end;

            // If there are no more statements, stop.
            // EG: Fix this.
            if (start.line === doc.lastLine() &&
                start.ch === doc.getLine(doc.lastLine()).length) {
                return false;
            }
        }

        var start_ch = start.ch;
        var text, handle, end_ch=0, dotmatch=null;

        // EG: This seems broken...
        for (var i=start.line ; i<doc.lineCount() ; i++) {

            handle = doc.getLineHandle(i);
            text = handle.text.slice(start_ch);
            dotmatch = DOT_R.exec(text);

            if(dotmatch !== null &&
                cm.getTokenAt({line: i,
                               ch: dotmatch.index + 1}).type !== 'comment') {
                end_ch = start_ch + dotmatch.index + 1;
                break;
            }
            start_ch = 0;
        }


        if (dotmatch === null)
            return false;

        // We found a statement!
        var stm = new Statement(start,
                                {line : handle.lineNo(),
                                 ch   : end_ch},
                                 text
                               );

        // Add the statement to our list.
        stm.id = this.idgen.next();
        this.statements.push(stm);
        stm.position = this.statements.length - 1;

        // EG: The stm should gain eid and sid properties.
        // In fact, there are 3 states for a statement: new, parsed, and executed/errored.
        this.coqEval(stm);
        return true;
    };

    Editor.prototype.coqEval = function(stm) {

        // Mark the statement
        var doc  = this._editor.getDoc();

        // XXX: Quack!
        var mark = doc.markText(stm.start, stm.end, {className : 'coq-eval-pending'});
        mark.stm = stm;
        stm.mark = mark;

        // We should be fully event driven here...

        // Two things can happen: a parsing error (thus we will never get a sid),
        // of a succesful parse, we get a sid.

        // EG: For now we use a hack, parsing error returns 0
        var nsid = jsCoq.add(jsCoq.sid.last(), -1, stm.text);

        // Should we hook in the check add to request the commit after
        // the parse feedback?
        if (nsid) {

            // Try to execute it.
            jsCoq.sid.push(nsid);
            jsCoq.commit(nsid);

            // Commit was successful
            if (nsid == jsCoq.sid.last()) {
                mark.clear();
                mark = doc.markText(stm.start, stm.end, {className : 'coq-eval-ok'});
                mark.stm = stm;
                stm.mark = mark;

              // Print goals
              document.getElementById("goal-text").textContent = jsCoq.goals();
            }
        }
    };

    // Back...
    Editor.prototype.popStatement = function() {

        if (this.statements.length <= 1)
            return false;

        // Clear the mark from the last statement.
        var stm = this.statements.pop();
        stm.mark.clear();

        // Drop the last sid
        jsCoq.sid.pop();
        // And tell coq to go back to the old state.
        jsCoq.edit(jsCoq.sid.last());

        // Update goals
        document.getElementById("goal-text").textContent = jsCoq.goals();
        return true;
    };

    // This is an event, shouldn't it return true?
    Editor.prototype.onCMChange = function(evt) {

        var doc   = this._editor.getDoc();
        var marks = doc.findMarksAt(doc.getCursor());

        if (this.statements.length <= 1)
            return;

        if (marks.length === 1) {
            for (var i = this.statements.length - 1 ; i >= marks[0].stm.position ; i-- ) {
                this.popStatement();
            }
        }
    };

    var IDGen = function() {
        this.id = 1;
    };

    IDGen.prototype.next = function() {
        this.id--;
        return this.id;
    };

    var Statement = function(start, end, text){
        // start, end: {line: l, ch: c}
        this.start = start;
        this.end = end;
        this.text = text;
        this.id = 0;
        this.mark = undefined;
    };
}());
