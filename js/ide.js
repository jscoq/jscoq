var JSCoqIDE;
var Editor;

(function(){
    "use strict";
    Array.prototype.last = function() { return this[this.length-1]; };

    JSCoqIDE = function() {

        this.buttons       = document.getElementById('buttons');
        this.script_panel  = document.getElementById('script-panel');
        this.goal_text     = document.getElementById("goal-text");
        this.message_panel = document.getElementById('message-panel');
        this.editor        = new Editor(this, this.script_panel.getElementsByTagName('textarea')[0]);

        window.addEventListener('load', evt => { this.onload(evt); } );
    };

    JSCoqIDE.prototype.onload = function(evt) {

        // XXX: make it a config parameter.
        var jscoq_mock     = true;

        // Load JsCoq
        var jscoqscript    = document.createElement('script');
        jscoqscript.type   = 'text/javascript';
        jscoqscript.src    = jscoq_mock ? 'coq-js/jsmock.js' : 'coq-js/jscoq.js';
        jscoqscript.onload = evt => { this.setupCoq(evt); };
        document.head.appendChild(jscoqscript);
    };


    JSCoqIDE.prototype.enable = function() {

        this.buttons.addEventListener('click', evt => { this.toolbarClickHandler(evt); } );
        this.buttons.style.display = 'table-cell';
        this.buttons.style.opacity = 1;
        this.editor.focus();
    };

    JSCoqIDE.prototype.addImg = function(src, width, line, ch) {

        var oImg = document.createElement("img");
        oImg.src = src;
        oImg.width = width;

        this.editor._editor.addWidget({line: line, ch:ch}, oImg, false);
    }

    JSCoqIDE.prototype.addh2 = function(text, width, line, ch) {

        var elem = document.createElement("h2");
        elem.textContent = text;

        this.editor._editor.addWidget({line: line, ch:ch}, elem, false);
    }

    JSCoqIDE.prototype.setupCoq = function() {

        jsCoq.onError = e => { this.editor.popStatement(true); };

        jsCoq.onLog   = e => {
            console.log("CoqLog: " + e.toString());

            // Hacks, we should refine...

            // Error msg.
            if (e.toString().indexOf("ErrorMsg:") != -1)
                // Sanitize
                this.addToQueryBuffer(e.toString().replace(/^.*ErrorMsg:/, ""));
            // User queries, usually in the query buffer
            else if (e.toString().indexOf("Msg:") != -1)
                this.addToQueryBuffer(e.toString().replace(/^.*Msg:/, ""));
        };

        jsCoq.onInit = e => {

            // Enable the IDE.
            document.getElementById("goal-text").textContent += "\n===> JsCoq filesystem initalized with success!";
            this.enable();
        };

        // Initial sid.
        jsCoq.sid = [];
        jsCoq.sid.push(jsCoq.init());

        this.goal_text.textContent = jsCoq.version() + "\nPlease wait for the libraries to load, thanks!";
    };

    JSCoqIDE.prototype.addToQueryBuffer = function(text) {

        var span = document.createElement('span');
        // Now Coq logs escaped pseudo-xml...
        span.innerHTML = text;
        this.message_panel.insertBefore(span, this.message_panel.firstChild);
    };

    JSCoqIDE.prototype.toolbarClickHandler = function(evt) {

        var target = evt.target;
        this.editor.focus();
        switch (target.name) {
            case 'to-cursor' :
                this.editor.eatStatementsToCursor();
                break;

            case 'up' :
                this.editor.popStatement(false);
                break;

            case 'down' :
                this.editor.eatNextStatement();
                break;
        }
    };

    JSCoqIDE.prototype._raiseButton = function(btn_name) {
        var btns = this.buttons.getElementsByTagName('img');
        for(var i=0 ; i<btns.length ; i++){
            if(btns[i].name == btn_name) {
                btns[i].dispatchEvent(new MouseEvent('click',
                                                     {'view': window,
                                                      'bubbles': true,
                                                      'cancelable' : true}));
                break;
            }
        }
    };

    Editor = function(ide, element) {
        this.ide = ide;
        this.idgen = new IDGen();

        // Statements holds the code already sent to Coq.
        this.statements = [];

        // CodeMirror.defineMathMode("coq+math", {name: "coq",
        //                                        underscoresBreakWords: false});

        this._editor = CodeMirror.fromTextArea(element,
            // {mode : {name : "coq+math",
            {mode : {name : "coq",
                     version: 3,
                     singleLineStringErrors : false
                   },
             lineNumbers   : true,
             indentUnit    : 4,
             matchBrackets : true,
             theme : 'blackboard'
            }
        );

        // CodeMirror.hookMath(this._editor, MathJax);
        // this._editor.renderAllMath();

        this._editor.on('change', function(evt){ self.onCMChange(evt); });
        this._editor.setOption("extraKeys",
            {
                "Ctrl-N":     () => { this.ide._raiseButton('down'); },
                "Ctrl-P":     () => { this.ide._raiseButton('up');   },
                "Ctrl-Enter": () => { tihs.ide._raiseButton('to-cursor'); }
            }
        );
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

    // Returns the next token after the one seen at position: {line:…, ch:…}
    // type_re: regexp to match token type.
    // The returned object is a CodeMirror token with an additional attribute 'line'.
    Editor.prototype.getNextToken = function(position, type_re) {
        var cm = this._editor;
        var linecount = cm.getDoc().lineCount();
        var token, next, ch, line;
        do {
            token = cm.getTokenAt(position);
            ch = token.end + 1;
            line = position.line;
            if (token.end === cm.getLine(line).length) {
                line++;
                ch = 0;
                if (line >= linecount)
                    return null;
            }
            next = cm.getTokenAt({line:line, ch:ch});
            next.line = line;
            position = {line:next.line, ch:next.end};
        } while(type_re && !(type_re.test(next.type)));
        return next;
    };

    // Send next statement to Coq.
    Editor.prototype.eatNextStatement = function() {

        var cm    = this._editor;
        var doc   = cm.getDoc();
        var start = {line : 0, ch : 0};

        // get last evaluated statement
        if (this.statements.length) {

            var lastStm = this.statements.last();
            start = lastStm.end;

            if (start.line === doc.lastLine() &&
                start.ch === doc.getLine(doc.lastLine()).length) {
                return null;
            }
        }

        var token = this.getNextToken(start, /statementend|bullet|brace/);
        if(!token) return null;

        var stm = new Statement(start,
                                {line : token.line,
                                 ch   : token.end},
                                doc.getRange({line : start.line, ch : start.ch},
                                             {line : token.line, ch : token.end}),
                                token.type === 'comment'
                               );

        // Add the statement to our list.
        stm.id = this.idgen.next();
        this.statements.push(stm);
        stm.position = this.statements.length - 1;

        // EG: The stm should gain eid and sid properties.

        // In fact, there are 3 states for a statement: new, parsed,
        // and executed/errored.
        this.coqEval(stm);
        return stm;
    };

    Editor.prototype.eatStatementsToCursor = function () {
        var cm     = this._editor;
        var doc    = cm.getDoc();
        var cursor = doc.getCursor();
        var marks  = doc.findMarksAt(cursor);
        var stm;
        if(marks.length) {
            // backward
            marks = doc.findMarksAt(cursor);
            for (var i = this.statements.length - 1 ; i >= marks[0].stm.position ; i-- ) {
                this.popStatement();
            }
        }
        else {
            // forward
            do {
                stm = this.eatNextStatement();
            } while(stm && (stm.end.line < cursor.line || stm.end.ch < cursor.ch));
        }
    };

    Editor.prototype.coqEval = function(stm) {

        // Mark the statement
        var doc  = this._editor.getDoc();

        // XXX: Quack!
        var mark;
        if(stm.is_comment) {
            mark = doc.markText(stm.start, stm.end, {className : 'coq-eval-ok'});
            mark.stm = stm;
            stm.mark = mark;
            return;
        }
        mark = doc.markText(stm.start, stm.end, {className : 'coq-eval-pending'});
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
        } else { // Parse/library loading error.
            // XXXX: Similar to popStatement but without sid handling.
            stm = this.statements.pop();

            stm.mark.clear();
            mark = doc.markText(stm.start, stm.end, {className : 'coq-eval-failed'});
            mark.stm = stm;
            stm.mark = mark;
            this.errorMark = stm.mark;
        }
    };

    // Back...
    Editor.prototype.popStatement = function(is_error) {

        // This is very important, we cannot unload the prelude.
        if (this.statements.length <= 1)
            return null;

        // Clear the last errorMark
        if(this.errorMark) {
            this.errorMark.clear();
            this.errorMark = null;
        }

        // Clear the mark from the last statement.
        var stm = this.statements.pop();
        stm.mark.clear();

        // Mark errors as failed... We need a pending stack for this to work fine...
        if(is_error) {
            var doc  = this._editor.getDoc();
            var mark = doc.markText(stm.start, stm.end, {className : 'coq-eval-failed'});
            mark.stm = stm;
            stm.mark = mark;
            this.errorMark = mark;
        }

        if(stm.is_comment)
            return stm;

        // Drop the last sid
        jsCoq.sid.pop();
        // And tell coq to go back to the old state.
        jsCoq.edit(jsCoq.sid.last());

        // Update goals
        document.getElementById("goal-text").textContent = jsCoq.goals();
        return stm;
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

    Editor.prototype.focus = function() {
        this._editor.focus();
    };

    var IDGen = function() {
        this.id = 1;
    };

    IDGen.prototype.next = function() {
        this.id--;
        return this.id;
    };

    var Statement = function(start, end, text, is_comment) {
        // start, end: {line: l, ch: c}
        this.start = start;
        this.end = end;
        this.text = text;
        this.is_comment = is_comment;
        this.id = 0;
        this.mark = undefined;
    };
}());

// Local Variables:
// js-indent-level: 4
// End:
