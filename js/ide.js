var IDELayout;
var Editor;

(function(){
    var SEP_SIZE = 6;
    
    IDELayout = function() {
        this.left_panel = document.getElementById('left-panel');
        this.toolsbar = document.getElementById('toolsbar');
        this.right_panel = document.getElementById('right-panel');
        this.script_panel = document.getElementById('script-panel');
        this.goal_panel = document.getElementById('goal-panel');
        this.message_panel = document.getElementById('message-panel');
        this.vsep = document.getElementById('vsep');
        this.hsep = document.getElementById('hsep');
        this.editor = new Editor('coq', this.script_panel.getElementsByTagName('textarea')[0]);

        var self = this;
        this.toolsbar.addEventListener('click', function(evt){self.toolbarClickHandler(evt);});
        window.addEventListener('load', function(evt){self.fitToScreen(evt);});
        window.addEventListener('resize', function(evt){self.fitToScreen(evt);});
    };
    
    IDELayout.prototype.fitToScreen = function(evt) {
        var height = window.innerHeight;
        var width = window.innerWidth;
        var panel_width = (width - SEP_SIZE) / 2;

        this.left_panel.style.height = height + 'px';
        this.left_panel.style.width = panel_width + 'px';

        this.right_panel.style.height = height + 'px';
        this.right_panel.style.width = panel_width + 'px';
        
        this.vsep.style.height = height + 'px';
        this.vsep.style.left = panel_width + 'px';
        this.vsep.style.width = SEP_SIZE + 'px';
        
        this.goal_panel.style.height =
            this.message_panel.style.height = (height - SEP_SIZE) / 2 + 'px';
        this.message_panel.style.marginTop = SEP_SIZE + 'px';
        
        this.hsep.style.height = SEP_SIZE + 'px';
        this.hsep.style.width = width/2 + 'px';

        this.left_panel.getElementsByClassName('CodeMirror')[0].style.height = height + 'px';
    };
    
    IDELayout.prototype.toolbarClickHandler = function(evt) {
        var target = evt.target;
        switch (target.name) {
            case 'ceiling' :
                break;
            case 'floor' :
                break;
            case 'up' :
                break;
            case 'down' :
                this.editor.eatNextStatement();
                break;
        }
        console.log(target);
    };
    
    Editor = function(name, element) {
        this.idgen = new IDGen();
        this.statements = [];
        this._editor = CodeMirror.fromTextArea(element,
            {mode: {name: "coq",
                    version: 3,
                    singleLineStringErrors: false},
             lineNumbers: true,
             indentUnit: 4,
             matchBrackets: true
            }
        );
    };
    
    Editor.prototype.eatNextStatement = function() {
        var doc = this._editor.getDoc();
        var start = {line : 0, ch : 0};
        if (this.statements.length) {
            var lastStm = this.statements[this.statements.length - 1];
            start = lastStm.end;
        }
        
        var start_ch = start.ch;
        var text, handle, end_ch;
        for (var i=start.line ; i<doc.lineCount() ; i++) {
            handle = doc.getLineHandle(i);
            text = handle.text.slice(start_ch);
            if(text.indexOf('.') !== -1) {
                end_ch = start_ch + text.indexOf('.') + 1;
                break;
            }
            start_ch = 0;
        }

        var stm = new Statement(start,
                                {line : handle.lineNo(),
                                 ch   : end_ch}
                               );
        stm.id = this.idgen.next();
        this.statements.push(stm);
        this.coqEval(stm);
    };
    
    Editor.prototype.coqEval = function(stm) {
        var doc = this._editor.getDoc();
        // TODO: call coq here
        var mark = doc.markText(stm.start, stm.end, {className : 'coq-eval-ok'});
        stm.mark = mark;
    };
    
    var IDGen = function() {
        this.id = 1;
    };
    
    IDGen.prototype.next = function() {
        this.id--;
        return this.id;
    };
    
    var Statement = function(start, end){
        // start, end: {line: l, ch: c}
        this.start = start;
        this.end = end;
        this.id = 0;
        this.mark = undefined;
    };
}());