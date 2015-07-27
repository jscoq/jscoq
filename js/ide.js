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
        var start = 0;
        if (this.statements.length) {
            var lastStm = this.statements[this.statements.length - 1];
            start = lastStm.end + 1;
        }
        
        var stm_lines = [], line, handle;
        for (var i=start ; i<doc.lineCount() ; i++) {
            handle = doc.getLineHandle(i);
            stm_lines.push(handle);
            line = handle.text.trim();
            if (line.charAt(line.length - 1) === '.')
                break;
        }
        var stm = new Statement(start, handle.lineNo());
        this.statements.push(stm);
        this.coqEval(stm);
    };
    
    Editor.prototype.coqEval = function(stm) {
        var doc = this._editor.getDoc();
        doc.markText(
            {line : stm.start, ch : 0},
            {line : stm.end + 1, ch : 0},
            {className : 'coq-eval-ok'}
        );
    };
    
    var IDGen = function() {
        this.id = 1;
    };
    
    IDGen.prototype.next = function() {
        this.id--;
        return this.id;
    };
    
    var Statement = function(start, end){
        this.start = start;
        this.end = end;
    };
}());