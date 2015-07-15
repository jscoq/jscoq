var IDELayout;
(function(){
    var SEP_SIZE = 6;
    
    IDELayout = function() {
        this.left_panel = document.getElementById('left-panel');
        this.right_panel = document.getElementById('right-panel');
        this.script_panel = document.getElementById('script-panel');
        this.goal_panel = document.getElementById('goal-panel');
        this.message_panel = document.getElementById('message-panel');
        this.vsep = document.getElementById('vsep');
        this.hsep = document.getElementById('hsep');
        
        this.editor = CodeMirror.fromTextArea(this.script_panel.getElementsByTagName('textarea')[0], {
          mode: {name: "coq",
                 version: 3,
                 singleLineStringErrors: false},
          lineNumbers: true,
          indentUnit: 4,
          matchBrackets: true
        });
        
        var self = this;
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
}());