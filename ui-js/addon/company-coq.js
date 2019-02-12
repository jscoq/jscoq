

(function(mod) {
    if (typeof exports == "object" && typeof module == "object") // CommonJS
        mod(require("../../lib/codemirror"));
    else if (typeof define == "function" && define.amd) // AMD
        define(["../../lib/codemirror"], mod);
    else // Plain browser env
        mod(CodeMirror);
})(function(CodeMirror) {
"use strict";

/**
 * Generic markup class.
 */
class Markup {

    constructor(cm) {
        this.cm = cm;
        this.special_tokens = {};
        this.className = 'markup';
    }
    
    applyToDocument() {
        for (let line = 0; line < this.cm.lineCount(); line++)
            this.applyToLine(line);
    }

    applyToLine(line) {
        this.clearFromLine(line);
        for (let tok of this.cm.getLineTokens(line)) {
            let lit = this.special_tokens[tok.string]
            if (lit) {
                var from = {line, ch: tok.start},
                    to = {line, ch: tok.end};
                this.markText(from, to, 
                        {replacedWith: this.mkSymbol(lit), className: this.className, 
                         handleMouseEvents: true});
            }
        }
    }

    clearFromLine(line) {
        var from = {line, ch: 0},
            to = {line, ch: this.cm.getLine(line).length};
        for (let mark of this.cm.findMarks(from, to, m => m.className == this.className))
            mark.clear();
    }

    markText(from, to, options) {
        var existing_marks = this.cm.findMarksAt(from),
            mark = this.cm.markText(from, to, options);
        // Respect className and attributes of existing marks
        if (mark.widgetNode) {
            for (let em of existing_marks) {
                if (em.className) $(mark.widgetNode).addClass(em.className);
                for (let attrName in em.attributes || {})
                    $(mark.widgetNode).attr(attrName, em.attributes[attrName]);
            }
        }
        return mark;
    }

    mkSymbol(lit) {
        return document.createTextNode(lit);
    }

}

/**
 * Main CompanyCoq entry point.
 * - Creates markup and configures it with specific tokens.
 */
class CompanyCoq {

    constructor() {
        this.special_tokens = {
            '->': '→', '<-': '←', '=>': '⇒', '|-': '⊢',
            '/\\': '∧', '\\/': '∨',
            'fun': 'λ', 'forall': '∀', 'exists': '∃', 
            'Real': 'ℝ', 'nat': 'ℕ'
        };
    }

    attach(cm) {
        this.cm = cm;
        this.markup = new Markup(cm);
        this.markup.special_tokens = this.special_tokens;
        this.markup.className = 'company-coq';
        this.markup.applyToDocument();
        
        cm.on('change', () => this.markup.applyToDocument());
        return this;
    }

    static init() {
        CodeMirror.defineInitHook(cm => {
            if (cm.options.mode['company-coq'])
                cm.company_coq = new CompanyCoq().attach(cm);
        });
    }
}


/* Register addon */
CompanyCoq.init();


});