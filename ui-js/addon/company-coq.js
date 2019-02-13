/************************************************************************/
/* company-coq addon to coq-mode, a CodeMirror mode for the Coq Proof   */
/*   Assistant.                                                         */
/*                                                                      */
/* Inspired by company-coq [https://github.com/cpitclaudel/company-coq] */
/* by Clément Pit-Claudel, which is a minor mode for Emacs.             */
/*                                                                      */
/* Features:                                                            */
/*  - Prettification of symbols such as '->' and 'forall' via their     */
/*    Unicode counterparts.                                             */
/*  - Auto-completion of identifier names: tactics and lemmas in proof  */
/*    mode, constants in Gallina terms (the latter is not implemented   */
/*    of yet).                                                          */
/************************************************************************/


(function(mod) {
    if (typeof exports == "object" && typeof module == "object") // CommonJS
        mod(require("codemirror"));
    else if (typeof define == "function" && define.amd) // AMD
        define(["codemirror"], mod);
    else // Plain browser env
        mod(CodeMirror);
})(function(CodeMirror) {
"use strict";

var Pos = CodeMirror.Pos;

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

// Builtin tactics are copied from coq-mode.
// TODO: order tactics most common first rather than alphabetically.
var tactics = [
    'after', 'apply', 'assert', 'auto', 'autorewrite',
    'case', 'change', 'clear', 'compute', 'congruence', 'constructor',
    'congr', 'cut', 'cutrewrite',
    'dependent', 'destruct',
    'eapply', 'eassumption', 'eauto', 'econstructor', 'elim', 'exists',
    'field', 'firstorder', 'fold', 'fourier',
    'generalize',
    'have', 'hnf',
    'induction', 'injection', 'instantiate', 'intro', 'intros', 'inversion',
    'left',
    'move',
    'pattern', 'pose',
    'refine', 'remember', 'rename', 'repeat', 'replace', 'revert', 'rewrite',
    'right', 'ring',
    'set', 'simpl', 'specialize', 'split', 'subst', 'suff', 'symmetry',
    'transitivity', 'trivial', 'try',
    'unfold', 'unlock', 'using',
    'vm_compute',
    'where', 'wlog',
    /* Terminators */
    'assumption',
    'by',
    'contradiction',
    'discriminate',
    'easy',
    'exact',
    'now',
    'omega',
    'reflexivity',
    'tauto'
  ];

/**
 * Hints for lemma names and tactics.
 */
class AutoComplete {

    constructor() {
        // TODO: Allow to be configured externally
        this.vocab = {
            lemmas: ["andb_prop", "andb_true_intro", "and_iff_compat_l", "eq_sym", "not_eq_sym"],
            tactics: tactics
        };

        this.extraKeys = {
            Alt: (cm) => { this.hintZoom(cm); }
        };
    }

    lemmaHint(cm, options) { return this.hint(cm, options, 'lemmas', 'lemma'); }
    tacticHint(cm, options) { return this.hint(cm, options, 'tactics', 'tactic'); }

    hint(cm, _options, family, kind) {
            var cur = cm.getCursor(), 
            [token, token_start, token_end] = this._adjustToken(cur, cm.getTokenAt(cur)),
            match = /^\w/.exec(token.string) ? token.string : "";
    
        // Build completion list
        var matching = this._matches(match, family, kind);

        if (matching.length === 0) {
            cm.closeHint();
            return;
        }
    
        var data = { list: matching, from: token_start, to: token_end };
    
        // Emit 'hintHover' to allow context-sensitive info to be displayed by the IDE
        CodeMirror.on(data, "select",
            completion => CodeMirror.signal(cm, 'hintHover', completion));
    
        return data;
    }

    hintZoom(cm) {
        var cA = cm.state.completionActive;
        if (cA && cA.data && cA.widget) {
            // Emit 'hintZoom' to allow context-sensitive info to be displayed by the IDE
            var completion = cA.data.list[cA.widget.selectedHint];
            if (completion)
                CodeMirror.signal(cm, 'hintZoom', completion);
        }          
    }

    /**
     * Determines what kind of hint, if any, should be displayed when the
     * document is being edited.
     * Called on 'change' event; relies on coq-mode to recover context.
     * @param {CodeMirror} cm editor instance
     * @param {ChangeEvent} evt document modification object
     */
    senseContext(cm, evt) {
        if (evt.origin === '+input' && !cm.state.completionActive) {
            var cur = cm.getCursor(), token = cm.getTokenAt(cur),
                is_head = token.state.is_head,
                kind = token.state.sentence_kind;

            if ((is_head || kind === 'tactic' || kind === 'terminator') && 
                /^[a-zA-Z_]./.exec(token.string)) {
                var hint = is_head ? this.tacticHint : this.lemmaHint;
                cm.showHint({
                    hint: (cm, options) => hint.call(this, cm, options), 
                    completeSingle: false, 
                    extraKeys: this.extraKeys
                });
            }
        }
    }

    _adjustToken(cur, token) {
        if (token.end > cur.ch) {
            token.end = cur.ch;
            token.string = token.string.slice(0, cur.ch - token.start);
        }
      
        var tokenStart = Pos(cur.line, token.start),
            tokenEnd = Pos(cur.line, token.end);
      
        return [token, tokenStart, tokenEnd];
    }

    _matches(match, family, kind) {
        var matching = [];
    
        this.vocab[family].map( function(name) {
            if ( name.startsWith(match) ) {
                matching.push({text: name, kind: kind});
            }
        });
    
        return matching;
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

        this.completion = new AutoComplete();
    }

    attach(cm) {
        this.cm = cm;
        this.markup = new Markup(cm);
        this.markup.special_tokens = this.special_tokens;
        this.markup.className = 'company-coq';
        this.markup.applyToDocument();

        cm.on('change', () => this.markup.applyToDocument());
        cm.on('change', (cm, evt) => this.completion.senseContext(cm, evt));
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