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
        this.special_patterns = [];
        this.className = 'markup';
    }
    
    applyToDocument() {
        for (let line = 0; line < this.cm.lineCount(); line++)
            this.applyToLine(line);
    }

    applyToLine(line) {
        this.clearFromLine(line);
        for (let tok of this.cm.getLineTokens(line)) {
            if (this.special_tokens.hasOwnProperty(tok.string)) {
                let lit = this.special_tokens[tok.string],
                    from = {line, ch: tok.start},
                    to = {line, ch: tok.end};
                this.markText(from, to, 
                        {replacedWith: this.mkSymbol(lit), className: this.className, 
                         handleMouseEvents: true,
                         owner: this});
            }
            for (let pat of this.special_patterns) {
                let mo = pat.re.exec(tok.string);
                if (mo) {
                    for (let opts of pat.make(mo)) {
                        var from = {line, ch: tok.start + mo.index + opts.from},
                            to = {line, ch: tok.start + mo.index + opts.to};
                        this.markText(from, to, 
                            {className: [this.className].concat(opts.className ? [opts.className] : []).join(' '), 
                             replacedWith: opts.replacedWith,
                             handleMouseEvents: true,
                             owner: this});
                    }
                }
            }
        }
    }

    clearFromLine(line) {
        var from = {line, ch: 0},
            to = {line, ch: this.cm.getLine(line).length};
        for (let mark of this.cm.findMarks(from, to, m => m.owner == this))
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
var vocab = {
    lemmas: [],
    tactics: [
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
  ]};

var kinds = {lemmas: 'lemma', tactics: 'tactic'};


/**
 * Hints for lemma names and tactics.
 */
class AutoComplete {

    constructor() {
        this.vocab = vocab;
        this.kinds = kinds;

        this.max_matches = 100;  // threshold to prevent UI slowdown

        this.extraKeys = {
            Alt: (cm) => { this.hintZoom(cm); }
        };
    }

    lemmaHint(cm, options) { return this.hint(cm, options, 'lemmas'); }
    tacticHint(cm, options) { return this.hint(cm, options, 'tactics'); }

    hint(cm, _options, family) {
        var cur = cm.getCursor(), 
            [token, token_start, token_end] = this._adjustToken(cur, cm.getTokenAt(cur)),
            match = /^\w/.exec(token.string) ? token.string : undefined;
    
        // Build completion list
        var matching = match ? this._matches(match, family) : [];

        if (matching.length === 0) {
            cm.closeHint();
            return;
        }

        for (let m of matching) {
            m.render = (el, self, data) => this._render(el, data, match, cm)
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
     * Hint completion is invoked when typing an identifier token of two or more
     * characters.
     * @param {CodeMirror} cm editor instance
     * @param {ChangeEvent} evt document modification object
     */
    senseContext(cm, evt) {
        if (!cm.state.completionActive && this._isInsertAtCursor(cm, evt)) {
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

    _isInsertAtCursor(cm, evt) {
        var cur = cm.getCursor();
        return (evt.origin === '+input' && 
                cur.line === evt.to.line && cur.ch === evt.to.ch + 1);
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

    _matches(match, family) {
        var matching = [], kind = this.kinds[family];
    
        for (let entry of this.vocab[family]) {
            var name = entry.label || entry;
            if ( name.indexOf(match) > -1 ) {
                matching.push({
                    text: name, label: name, kind, prefix: entry.prefix || []
                });
                if (matching.length > this.max_matches) break;
            }
        }

        matching.sort((x, y) => (x.text.indexOf(match) - y.text.indexOf(match)) ||
                                (x.text.length - y.text.length));
    
        return matching;
    }

    _render(el, data, match, cm) {
        var first = true,
            bold = $('<b>').text(match),
            pkg = data.prefix && data.prefix.length ? data.prefix.join('.') : null;

        for (let part of data.text.split(match)) {
            if (!first) $(el).append(bold.clone());
            $(el).append(document.createTextNode(part));
            first = false;
        }
        if (pkg)
            $(el).append(
                $('<div>').addClass('hint-package').text(pkg)
            );
        // Make element active on hover (mostly in order to show tips)
        $(el).mouseenter(() => {
            var cA = cm.state.completionActive;
            if (cA && cA.widget)
                cA.widget.changeActive($(el).index());
        });
    }
}

/**
 * Main CompanyCoq entry point.
 * - Creates markup and configures it with specific tokens.
 * - Registers contextual hint trigger.
 */
class CompanyCoq {

    constructor() {
        this.special_tokens = {
            '->': '→', '<-': '←', '=>': '⇒', '|-': '⊢',
            '/\\': '∧', '\\/': '∨',
            'fun': 'λ', 'forall': '∀', 'exists': '∃', 
            'Real': 'ℝ', 'nat': 'ℕ'
        };
        this.special_patterns = [
            {re: /[^\d_](\d+)$/,   make: (mo) => [{from: 1, to: mo[0].length, className: 'company-coq-sub'}]},
            {re: /(__)([^_].*)$/,  make: (mo) => [{from: 0, to: 2, replacedWith: $('<span>')[0]},
                                                  {from: 2, to: mo[0].length, className: 'company-coq-sub'}]}
        ];

        this.completion = new AutoComplete();
    }

    attach(cm) {
        this.cm = cm;
        this.markup = new Markup(cm);
        this.markup.special_tokens = this.special_tokens;
        this.markup.special_patterns = this.special_patterns;
        this.markup.className = 'company-coq';
        this.markup.applyToDocument();

        cm.on('change', () => this.markup.applyToDocument());
        cm.on('change', (cm, evt) => this.completion.senseContext(cm, evt));
        cm.on('cursorActivity', (cm, evt) => this.observeIdentifier(cm));
        return this;
    }

    observeIdentifier(cm) {
        var cur0 = cm.getCursor(), cur1 = {line: cur0.line, ch: cur0.ch + 1};
        var tok = cm.getTokenAt(cur0);

        if (tok.type != 'variable') tok = cm.getTokenAt(cur1);

        var entries;

        if (tok && tok.type == 'variable' &&
            (entries = CompanyCoq._vocab_index[tok.string])) {
            CodeMirror.signal(cm, 'hintEnter', tok, entries);
        }
        else
            CodeMirror.signal(cm, 'hintOut', tok, entries);
    }

    static loadSymbols(symbols, replace_existing=false) {
        for (let key in CompanyCoq.vocab) {
            if (symbols[key]) {
                if (replace_existing) CompanyCoq.vocab[key].splice(0);
                CompanyCoq.vocab[key].push(...symbols[key]);
                // It is important to modify in-place to also affect CodeMirror
                //  instances that were already created... :\
            }
        }
        CompanyCoq._makeVocabIndex();
    }

    static _makeVocabIndex(vocab = CompanyCoq.vocab) {
        var kinds = CompanyCoq.kinds,
            vindex = {};
        
        for (let key in vocab) {
            for (let symb of vocab[key]) {
                if (typeof symb === 'object')
                    symb.kind = symb.kind || kinds[key];
                (vindex[symb.label] = vindex[symb.label] || []).push(symb);
            }
        }
        CompanyCoq._vocab_index = vindex;
    }

    static init() {
        CompanyCoq.vocab = vocab;
        CompanyCoq.kinds = kinds;
        CodeMirror.CompanyCoq = CompanyCoq;

        CompanyCoq._makeVocabIndex();

        CodeMirror.defineInitHook(cm => {
            if (cm.options.mode['company-coq'])
                cm.company_coq = new CompanyCoq().attach(cm);
        });
    }
}


/* Register addon */
CompanyCoq.init();


});