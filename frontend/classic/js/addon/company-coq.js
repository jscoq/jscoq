"use strict";
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

import CodeMirror from 'codemirror';
import $ from 'jquery';

var Pos = CodeMirror.Pos;

/**
 * Generic markup class.
 */
class Markup {

    constructor() {
        this.special_tokens = {};
        this.special_patterns = [];
        this.reserved = {tokens: [], types: ['comment']};
        this.className = 'markup';
    }
    
    attach(cm) {
        this.cm = cm;
        this.work = new WorkQueue(cm);
        this._on = {
            change: (cm, change_obj) => this._flush(change_obj),
            renderLine: (cm, ln, el) => this._rescan(ln)
        };
        cm.on('change', this._on.change);
        cm.on('renderLine', this._on.renderLine);
        this.applyToDocument();
    }

    detach() {
        this.clearAll();
        this.cm.off('change', this._on.change);
        this.cm.off('renderLine', this._on.renderLine);
    }

    applyToDocument() {
        for (let line = 0; line < this.cm.lineCount(); line++)
            this.applyToLine(line);
    }

    applyToLine(line) {
        this.clearFromLine(line);
        for (let tok of this.cm.getLineTokens(line)) {
            if ((this.reserved.types || []).includes(tok.type) ||
                (this.reserved.tokens || []).includes(tok.string)) continue;

            if (this.special_tokens.hasOwnProperty(tok.string)) {
                let lit = this.special_tokens[tok.string],
                    from = {line, ch: tok.start},
                    to = {line, ch: tok.end};
                this.markText(from, to, 
                        {replacedWith: this.mkSymbol(lit), className: this.className, 
                         handleMouseEvents: true,
                         owner: this});
            }
            else
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
                    break;
                }
            }
        }

        if (this.cm.display.maxLine && 
            this.cm.display.maxLine.lineNo() === line) this._maxLineHack();
    }

    clearAll() {
        for (let mark of this.cm.getAllMarks().filter(m => m.owner == this))
            mark.clear();
    }

    clearFromLine(line) {
        var from = {line, ch: 0},
            to = {line, ch: this.cm.getLine(line).length};
        for (let mark of this.cm.findMarks(from, to, m => m.owner == this))
            mark.clear();
    }

    _flush(change_obj) {
        for (let ln = change_obj.from.line; ln <= change_obj.to.line; ln++) {
            let lineh = this.cm.getLineHandle(ln);
            if (lineh) delete lineh._cc_recorded_styles;
        }

        if (this.cm.display.maxLine) {
            var mx = this.cm.display.maxLine.lineNo();
            if (mx >= change_obj.from.line && 
                mx <= change_obj.to.line) this._maxLineHack();
        }
    }

    _rescan(ln) {
        if (!ln.styles.equals(ln._cc_recorded_styles)) {
            ln._cc_recorded_styles = ln.styles;
            this.work.enqueue(() => this.applyToLine(ln.lineNo()));
        }
    }

    /**
     * (internal) This is needed to prevent a scrolling bug in CodeMirror 5.47.
     * CodeMirror saves the line that has the maximal length and updates the
     * sizerWidth to its total width.
     * Since replacedWith widgets effectively shrinks the line, this results in
     * underscrolling in many cases.
     */
    _maxLineHack() {
        var display = this.cm.display, curOp = this.cm.curOp;
        const CLEARANCE = 3;  /* space added to the right, in characters */
        display.maxLineChanged = false;
        if (curOp) {
            curOp.updateMaxLine = false;
            curOp.adjustWidthTo = (display.maxLine.text.length + CLEARANCE) *
                                  this.cm.defaultCharWidth();
            // Force the size using the actual character count.
            // May result in too much horizontal scrolling, but that is
            // better than the alternative.
        }
    }

    applyToDOM(dom) {
        this._forEachText(dom, text => this.applyToTextNode(text));
    }

    applyToTextNode(dom_text) {
        var markup = this.tokenize(dom_text.nodeValue).map(token =>
            this.applyToToken(token)).flatten();
        dom_text.replaceWith(...markup);
    }

    applyToToken(token) {
        if (this.special_tokens.hasOwnProperty(token)) {
            return [this.mkSymbol(this.special_tokens[token])];
        }
        else
        for (let pat of this.special_patterns) {
            let mo = pat.re.exec(token);
            if (mo) {
                var parts = [], idx = 0;
                // assumes opts are ordered by 'from'
                for (let opts of pat.make(mo)) {
                    var from = mo.index + opts.from,
                        to = mo.index + opts.to;
                    if (from > idx)
                        parts.push(token.substring(idx, from));
                    if (opts.replacedWith)
                        parts.push(opts.replacedWith)
                    else if (opts.className)
                        parts.push($('<span>').text(token.substring(from, to))
                            .addClass(opts.className)[0]);
                    idx = to;
                }
                return parts;
            }
        }
        
        return [token];
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

    tokenize(s) {
        return s.split(/(\w+)/).filter(s => s);
    }

    /**
     * Iterates the text nodes within a DOM element, allowing nodes to be replaced
     * while they are being iterated.
     * @param {Element} dom DOM element to traverse
     * @param {function} operation will be called for every descendant text node
     */
    _forEachText(dom, operation) {
        var i = document.createTreeWalker(dom, NodeFilter.SHOW_TEXT, null, false),
            cur = i.nextNode(), prev = cur;
        // Perform hand-over-hand scan so that iterator is not invalidated by 
        // changes to the DOM
        while (cur = i.nextNode()) {
            operation(prev);
            prev = cur;
        }
        if (prev) operation(prev);
    }

}

/**
 * Auxiliary class for Markup.
 * Bunches update tasks and performs them in a CodeMirror operation.
 */
class WorkQueue {
    constructor(cm) { this.cm = cm; this.tasks = []; this.primed = false; }
    enqueue(task) { 
        this.tasks.push(task); 
        if (!this.primed) this._engage();
    }
    clear() {
        this.tasks.splice();
    }
    _engage() {
        this.primed = true;
        requestAnimationFrame(() => this.cm.operation(() => {
            try     { for (let t of this.tasks) t(); }
            finally { this.primed = false; this.tasks = []; this._cleanup(); }
        }));
    }
    _cleanup() {
    }
}


var vocab_kinds = {lemmas: 'lemma', tactics: 'tactic', keywords: 'keyword'};


/**
 * Hints for lemma names and tactics.
 */
class AutoComplete {

    constructor() {
        this.vocab = {};
        this.kinds = vocab_kinds;

        this.max_matches = 100;  // threshold to prevent UI slowdown
    }

    attach(cm) {
        this.cm = cm;
        this._on = {change: (cm, evt) => this.senseContext(cm, evt)};
        cm.on('change', this._on.change);
    }

    detach() {
        this.cm.off('change', this._on.change);
    }

    lemmaHint(cm, options) { return this.hint(cm, options, ['keywords', 'lemmas']); }
    tacticHint(cm, options) { return this.hint(cm, options, ['tactics']); }

    hint(cm, _options, family) {
        var cur = cm.getCursor(), 
            [token, token_start, token_end] = this._adjustToken(cur, cm.getTokenAt(cur)),
            match = token.string.trim();
    
        // Build completion list
        var matching = this._matches(match, family);

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
     * Hint completion is invoked when typing an identifier token of three or
     * more characters.
     * @param {CodeMirror} cm editor instance
     * @param {ChangeEvent} evt document modification object
     *   (if omitted, shows hints unconditionally)
     */
    senseContext(cm, evt) {
        if (!evt || !cm.state.completionActive && this._isInsertAtCursor(cm, evt)) {
            var cur = cm.getCursor(), token = cm.getTokenAt(cur),
                is_head = token.state.is_head || token.state.begin_sentence,
                kind = token.state.sentence_kind;

            if (!evt || ((is_head || kind === 'tactic' || kind === 'terminator') &&
                         /^[a-zA-Z_]../.exec(token.string))) {
                var hint = is_head ? this.tacticHint : this.lemmaHint;
                requestAnimationFrame(() =>
                    cm.showHint({
                        hint: (cm, options) => hint.call(this, cm, options),
                        completeSingle: false
                    }));
            }
        }
    }

    /**
     * Called by 'showHint' on 'autocomplete' command.
     * (There is some overlap with senseContext functionality, but seems
     * unavoidable.)
     * @param {CodeMirror} cm editor instance
     * @param {object} options showHint options object
     */
    getCompletions(cm, options) {
        var cur = cm.getCursor(), token = cm.getTokenAt(cur),
            is_head = token.state.is_head || token.state.begin_sentence;

        var hint = is_head ? this.tacticHint : this.lemmaHint;
        return hint.call(this, cm, options);
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

    _matches(match, families) {
        var matching = []

        for (let family of families) {
            var kind = this.kinds[family];

            for (let scope of Object.values(this.vocab)) {
                for (let entry of scope[family] || []) {
                    var name = entry.label || entry;
                    if ( name.indexOf(match) > -1 ) {
                        matching.push({
                            text: name, label: name, kind, prefix: entry.prefix || []
                        });
                        if (matching.length > this.max_matches) break;
                    }
                }
            }
        }

        matching.sort((x, y) => (x.text.indexOf(match) - y.text.indexOf(match)) ||
                                (x.text.length - y.text.length) ||
                                (this._modulePref(x.prefix) - this._modulePref(y.prefix)));
    
        return matching;
    }

    /**
     * Some heuristic to make a reasonable order of the same symbol when it is
     * defined in different modules.
     * (lower is better)
     */
    _modulePref(mod) {
        return mod.length + mod.join('').length;
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
        // but only if the mouse is actually moved
        $(el).on('mousemove', () => {
            var cA = cm.state.completionActive;
            if (cA && cA.widget)
                cA.widget.changeActive($(el).index());
        });
    }
}

class ObserveIdentifier {

    constructor() {
        this.vocab = {};
        this._makeVocabIndex();
    }

    attach(cm) {
        this.cm = cm;
        this._on = {cursorActivity: (cm, evt) => this.underCursor(cm)};
        cm.on('cursorActivity', this._on.cursorActivity);
    }

    detach() {
        this.cm.off('cursorActivity', this._on.cursorActivity);
    }

    underCursor(cm) {
        var cur0 = cm.getCursor(), cur1 = {line: cur0.line, ch: cur0.ch + 1};
        var tok = cm.getTokenAt(cur0);

        if (tok.type != 'variable') tok = cm.getTokenAt(cur1);

        var entries;

        if (tok && tok.type == 'variable' &&
            (entries = this._vocab_index.get(tok.string))) {
            CodeMirror.signal(cm, 'hintEnter', tok, entries);
        }
        else
            CodeMirror.signal(cm, 'hintOut', tok, entries);
    }

    _makeVocabIndex(vocab = this.vocab) {
        var kinds = CompanyCoq.kinds,
            vindex = new Map;
        
        for (let scope of Object.values(vocab)) {
            for (let key in scope) {
                for (let symb of scope[key]) {
                    if (typeof symb === 'object')
                        symb.kind = symb.kind || kinds[key];
                    else
                        symb = {label: symb, kind: kinds[key]};
                    let vl = vindex.get(symb.label);
                    if (!vl) { vl = []; vindex.set(symb.label, vl); }
                    vl.push(symb);
                }
            }
        }
        this._vocab_index = vindex;
    }

}

/* -- Configuration Section -- */

const special_tokens = {
        '->': '→', '<-': '←', '<->': '↔', '>->': '↣', '=>': '⇒', '|-': '⊢',
        '/\\': '∧', '\\/': '∨',
        '<=': '≤', '>=': '≥', '<>': '≠',
        'fun': 'λ', 'forall': '∀', 'exists': '∃', 
        'Real': 'ℝ', 'nat': 'ℕ', 'Prop': 'ℙ'
    },
    index_sub =      (mo) => [{from: 1, to: mo[0].length, className: 'company-coq-sub'}],
    underscore_sub = (mo) => [{from: 0, to: 2, replacedWith: $('<span>')[0]},
                              {from: 2, to: mo[0].length, className: 'company-coq-sub'}],
    special_patterns = [
        {re: /[^\d_](\d+)$/,   make: index_sub},
        {re: /(__)([^_].*)$/,  make: underscore_sub}
    ],
    reserved = {
        tokens: ['Int31', 'Int63', 'Uint63', 'Ltac2', 'Utf8', 'Coq88', 'Coq89', 'Coq810'],
        types:  ['comment', 'tactic']
    };

// Builtin tactics are copied from coq-mode.
// TODO: order tactics most common first rather than alphabetically.
const vocab = {
    locals: {lemmas: [], tactics: []},  /* keep locals before globals */
    globals: {
        lemmas: [],
        tactics: [
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
            'tauto',
            /* Other tactics */
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
            'where', 'wlog'
        ],
        keywords: [
            'in', 'as', 'with'
        ]
    }
};

/* --                       -- */

/**
 * Main CompanyCoq entry point.
 * - Creates markup and configures it with specific tokens.
 * - Registers contextual hint trigger.
 */
class CompanyCoq {

    constructor() {
        this.markup = new Markup();
        this.completion = new AutoComplete();
        this.observe = ObserveIdentifier.instance;

        this.markup.special_tokens = special_tokens;
        this.markup.special_patterns = special_patterns;
        this.markup.reserved = reserved;
        this.markup.className = 'company-coq';

        this.completion.vocab = CompanyCoq.vocab;
    }

    attach(cm) {
        this.markup.attach(cm);
        this.completion.attach(cm);
        this.observe.attach(cm);

        return this;
    }

    detach() {
        this.markup.detach();
        this.completion.detach();
        this.observe.detach();

        return this;
    }

    static hint(cm, options) {
        if (cm.company_coq)
            return cm.company_coq.completion.getCompletions(cm, options);
    }

    static mkEmptyScope() {
        return { lemmas: [], tactics: [] };
    }

    static loadSymbols(symbols, scope, replace_existing=false) {
        var vocab = CompanyCoq.vocab[scope] = CompanyCoq.vocab[scope] || CompanyCoq.mkEmptyScope();

        for (let key in vocab) {
            if (symbols[key]) {
                if (replace_existing) vocab[key].splice(0);
                vocab[key].push(...symbols[key]);
                // It is important to modify in-place to also affect CodeMirror
                //  instances that were already created... :\
            }
        }

        ObserveIdentifier.instance._makeVocabIndex();
    }

    static init() {
        CompanyCoq.vocab = vocab;
        CompanyCoq.kinds = vocab_kinds;
        ObserveIdentifier.instance = new ObserveIdentifier(); // singleton
        ObserveIdentifier.instance.vocab = vocab;

        CodeMirror.defineInitHook(cm =>
            CompanyCoq.configure(cm, cm.options));

        CodeMirror.registerGlobalHelper("hint", "company-coq",
            (mode, cm) => mode.name === 'coq' && !!cm.company_coq, 
            CompanyCoq.hint);
    }

    static configure(cm, options) {
        switch (options.mode && options.mode['company-coq']) {
        case true:
            if (!cm.company_coq)
                cm.company_coq = new CompanyCoq().attach(cm);
            break;
        case false:
            if (cm.company_coq) {
                cm.company_coq.detach();
                cm.company_coq = undefined;
            }
            break;
        }
    }
}


/* Register addon */
CompanyCoq.init();

export { CompanyCoq }
