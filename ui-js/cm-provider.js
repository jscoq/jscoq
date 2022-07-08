"use strict";

class CmSentence {

    constructor(start, end, text, flags) {
        // start, end: {line: number, ch: number}
        // flags: {is_comment: bool, is_hidden: bool}
        this.start = start;
        this.end   = end;
        this.text  = text;
        this.mark  = undefined;
        this.flags = flags || {};
        this.feedback = [];
        this.action = undefined;
    }

}

// A CodeMirror-based Provider of coq statements.
class CmCoqProvider {

    constructor(element, options, replace) {

        this.constructor._config();

        var cmOpts =
            { mode : { name : "coq",
                       version: 4,
                       singleLineStringErrors : false
                     },
              lineNumbers       : true,
              indentUnit        : 2,
              tabSize           : 2,
              indentWithTabs    : false,
              matchBrackets     : true,
              styleSelectedText : true,
              dragDrop          : false, /* handled by CoqManager */
              keyMap            : "jscoq",
              className         : "jscoq"
            };

        if (options)
            copyOptions(options, cmOpts);
        
        var makeHidden = $(element).is(':hidden') ||
            /* corner case: a div with a single hidden child is considered hidden */
            element.children.length == 1 && $(element.children[0]).is(':hidden');

        if (element.tagName === 'TEXTAREA') {
            /* workaround: `value` sometimes gets messed up after forward/backwarn nav in Chrome */
            element.value ||= element.textContent;
            this.editor = CodeMirror.fromTextArea(element, cmOpts);
            replace = true;
        } else {
            this.editor = this.createEditor(element, cmOpts, replace);
        }

        this.editor.contentDOM.addEventListener('focus', () => this.onFocus());

        //if (replace) this.editor.addKeyMap('jscoq-snippet');

        this.filename = element.getAttribute('data-filename');
        this.autosave_interval = 20000 /*ms*/;

        if (this.filename) { this.openLocal(); this.startAutoSave(); }
        return;

        // Event handlers (to be overridden by ProviderContainer)
        this.onFocus = () => {};
        this.onInvalidate = (mark) => {};
        this.onMouseEnter = (stm, ev) => {};
        this.onMouseLeave = (stm, ev) => {};
        this.onTipHover = (entries, zoom) => {};
        this.onTipOut = () => {};
        this.onResize = (lineCount) => {};
        this.onAction = (action) => {};

        this.editor.on('beforeChange', (cm, evt) => this.onCMChange(cm, evt) );

        this.editor.on('cursorActivity', (cm) => 
            cm.operation(() => this._adjustWidgetsInSelection()));

        this.trackLineCount();

        // Handle mouse hover events
        var editor_element = $(this.editor.getWrapperElement());
        editor_element.on('mousemove', ev => this.onCMMouseMove(ev));
        editor_element.on('mouseleave', ev => this.onCMMouseLeave(ev));
        if (makeHidden && !editor_element.is(':hidden'))
            editor_element.css({display: "none"});

        // Some hack to prevent CodeMirror from consuming PageUp/PageDn
        if (replace) pageUpDownOverride(editor_element[0]);

        this._keyHandler = this.keyHandler.bind(this);
        this._key_bound = false;

        this.hover = [];

        // Handle hint events
        this.editor.on('hintHover',     completion     => this.onTipHover([completion], false));
        this.editor.on('hintZoom',      completion     => this.onTipHover([completion], true));
        this.editor.on('hintEnter',     (tok, entries) => this.onTipHover(entries, false));
        this.editor.on('hintOut',       ()             => this.onTipOut());
        this.editor.on('endCompletion', cm             => this.onTipOut());
    }

    createEditor(element, opts, replace) {
        var text = replace && $(element).text(),
            doc = this.createDoc(''),
            div = document.createElement('div'),
            editor = new cm6.EditorViewWithBenefits({parent: div, state: doc});
        div.classList.add('jscoq', 'cm-container');
        if (replace) {
            editor.setValue(Deprettify.cleanup(text));
            element.replaceWith(div);
        }
        else element.append(div);
        return editor;
    }

    createDoc(text) {
        return cm6.EditorState.create({doc: text, extensions: cm6.setup()});
    }

    configure(options) {
        if (options.theme) {
            this.editor.setOption('theme', options.theme);
        }
        CodeMirror.CompanyCoq.configure(this.editor, options);
    }

    trackLineCount() {
        this.lineCount = this.editor.lineCount();
        this.editor.on('change', ev => {
            let lineCount = this.editor.lineCount();
            if (lineCount != this.lineCount)
                this.onResize(this.lineCount = lineCount);
        });
    }

    focus() {
        this.editor.focus();
        /*
        var dialog_input = this.editor.getWrapperElement()
            .querySelector('.CodeMirror-dialog');
        // If a dialog is open, editor.focus() will close it,
        // leading to poor UX.
        if (!dialog_input) this.editor.focus();*/
    }

    isHidden() {
        return $(this.editor.contentDOM).is(':hidden');
    }

    // If prev == null then get the first.
    getNext(prev, until) {

        var pos = prev ? this.editor.posToOffset(prev.end) : 0,
            sc = this.editor.syntaxTree().cursorAt(pos, -1),
            until = until ? this.editor.posToOffset(until) : undefined;

        while (sc.next()) {
            if (sc.name === 'Sentence' && sc.node.from >= pos) break;
        }

        if (sc?.node && sc.name === 'Sentence') {
            let {from, to} = sc.node;
            if (until !== undefined && from >= until) return null;
            return new CmSentence(this.editor.offsetToPos(from), this.editor.offsetToPos(to),
                this.editor.state.sliceDoc(from, to),
                {is_comment: false /* @todo */, is_hidden: this.isHidden()});
        }
        else
            return null;

        /**
        var doc = this.editor.getState(),
            start = prev ? prev.end : {line : 0, ch : 0};

        if (until && this.onlySpacesBetween(start, until))
            return null;

        // small DFA that scans either a comment block or a statement
        const delim = ['statementend', 'coq-bullet', 'brace'];
        var state = 0, upto;
        dfa: for (let cur of this.iterTokens(start)) {
            switch (state) {
            case 0: state = cur.type === 'comment' ? 2 : 1; /* fallthrough *
            case 1: upto = cur; if (delim.includes(cur.type)) break dfa; break;
            case 2: if (cur.type !== 'comment') break dfa; upto = cur; break;
            }
        }

        if (!upto) return null; // EOF

        var end = {line: upto.line, ch: upto.end};

        return new CmSentence(start, end, doc.getRange(start, end),
            {is_comment: state == 2, is_hidden: this.isHidden()});
        */
    }

    /**
     * Gets sentence at current cursor location
     */
    getAtPoint() {
        let pos = this.editor.getCursorOffset(),
            iter = this.editor.state.field(cm6.markField).iter(pos);

        if (iter.value && iter.from <= pos)
            return iter.value.spec.id;
        else
            return undefined;
    }

    /** 
     * Mark a sentence with status ∈ {clear, processing, error, ok}.
     * Optionally underline a subset of it with a squiggly error indicator.
     */
    mark(stm, status, loc_focus) {
        let effects = [];
        if (stm.mark) {
            effects.push(cm6.clearMark.of({obj: stm}));
            stm.mark = undefined;
        }

        switch (status) {
        case "clear":
            break;
        case "processing":
            effects.push(this.markWithClass(stm, 'coq-eval-pending'));
            break;
        case "error":
            effects.push(this.markWithClass(stm, 'coq-eval-failed'));
            /* @todo
            if (loc_focus) {
                let foc = this.squiggle(stm, loc_focus, 'coq-squiggle');
                if (foc) this.editor.setCursor(foc.find().to);
            }
            else */ {
                this.editor.setCursor(stm.end);
            }
            break;
        case "ok":
            effects.push(this.markWithClass(stm, 'coq-eval-ok'));
            break;
        }

        this.editor.dispatch({effects});
    }

    highlight(stm, flag) {
        if (stm.mark && stm.coq_sid) {
            var spans = $(this.editor.getWrapperElement())
                        .find(`[data-coq-sid=${stm.coq_sid}]`),
                c = 'coq-highlight';
            /* Update the spans directly to avoid having to destroy and     */
            /* re-create the spans.                                         */
            /* (re-creating elements under cursor messes with mouse events) */
            if (flag) spans.addClass(c); 
            else      spans.removeClass(c);
            stm.mark.className =
                stm.mark.className.replace(/( coq-highlight)?$/, flag ? ' coq-highlight' : '');
        }
    }

    squiggle(stm, loc, className) {
        var pos = this._subregion(stm, loc);
        if (pos)
            return this.markSubordinate(stm, pos, className);
    }

    /**
     * Removes all sentence marks
     */
    retract() {
        for (let mark of this.editor.getAllMarks()) {
            if (mark.stm) {
                this.mark(mark.stm, 'clear');
            }
        }
    }

    markWithClass(stm, className) {
        stm.mark = {className};

        return cm6.addMark.of({
            from: this.editor.posToOffset(stm.start),
            to: this.editor.posToOffset(stm.end),
            class: className,
            obj: stm,
            attrs: stm.coq_sid ? {coq_sid: stm.coq_sid} : undefined
        });

        //this._markWidgetsAsWell(start, end, mark);
    }

    markSubordinate(stm, pos, className) {
        var doc = this.editor.getDoc(),
            {start, end} = pos;

        var mark = 
            doc.markText(start, end, {className: className});

        this._markWidgetsAsWell(start, end, mark);

        stm.mark.on('clear', () => mark.clear());
        return mark;
    }

    _subregion(stm, loc) {
        // Offsets are in bytes :/
        var stmBytes = new TextEncoder().encode(stm.text),
            td = new TextDecoder(),
            bytesToChars = (i) => td.decode(stmBytes.slice(0, i)).length,
            bp = bytesToChars(loc.bp), ep = bytesToChars(loc.ep);

        var doc = this.editor.getDoc(),
            idx = doc.indexFromPos(stm.start), end = doc.indexFromPos(stm.end);

        if (bp <= loc.ep && idx + ep <= end)
            return {start: doc.posFromIndex(idx + bp),
                    end:   doc.posFromIndex(idx + ep)}
    }

    /**
     * Hack to apply MarkedSpan CSS class formatting and attributes to widgets
     * within mark boundaries as well. 
     * (This is not handled by the native CodeMirror#markText.)
     */
    _markWidgetsAsWell(start, end, mark) {
        var classNames = mark.className.split(/ +/);
        var attrs = mark.attributes || {};
        for (let w of this.editor.findMarks(start, end, x => x.widgetNode)) {
            for (let cn of classNames)
                w.widgetNode.classList.add(cn);
            for (let attr in attrs)
                w.widgetNode.setAttribute(attr, attrs[attr]);
        }
    }

    /** 
     * Hack contd: negates effects of _markWidgetsAsWell when mark is cleared.
     */
    _unmarkWidgets(start, end) {
        for (let w of this.editor.findMarks(start, end, x => x.widgetNode)) {
            for (let cn of [...w.widgetNode.classList]) {
                if (/^coq-/.exec(cn))
                    w.widgetNode.classList.remove(cn);
            }
            for (let attr of [...w.widgetNode.attributes]) {
                if (/^data-coq-/.exec(attr.name))
                    w.widgetNode.removeAttributeNode(attr);
            }
        }
    }

    /**
     * Final hack: adjust class of widget when active selection is manipulated
     * by mark-selection addon.
     */
    _adjustWidgetsInSelection() {
        var editor = this.editor,
            sel_className = 'CodeMirror-selectedtext';

        // Clear any previously marked widgets
        $(editor.getWrapperElement()).find(`.CodeMirror-widget.${sel_className}`)
            .removeClass(sel_className);

        // Locate selection mark and adjust widgets contain therein
        var selmark = editor.findMarksAt(editor.getCursor())
            .filter(m => m.className == sel_className)[0], selmark_at;

        if (selmark && (selmark_at = selmark.find()))
            this._markWidgetsAsWell(selmark_at.from, selmark_at.to, selmark);
    }

    getCursor() {
        return this.editor.getCursor();
    }

    cursorLess(c1, c2) {
        return (c1.line < c2.line ||
                (c1.line === c2.line && c1.ch < c2.ch));
    }

    cursorToEnd(stm) {
        this.editor.scrollTo({left: 0});  // try to get back to the leftmost part
        this.editor.setCursor(stm.end);
    }

    /**
     * Checks whether the range from start to end consists solely of
     * whitespaces.
     * @param {Pos} start starting position ({line, ch})
     * @param {Pos} end ending position ({line, ch})
     */
    onlySpacesBetween(start, end) {
        if (start.line > end.line) return true;
        var cur = {line: start.line, ch: start.ch};
        while (cur.line < end.line) {
            let cur_end = this.editor.getLine(cur.line).length,
                portion = this.editor.getRange(cur, {line: cur.line, ch: cur_end});
            if (!this._onlySpaces(portion)) return false;
            cur.line++;
            cur.ch = 0;
        }
        return this._onlySpaces(this.editor.getRange(cur, end));
    }

    _onlySpaces(str) {
        return !!(/^\s*$/.exec(str));
    }

    // If any marks, then call the invalidate callback!
    onCMChange(editor, evt) {

        var doc   = editor.getDoc();
        var marks = doc.getAllMarks();

        // Find the first mark that is at or after the change point
        for (let mark of marks) {
            let b = mark.find();
            if (mark.stm && this.cursorLess(evt.from, b.to)) {
                this.onInvalidate(mark.stm);
                break;
            }
        }
    }

    invalidateAll() {
        /*
        var doc   = this.editor.getDoc();
        var marks = doc.getAllMarks();
        for (let mark of marks) {
            if (mark.stm) this.onInvalidate(mark.stm);
        }
        */
    }

    _markFromElement(dom) {
        var sid = dom.classList.contains('CodeMirror-line') ?
                    $(dom).find('[data-coq-sid]').last().attr('data-coq-sid')
                  : $(dom).attr('data-coq-sid');

        if (sid) {
            for (let mark of this.editor.getAllMarks()) {
                if (mark.stm && mark.stm.coq_sid == sid) {
                    return mark;
                }
            }
        }

        return undefined;
    }

    /**
     * Highlights the sentence mark under the mouse cursor and emits
     * onMouseEnter/onMouseLeave when the active mark changes.
     * @param {MouseEvent} evt event object
     */
    onCMMouseMove(evt) {

        var mark = evt.buttons ? null : this._markFromElement(evt.target);

        if (mark && this.hover.indexOf(mark) > -1) return;

        for (let m of this.hover)
            this.highlight(m.stm, false);

        if (mark && mark.stm.action) {
            this.hover = [mark];
            this.highlight(mark.stm, true);
            this.onMouseEnter(mark.stm, evt);
            if (!this._key_bound) {
                this._key_bound = true;
                $(document).on('keydown keyup', this._keyHandler);
            }
        }
        else {
            if (this.hover[0])
                this.onMouseLeave(this.hover[0].stm, evt);
            this.hover = [];
            $(document).off('keydown keyup', this._keyHandler);
            this._key_bound = false;
        }
    }

    /**
     * De-highlights and emits onMouseLeave when leaving the active mark.
     * @param {MouseEvent} evt event object
     */
    onCMMouseLeave(evt) {
        if (this.hover.length > 0) {
            for (let m of this.hover)
                this.highlight(m.stm, false);
            this.onMouseLeave(this.hover[0].stm, evt);
            this.hover = [];
        }
    }

    keyHandler(evt) {
        /* re-issue mouse enter when modifier key is pressed or released */
        if (this.hover[0] && (evt.key === 'Control'))
            this.onMouseEnter(this.hover[0].stm, evt);
    }

    static _config() {
        CodeMirror.defineOption('className', null, (cm, val) => {
            if (val) {
                var vals = (typeof val == 'string') ? val.split(/\s+/) : val;
                cm.getWrapperElement().classList.add(...vals);
            }
        });
        this._config = () => {};
    }

    /**
     * Iterates (non-whitespace) tokens beginning at `from`.
     * @param {*} from {line, ch} location (zero-based, CM-style)
     */
    *iterTokens(from) {
        var cm = this.editor,
            {line, ch} = from,
            linecount = cm.getDoc().lineCount();
        while (line < linecount) {
            for (let token of cm.getLineTokens(line)) {
                if (token.type && token.start >= ch) yield {line, ...token};
            }
            line++; ch = 0;
        }
    }

    // ================
    // Persistence Part
    // ================

    load(text, filename, dirty=false) {
        if (this.autosave && this.dirty) this.saveLocal();

        this.invalidateAll();

        this.editor.setState(this.createDoc(text));
        this.filename = filename;
        this.dirty = dirty;
        if (filename) this.startAutoSave();
        // TODO clear marks and issue invalidate
    }

    openFile(file) {
        var rdr = new FileReader();
        return new Promise((resolve, reject) => {
            rdr.onload = evt => {
                this.load(evt.target.result, file.name);
                resolve(evt.target.result);
            };
            rdr.readAsText(file, 'utf-8');
        });
    }

    openLocal(filename) {
        filename = filename || this.filename;

        if (filename) {
            var file_store = this.getLocalFileStore();
            return file_store.getItem(filename).then((text) =>
                { this.load(text || "", filename); return text; });
        }
    }

    saveLocal(filename) {
        if (filename) this.filename = filename;

        if (this.filename) {
            var file_store = this.getLocalFileStore();
            file_store.setItem(this.filename, this.editor.getValue());
            this.dirty = false;
        }
    }

    startAutoSave() {
        if (!this.autosave) {
            /** @todo handle with generation instead */
            /*
            this.editor.on('change', () => { this.dirty = true; });
            this.autosave = setInterval(() => { if (this.dirty) this.saveLocal(); },
                this.autosave_interval);
            */
            window.addEventListener('beforeunload', 
                () => { clearInterval(this.autosave);
                        if (this.dirty) this.saveLocal(); });
        }
    }

    getLocalFileStore() { return CmCoqProvider.getLocalFileStore(); }

    static getLocalFileStore() {
        if (!CmCoqProvider.file_store)
            CmCoqProvider.file_store = localforage.createInstance({'name': 'CmCoqProvider.file_store'});
        return CmCoqProvider.file_store;
    }

    // Save/load UI

    openLocalDialog() {
        var span = this._makeFileDialog("Open file: "),
            a = this._makeDialogLink('From disk...', 
                () => this.openFileDialog());

        span.append(a);

        this.editor.openDialog(span[0], sel => this.openLocal(sel));
    }

    openFileDialog() {
        var input = $('<input>').attr('type', 'file');
        input.on('change', () => {
            if (input[0].files[0]) this.openFile(input[0].files[0]);
        });
        input.trigger('click');
    }

    saveLocalDialog() {
        var span = this._makeFileDialog("Save file: "),
            a1 = this._makeDialogLink('To disk...', () => this.saveToFile()),
            a2 = this._makeDialogLink('Share', () => this.saveShare());

        span.append(a1, a2);

        this.editor.openDialog(span[0], sel => this.saveLocal(sel), 
                               {value: this.filename});
    }

    saveToFile() {
        var blob = new Blob([this.editor.getValue()]),
            a = $('<a>').attr({href: URL.createObjectURL(blob),
                               download: this.filename || 'untitled.v'});
        a[0].click();
    }

    saveShare() {
        this.onAction({type: 'share'});
    }

    _makeFileDialog(text) {
        var list_id = 'cm-provider-local-files',
            input = $('<input>').attr('list', list_id),
            list = $('<datalist>').attr('id', list_id);
        
        this.getLocalFileStore().keys().then((keys) => {
            for (let key of keys) {
                list.append($('<option>').val(key));
            }
        });

        this._setupTabCompletion(input, list);

        return $('<span>').text(text).append(input, list)
            .on('done', () => this.editor.focus());
    }

    _makeDialogLink(text, handler, className="dialog-link") {
        return $('<a>').addClass(className).text(text)
            .on('mousedown', ev => ev.preventDefault())
            .on('click', ev => { handler(); $(ev.target).trigger('done'); });
    }

    _setupTabCompletion(input, list) {
        input.keydown(ev => { if (ev.key === 'Tab') {
            this._complete(input, list);
            ev.preventDefault(); ev.stopPropagation(); } 
        });
    }

    _complete(input, list) {
        var value = input.val();

        if (value) {
            var match = list.children('option').get()
                            .find(o => o.value.includes(value));
            if (match) {
                input.val(match.value);
            }
        }
    }
}

CodeMirror.keyMap['jscoq'] = {
    'Tab': 'indentMore',
    'Shift-Tab': 'indentLess',
    'Ctrl-Space': 'autocomplete',
    fallthrough: ["default"]
};

CodeMirror.keyMap['jscoq-snippet'] = {
    PageUp: false,
    PageDown: false,
    //'Cmd-Up': false,   /** @todo this does not work? */
    //'Cmd-Down': false
};

/**
 * Workaround to prevent CodeMirror from consuming PageUp/PageDn.
 * This means that editor focus is lost when scrolling with the keyboard;
 * but seems better than the alternative, which is the user having to
 * click PageUp/PageDn twice to initiate scroll.
 */
function pageUpDownOverride(element) {
    var scrollable = document.querySelector('#page'); /** @todo */
    if (scrollable)
        element.addEventListener('keydown', ev => {
            if (ev.key === 'PageDown' || ev.key === 'PageUp') {
                ev.stopPropagation(); scrollable.focus();
            }
        }, {capture: true});
}

/**
 * For HTML-formatted Coq snippets created by coqdoc.
 * This reverses the modifications made during pretty-printing
 * to allow the text to be placed in an editor.
 */
class Deprettify {

    /**
     * Remove redundant leading and trailing newlines generated by coqdoc.
     * @param {HTMLElement} element 
     */
    static trim(element) {
        var c;
        if ((c = element.firstChild) && Deprettify.isWS(c))
            element.removeChild(c);
        if ((c = element.firstChild) && Deprettify.isBR(c))
            element.removeChild(c);
        //if ((c = element.firstChild) && Deprettify.isWS(c))
        //    element.removeChild(c);
        while ((c = element.lastChild) && 
                (Deprettify.isWS(c) || Deprettify.isBR(c)))
            element.removeChild(element.lastChild);
        return element;
    }

    static isWS(node) {
        return node.nodeType === Node.TEXT_NODE &&
               node.nodeValue.match(/^\s*\n$/);
    }

    static isBR(node) {
        return node.nodeType === Node.ELEMENT_NODE &&
               node.nodeName === 'BR';
    }

    /**
     * Translate back some unicode symbols to their original ASCII.
     * @param {string} text 
     */
    static cleanup(text) {
        for (let [re, s] of this.REPLACES) text = text.replace(re, s);
        return text.replace(/^\n/, '');
    }
}

Deprettify.REPLACES = [  /* Safari does not support static members? */
    [/\xa0/g, ' '], [/⇒/g, '=>'],   [/×/g, '*'],
    [/→/g, '->'],   [/←/g, '<-'],   [/¬/g, '~'],
    [/⊢/g, '|-'],   [/\n☐/g, ''],
    [/∃/g, 'exists']  /* because it is also a tactic... */
];

// Local Variables:
// js-indent-level: 4
// End:
