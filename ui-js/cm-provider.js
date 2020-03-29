"use strict";

class CmSentence {

    constructor(start, end, text, is_comment) {
        // start, end: {line: l, ch: c}
        this.start = start;
        this.end   = end;
        this.text  = text;
        this.mark  = undefined;
        this.is_comment = is_comment;
        this.feedback = [];
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
              keyMap            : "emacs",
              extraKeys: {
                  'Tab': 'indentMore',
                  'Shift-Tab': 'indentLess',
                  'Ctrl-Space': 'autocomplete'
              },
              className         : "jscoq"
            };

        if (options)
            copyOptions(options, cmOpts);

        if (element.tagName === 'TEXTAREA') {
            this.editor = CodeMirror.fromTextArea(element, cmOpts);
        } else {
            this.editor = this.createEditor(element, cmOpts, replace);
        }

        this.filename = element.getAttribute('data-filename');
        this.autosave_interval = 20000 /*ms*/;

        if (this.filename) { this.openLocal(); this.startAutoSave(); }

        // Event handlers (to be overridden by ProviderContainer)
        this.onInvalidate = (mark) => {};
        this.onMouseEnter = (stm, ev) => {};
        this.onMouseLeave = (stm, ev) => {};
        this.onTipHover = (completion, zoom) => {};
        this.onTipOut = () => {};
        this.onResize = (lineCount) => {};

        this.editor.on('beforeChange', (cm, evt) => this.onCMChange(cm, evt) );

        this.editor.on('cursorActivity', (cm) => 
            cm.operation(() => this._adjustWidgetsInSelection()));

        this.trackLineCount();

        // Handle mouse hover events
        var editor_element = $(this.editor.getWrapperElement());
        editor_element.on('mousemove', ev => this.onCMMouseMove(ev));
        editor_element.on('mouseleave', ev => this.onCMMouseLeave(ev));

        this._keyHandler = this.keyHandler.bind(this);
        this._key_bound = false;

        this.hover = [];

        // Handle hint events
        this.editor.on('hintHover',     completion     => this.onTipHover(completion, false));
        this.editor.on('hintZoom',      completion     => this.onTipHover(completion, true));
        this.editor.on('hintEnter',     (tok, entries) => this.onTipHover(entries[0], false));
        this.editor.on('hintOut',       ()             => this.onTipOut());
        this.editor.on('endCompletion', cm             => this.onTipOut());
    }

    createEditor(element, opts, replace) {
        var text = replace && $(element).text(),
            editor = new CodeMirror(element, opts);
        if (replace) {
            editor.setValue(Deprettify.cleanup(text));
            element.replaceWith(editor.getWrapperElement());
        }
        return editor;
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
        var dialog_input = this.editor.getWrapperElement()
            .querySelector('.CodeMirror-dialog');
        // If a dialog is open, editor.focus() will close it,
        // leading to poor UX.
        if (!dialog_input) this.editor.focus();
    }

    // If prev == null then get the first.
    getNext(prev, until) {

        var start = {line : 0, ch : 0};
        var doc = this.editor.getDoc();

        if (prev) {
            start = prev.end;
        }

        if (until && this.onlySpacesBetween(start, until))
            return null;

        // EOF
        if (start.line === doc.lastLine() &&
            start.ch === doc.getLine(doc.lastLine()).length) {
            return null;
        }

        var token = this.getNextToken(start, /statementend|bullet|brace/);
        if (!token) return null;

        var end = {line : token.line, ch : token.end};

        for (var mark of doc.findMarks(end,end)) {
            mark.clear();
        }

        var stm = new CmSentence(start, end,
                                 doc.getRange({line : start.line, ch : start.ch},
                                              {line : token.line, ch : token.end}),
                                 token.type === 'comment'  // XXX This is never true
                                );
        return stm;
    }

    // Gets sentence at point;
    getAtPoint() {

        var doc   = this.editor.getDoc();
        var marks = doc.findMarksAt(doc.getCursor());

        for (let mark of marks) {
            if (mark.stm) return mark.stm;
        }
    }

    // Mark a sentence with {clear, processing, error, ok}
    mark(stm, mark_type) {

        if (stm.mark) {
            let b = stm.mark.find();
            if (!b) return;  /* mark has been deleted altogether; fail silently */
            stm.start = b.from; stm.end = b.to;
            stm.mark.clear(); this._unmarkWidgets(stm.start, stm.end);
            stm.mark = null;
        }

        switch (mark_type) {
        case "clear":
            // XXX: Check this is the right place.
            // doc.setCursor(stm.start);
            break;
        case "processing":
            this.markWithClass(stm, 'coq-eval-pending');
            break;
        case "error":
            this.markWithClass(stm, 'coq-eval-failed');
            // XXX: Check this is the right place.
            this.editor.setCursor(stm.end);
            break;
        case "ok":
            this.markWithClass(stm, 'coq-eval-ok');
            // XXX: Check this is the right place.
            // This interferes with the go to target.
            // doc.setCursor(stm.end);
            break;
        }
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
        var doc = this.editor.getDoc();

        var mark = 
            doc.markText(stm.start, stm.end, {className: className,
                attributes: {'data-coq-sid': stm.coq_sid}});

        this._markWidgetsAsWell(stm.start, stm.end, mark);

        mark.stm = stm;
        stm.mark = mark;
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

        if (mark) {
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

    // CM specific functions.

    // Returns the next token after the one seen at position: {line:…, ch:…}
    // type_re: regexp to match token type.
    // The returned object is a CodeMirror token with an additional attribute 'line'.
    getNextToken(position, type_re) {
        var cm = this.editor;
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
    }

    // ================
    // Persistence Part
    // ================

    load(text, filename, dirty=false) {
        if (this.autosave && this.dirty) this.saveLocal();

        this.editor.setValue(text);
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
            this.editor.on('change', () => { this.dirty = true; });
            this.autosave = setInterval(() => { if (this.dirty) this.saveLocal(); },
                this.autosave_interval);
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
            a = $('<a>').addClass('dialog-link').text('From disk...')
                        .mousedown(ev => ev.preventDefault())
                        .click(() => this.openFileDialog());

        span.append(a);

        this.editor.openDialog(span[0], sel => this.openLocal(sel));
    }

    openFileDialog() {
        var input = $('<input>').attr('type', 'file');
        input.change(() => {
            if (input[0].files[0]) this.openFile(input[0].files[0]);
        });
        input.click();
    }

    saveLocalDialog() {
        var span = this._makeFileDialog("Save file: "),
            a = $('<a>').addClass('dialog-link').text('To disk...')
                        .mousedown(ev => ev.preventDefault())
                        .click(() => this.saveToFile());

        span.append(a);

        this.editor.openDialog(span[0], sel => this.saveLocal(sel), 
                               {value: this.filename});
    }

    saveToFile() {
        var blob = new Blob([this.editor.getValue()]),
            a = $('<a>').attr({href: URL.createObjectURL(blob),
                               download: this.filename || 'untitled.v'});
        a[0].click();
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

        return $('<span>').text(text).append(input, list);
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


/**
 * For HTML-formatted Coq snippets created by coqdoc.
 * This reverses the modifications made during pretty-printing
 * to allow the text to be placed in an editor.
 */
class Deprettify {

    static trim(element) {
        if (element.firstChild && Deprettify.isWS(element.firstChild))
            element.removeChild(element.firstChild);
        if (element.lastChild && Deprettify.isWS(element.lastChild))
            element.removeChild(element.lastChild);
        return element;
    }

    static isWS(element) {
        return element.nodeType === Node.TEXT_NODE &&
               element.nodeValue.match(/^\s*$/);
    }

    static cleanup(text) {
        return text.replace(/\xa0/g, ' ').replace(/⇒/g, '=>');
    }

}

// Local Variables:
// js-indent-level: 4
// End:
