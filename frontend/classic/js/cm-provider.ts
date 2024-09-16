import $ from 'jquery';
import localforage from "localforage";

function assert(value: boolean, message?: string): asserts value {
    if (!value) throw new Error(message);
}

// CM imports
import CodeMirror, { Editor } from "codemirror";

import 'codemirror/addon/hint/show-hint.js';
import 'codemirror/addon/edit/matchbrackets.js';
import 'codemirror/keymap/emacs.js';
import 'codemirror/addon/selection/mark-selection.js';
import 'codemirror/addon/edit/matchbrackets.js';
import 'codemirror/addon/dialog/dialog.js';
import 'codemirror/addon/search/search.js';
import 'codemirror/addon/search/searchcursor.js';
import 'codemirror/addon/search/jump-to-line.js';

// CM medias
import 'codemirror/lib/codemirror.css';
import 'codemirror/theme/blackboard.css';
import 'codemirror/theme/darcula.css';
import 'codemirror/addon/hint/show-hint.css';
import 'codemirror/addon/dialog/dialog.css';

// Project imports
import { copyOptions, isMac } from '../../common/etc.js';
import { JsCoq } from './index.js';

import { CoqManager } from './coq-manager';
import { Deprettify } from './deprettify';

import '../external/CodeMirror-TeX-input/addon/hint/tex-input-hint.js';
import './mode/coq-mode.js';
import { CompanyCoq }  from './addon/company-coq.js';
import { Diagnostic } from '../../../backend/coq-worker.js';

/**
 * A Coq sentence, typically ended in dot "."
 *
 * @class CmSentence
 */
class CmSentence {
    start : CodeMirror.Position;
    end : CodeMirror.Position;
    text : string;
    mark ?: number;
    flags : {is_comment : boolean, is_hidden : boolean};
    feedback : number[];
    action : number;
    coq_sid : string;

    /**
     * Creates an instance of CmSentence.
     * @param {CodeMirror.Position} start
     * @param {CodeMirror.Position} end
     * @param {string} text
     * @param {object} flags
     * @memberof CmSentence
     */
    constructor(start, end, text, flags) {
        // start, end: {line: number, ch: number}
        // flags: {is_comment: bool, is_hidden: bool}
        this.start = start;
        this.end   = end;
        this.text  = text;
        /**
         * @type {undefined}
         */
        this.mark  = undefined;
        this.flags = flags || {};
        this.feedback = [];
        /**
         * @type {undefined}
         */
        this.action = undefined;
    }
} 

// Extensions to TS typing in npm
declare module "codemirror" {
    var keyMap : any;

    interface TextMarker<T = CodeMirror.MarkerRange | CodeMirror.Position> {
        stm : CmSentence;
        diag : boolean;
        widgetNode : HTMLElement;
    }
    interface Editor {
        findMarks(from, to, filter);
        on(method: 'hintHover', fn);
        on(method: 'hintZoom', fn);
        on(method: 'hintEnter', fn);
        on(method: 'hintOut', fn);
    }
    interface OpenDialogOptions {
        value : string;
    }
}

interface CM5Options {
    mode?: { "company-coq": boolean } 
}

/**
 * A CodeMirror-based Provider of coq statements.
 */
export class CmCoqProvider {
    idx : number;
    filename ?: string;
    dirty : boolean;
    autosave : any; // result of setTimeout
    autosave_interval : number;
    editor : Editor;
    onChange : (cm : Editor, change) => void;
    onCursorUpdate : (cm : Editor) => void;
    onInvalidate : (evt : any ) => void;
    onMouseEnter : (stm, evt : any ) => void;
    onMouseLeave : (stm, evt : any ) => void;
    onTipHover : (entrires, zoom : any ) => void;
    onTipOut : (evt : any ) => void;
    onResize : (evt : any ) => void;
    onAction : (evt : any ) => void;
    _keyHandler : (x : any) => void;
    _key_bound : boolean;
    hover : any[];
    company_coq ?: CompanyCoq;
    lineCount : number;
    options : any;
    manager : CoqManager;

    /**
     * Creates an instance of CmCoqProvider.
     * @param element DOM element to place the editor in
     * @param options CodeMirror options object
     * @param replace if `true`, `element` is *replaced* by the editor, and
     *   whatever text was contained in it is placed in the editor.
     * @param {number} idx index of this snippet within a ProviderContainer
     * @memberof CmCoqProvider
     */
// <<<<<<< HEAD
/*    constructor(element: HTMLElement, options : CM5Options, replace : boolean, idx: number, manager: CoqManager) {

        this.options = options;
        this.idx = idx;
        this.manager = manager;
*/
    constructor(element, options : CM5Options, replace : boolean, idx : number) {

        CmCoqProvider._config();

        var cmOpts = /** @type {CodeMirror.EditorConfiguration} */ (
            { mode : { name : "coq",
                       singleLineStringErrors : false },
              lineNumbers       : true,
              indentUnit        : 2,
              tabSize           : 2,
              indentWithTabs    : false,
              matchBrackets     : true,
              styleSelectedText : true,
              dragDrop          : false, /* handled by CoqManager */
              keyMap            : "jscoq",
              className         : "jscoq"
            });

        copyOptions(options, cmOpts);

        // We test for :hidden custom attribute, as to assume less shared attribute
        // state, this is useful when replacing editors.
        var makeHidden = $(element).is(':hidden') ||
            /* corner case: a div with a single hidden child is considered hidden */
            element.children.length == 1 && $(element.children[0]).is(':hidden');

        if (element.tagName === 'TEXTAREA') {
            assert(element instanceof HTMLTextAreaElement);
            /* workaround: `value` sometimes gets messed up after forward/backwarn nav in Chrome */
            element.value ||= element.textContent;
            /** @todo desirable, but causes a lot of errors: @ type {CodeMirror.Editor} */
            this.editor = CodeMirror.fromTextArea(element, cmOpts);
            replace = true;
        } else {
            this.editor = this.createEditor(element, cmOpts, replace);
        }

        if (replace) this.editor.addKeyMap('jscoq-snippet');

        this.filename = element.getAttribute('data-filename');
        this.autosave_interval = 20000 /*ms*/;

        if (this.filename) { this.openLocal(this.filename); this.startAutoSave(); }

        // Event handlers (to be overridden by ProviderContainer)
        this.onChange = (nt) => {};
        this.onCursorUpdate = (cm) => {};
        this.onInvalidate = (mark) => {};
        this.onMouseEnter = (stm, ev) => {};
        this.onMouseLeave = (stm, ev) => {};
        this.onTipHover = (entries, zoom) => {};
        this.onTipOut = () => {};
        this.onResize = (lineCount) => {};
        this.onAction = (action) => {};

        this.editor.on('beforeChange', (cm, evt) => this.onCMChange(cm, evt) );
        this.editor.on('change', (cm, evt) => this.onChange(cm, evt));

        this.editor.on('cursorActivity', (cm) => {
            this.onCursorUpdate(cm);
            cm.operation(() => this._adjustWidgetsInSelection())
        });

        this.trackLineCount();

        // Handle mouse hover events
        var editor_element = $(this.editor.getWrapperElement());
        editor_element.on('mousemove', ev => this.onCMMouseMove(ev));
        editor_element.on('mouseleave', ev => this.onCMMouseLeave(ev));

        // EJGA: Don't make hidden editors for now
        if (false && makeHidden && !editor_element.is(':hidden'))
            editor_element.css({display: "none"});

        // Some hack to prevent CodeMirror from consuming PageUp/PageDn
        if (replace) pageUpDownOverride(editor_element[0]);

        this._keyHandler = this.keyHandler.bind(this);
        this._key_bound = false;

        this.hover = [];

        // Handle hint events
        this.editor.on('hintHover',     (completion)     => this.onTipHover([completion], false));
        this.editor.on('hintZoom',      (completion)     => this.onTipHover([completion], true));
        this.editor.on('hintEnter',     (tok, entries)   => this.onTipHover(entries, false));
        this.editor.on('hintOut',       (cm)             => this.onTipOut(cm));
        this.editor.on('endCompletion', (cm)             => this.onTipOut(cm));

        if (this.options?.mode?.['company-coq']) {
            this.company_coq = new CompanyCoq(this.manager);
            this.company_coq.attach(this.editor);
        }
    }

    static file_store = null;

    /**
     * @param {HTMLElement} element
     * @param {CodeMirror.EditorConfiguration | undefined} opts
     * @param {any} replace
     */
    createEditor(element, opts, replace) {
        var text = replace && $(element).text(),
            editor = CodeMirror(element, opts);
        if (replace) {
            editor.setValue(Deprettify.cleanup(text));
            element.replaceWith(editor.getWrapperElement());
        }
        return editor;
    }

    /**
     * @param {{ theme: any; }} options
     */
    configure(options) {
        if (options.theme) {
            this.editor.setOption('theme', options.theme);
        }
        CompanyCoq.configure(this.editor, options);
    }

    getText() {
        return this.editor.getValue();
    }
    // ----------------------------------
    // CoqEditor interface implementation

    getValue() {
         return this.editor.getValue();
     }

    getCursorOffset() {
        return this.editor.getDoc().indexFromPos(this.editor.getCursor());
    }

    // ---------------------------------

    getLength() {
        /** @todo optimize */
        return this.editor.getValue().length;
    }
    
    trackLineCount() {
        this.lineCount = this.editor.lineCount();
        this.editor.on('change', (ev) => {
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

    isHidden() {
        return $(this.editor.getWrapperElement()).is(':hidden');
    }

    // If prev == null then get the first.
    /**
     * @param {{ end: any; }} prev
     * @param {CodeMirror.Position} until
     */
    getNext(prev, until) {

        var doc = this.editor.getDoc(),
            start = prev ? prev.end : {line : 0, ch : 0};

        if (until && this.onlySpacesBetween(start, until))
            return null;

        // small DFA that scans either a comment block or a statement
        const delim = ['statementend', 'coq-bullet', 'brace'];
        var state = 0, upto;
        dfa: for (let cur of this.iterTokens(start)) {
            switch (state) {
            case 0: state = cur.type === 'comment' ? 2 : 1; /* fallthrough */
            case 1: upto = cur; if (delim.includes(cur.type)) break dfa; break;
            case 2: if (cur.type !== 'comment') break dfa; upto = cur; break;
            }
        }

        if (!upto) return null; // EOF

        var end = {line: upto.line, ch: upto.end};

        return new CmSentence(start, end, doc.getRange(start, end),
            {is_comment: state == 2, is_hidden: this.isHidden()});
    }

    // Gets sentence at point;
    getAtPoint() {

        var doc   = this.editor.getDoc();
        var marks = doc.findMarksAt(doc.getCursor());

        for (let mark of marks) {
            if (mark.stm) return mark.stm;
        }
    }

    /**
     * @param {{ mark: { className: string; }; coq_sid: any; }} stm
     * @param {boolean} flag
     */
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
     * @param {any} stm
     * @param {any} loc
     * @param {string} className
     */
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
            // XXX: Avoid to clear company-coq marks
            mark.clear();
        }
    }

    mark(diag : Diagnostic) {

        var tr_loc = ({character, line}) => { return {line: line, ch: character } };

        var className = diag.extra ? 'coq-eval-pending' :
                        (diag.severity === 1) ? 'coq-eval-failed' : 'coq-eval-ok';

        var doc = this.editor.getDoc();
        let start = tr_loc(diag.range.start), end = tr_loc(diag.range.end);

        var mark =
            doc.markText(start, end,
             {className: className, attributes: {'data-coq-range': JSON.stringify(diag.range)}});

        this._markWidgetsAsWell(start, end, mark);

    }

    /**
     * @param {{ mark: { on: (arg0: string, arg1: () => any) => void; }; }} stm
     * @param {{ start: any; end: any; }} pos
     * @param {any} className
     */
    markSubordinate(stm, pos, className) {
        var doc = this.editor.getDoc(),
            {start, end} = pos;

        var mark = 
            doc.markText(start, end, {className: className});

        this._markWidgetsAsWell(start, end, mark);

        stm.mark.on('clear', () => mark.clear());
        return mark;
    }

    /**
     * @param {{ text: string | undefined; start: any; end: any; }} stm
     * @param {{ bp: any; ep: number; }} loc
     */
    _subregion(stm, loc) {
        // Offsets are in bytes :/
        var stmBytes = new TextEncoder().encode(stm.text),
            td = new TextDecoder(),
            bytesToChars = (/** @type {number | undefined} */ i) => td.decode(stmBytes.slice(0, i)).length,
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
     * @param {any} start
     * @param {any} end
     * @param {{ className: string; attributes: {}; }} mark
     */
    _markWidgetsAsWell(start, end, mark) {
        var classNames = mark.className.split(/ +/);
        var attrs = mark.attributes || {};
        for (let w of this.editor.findMarks(start, end, (x) => x.widgetNode)) {
            for (let cn of classNames)
                w.widgetNode.classList.add(cn);
            for (let attr in attrs)
                w.widgetNode.setAttribute(attr, attrs[attr]);
        }
        mark.on('clear', (from, to) => this._unmarkWidgets(from, to));
    }

    /**
     * Hack contd: negates effects of _markWidgetsAsWell when mark is cleared.
     * @param {any} start
     * @param {any} end
     */
    _unmarkWidgets(start, end) {
        for (let w of this.editor.findMarks(start, end, (/** @type {{ widgetNode: any; }} */ x) => x.widgetNode)) {
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
            .filter((/** @type {{ className: string; }} */ m) => m.className == sel_className)[0], selmark_at;

        if (selmark && (selmark_at = selmark.find()))
            this._markWidgetsAsWell(selmark_at.from, selmark_at.to, selmark);
    }

    getCursor() {
        return this.editor.getCursor();
    }

    /**
     * @param {{ line: number; ch: number; }} c1
     * @param {{ line: number; ch: number; }} c2
     */
    cursorLess(c1, c2) {
        return (c1.line < c2.line ||
                (c1.line === c2.line && c1.ch < c2.ch));
    }

    /**
     * @param {{ end: any; }} stm
     */
    cursorToEnd(stm) {
        this.editor.scrollTo(0);  // try to get back to the leftmost part
        this.editor.setCursor(stm.end);
    }

    /**
     * Checks whether the range from start to end consists solely of
     * whitespaces.
     * @param {CodeMirror.Position} start starting position ({line, ch})
     * @param {CodeMirror.Position} end ending position ({line, ch})
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

    /**
     * @param {string} str
     */
    _onlySpaces(str) {
        return !!(/^\s*$/.exec(str));
    }

    // If any marks, then call the invalidate callback!
    /**
     * @param {{ getDoc: () => any; }} editor
     * @param {{ from: any; }} evt
     */
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
        var doc   = this.editor.getDoc();
        var marks = doc.getAllMarks();
        for (let mark of marks) {
            if (mark.stm) this.onInvalidate(mark.stm);
        }
    }

    /**
     * @param {HTMLElement} dom
     */
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
     * @param {JQuery.MouseMoveEvent} evt event object
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
     * @param {JQuery.MouseLeaveEvent} evt event object
     */
    onCMMouseLeave(evt) {
        if (this.hover.length > 0) {
            for (let m of this.hover)
                this.highlight(m.stm, false);
            this.onMouseLeave(this.hover[0].stm, evt);
            this.hover = [];
        }
    }

    /**
     * @param {{ key: string; }} evt
     */
    keyHandler(evt) {
        /* re-issue mouse enter when modifier key is pressed or released */
        if (this.hover[0] && (evt.key === 'Control'))
            this.onMouseEnter(this.hover[0].stm, evt);
    }

    /**
     * XXXX
     * @function _config
     * @memberof CmCoqProvider
     * @static
     */
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

    /**
     * @param {string} text
     * @param {any} filename
     */
    load(text, filename, dirty=false) {
        if (this.autosave && this.dirty) this.saveLocal();

        this.invalidateAll();

        this.editor.swapDoc(new CodeMirror.Doc(text, this.editor.getOption('mode')));
        this.filename = filename;
        this.dirty = dirty;
        if (filename) this.startAutoSave();
        // TODO clear marks and issue invalidate
    }

    /**
     * @param {File} file
     * @return {Promise<string>}
     */
    openFile(file) {
        var rdr = new FileReader();
        return new Promise((resolve, reject) => {
            rdr.onload = evt => {
                let content = /** @type {string} */ (evt.target.result);
                this.load(content, file.name);
                resolve(content);
            };
            rdr.readAsText(file, 'utf-8');
        });
    }

    /**
     * @param {undefined} [filename]
     */
    openLocal(filename) {
        filename = filename || this.filename;

        if (filename) {
            var file_store = this.getLocalFileStore();
            return file_store.getItem(filename).then((text) =>
                { this.load(text || "", filename); return text; });
        }
    }

    /**
     * @param {undefined} [filename]
     */
    saveLocal(filename?) {
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
            a = this._makeDialogLink('From disk...', 
                () => this.openFileDialog());

        span.append(a);

        this.editor.openDialog(span[0], (sel) => this.openLocal(sel));
    }

    openFileDialog() {
        var input = $('<input>').attr('type', 'file') as JQuery<HTMLInputElement>;
        input.on('change', () => {
            if (input[0].files[0]) this.openFile(input[0].files[0]);
        });
        input.trigger('click');
    }

    saveLocalDialog() {
        var span = this._makeFileDialog("Save file: "),
            a1 = this._makeDialogLink('To disk...', () => this.saveToFile()),
            share = $('<span>').addClass('dialog-share')
                    .append($('<img>').attr('src', JsCoq.base_path + 'frontend/classic/images/share.svg')),
            a2 = this._makeDialogLink('Hastebin', () => this.shareHastebin()),
            a3 = betaOnly(() =>
                 this._makeDialogLink('P2P', () => this.shareP2P())),
            a4 = this._makeDialogLink('Gist', () => this.shareGist());

        span.append(a1, share.append(a2, a3, a4));

        this.editor.openDialog(span[0], (sel) => this.saveLocal(sel), 
                               {value: this.filename});
    }

    saveToFile() {
        var blob = new Blob([this.editor.getValue()]),
            a = $('<a>').attr({href: URL.createObjectURL(blob),
                               download: this.filename || 'untitled.v'});
        a[0].click();
    }

    shareHastebin() {
        this.onAction({type: 'share-hastebin'});
    }

    shareP2P() {
        this.onAction({type: 'share-p2p'});
    }

    shareGist() {
        this.onAction({type: 'share-gist'});
    }

    /**
     * @param {string | number | boolean | ((this: HTMLElement, index: number, text: string) => string | number | boolean)} text
     */
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

    /**
     * @param {string | number | boolean | ((this: HTMLElement, index: number, text: string) => string | number | boolean)} text
     * @param {{ (): void; (): void; (): void; (): void; (): void; }} handler
     */
    _makeDialogLink(text, handler, className="dialog-link") {
        return $('<a>').addClass(className).text(text)
            .on('mousedown', ev => ev.preventDefault())
            .on('click', ev => { handler(); $(ev.target).trigger('done'); });
    }

    /**
     * @param {JQuery<HTMLElement>} input
     * @param {JQuery<HTMLElement>} list
     */
    _setupTabCompletion(input, list) {
        input.keydown((/** @type {{ key: string; preventDefault: () => void; stopPropagation: () => void; }} */ ev) => { if (ev.key === 'Tab') {
            this._complete(input, list);
            ev.preventDefault(); ev.stopPropagation(); } 
        });
    }

    /**
     * @param { * } input
     * @param { * } list
     */
    _complete(input, list) {
        var value = input.val();

        if (value) {
            var match = list.children('option').get()
                            .find((o) => o.value.includes(value));
            if (match) {
                input.val(match.value);
            }
        }
    }

    static _set_keymap() {

        const Mod = isMac ? 'Cmd' : 'Ctrl',
              MMod = isMac ? 'Cmd-Option' : 'Shift-Ctrl';

        CodeMirror.keyMap['jscoq'] = {
            'Tab': 'indentMore',
            'Shift-Tab': 'indentLess',
            'Ctrl-Space': 'autocomplete',
            [`${Mod}-F`]: 'findPersistent',  /* non-persistent find is just foolish */
            fallthrough: ["default"]
        };

        CodeMirror.keyMap['jscoq-snippet'] = {
            PageUp: false,        /* to allow keyboard scrolling through the page */
            PageDown: false,
            [`${Mod}-F`]: false,  /* sorry, have to disable search because it looks dumb in snippets */
            [`${MMod}-F`]: false,
            'Alt-G': false,
            //'Cmd-Up': false,   /** @todo this does not work? */
            //'Cmd-Down': false
        };
    }
}

/**
 * @param {{ (): JQuery<HTMLElement>; (): any; }} thing
 */
function betaOnly(thing) {
    return JsCoq.globalConfig().features.includes('beta')
             ? thing() : undefined;
}

/**
 * Workaround to prevent CodeMirror from consuming PageUp/PageDn.
 * This means that editor focus is lost when scrolling with the keyboard;
 * but seems better than the alternative, which is the user having to
 * click PageUp/PageDn twice to initiate scroll.
 * @param {HTMLElement} element
 */
function pageUpDownOverride(element) {
    var scrollable = (document.querySelector('#page') as HTMLDivElement);
    if (scrollable)
        element.addEventListener('keydown', (ev) => {
            if (ev.key === 'PageDown' || ev.key === 'PageUp') {
                ev.stopPropagation(); scrollable.focus();
            }
        }, {capture: true});
}

// Local Variables:
// js-indent-level: 4
// End:
