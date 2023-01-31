import { Future } from "../../../backend/future.js";
import { CmCoqProvider, Deprettify } from './cm-provider.js';

/**
 * A Provider Container aggregates several containers, the main deal
 * here is keeping track of focus, as the focused container can be
 * different from the "active" one
 *
 * @class ProviderContainer
 */
export class ProviderContainer {
    options : any;
    snippets : CmCoqProvider[];
    onChange : (cm, change ) => void;
    onInvalidate : (evt : any ) => void;
    onMouseEnter : (stm, evt : any ) => void;
    onMouseLeave : (stm, evt : any ) => void;
    onTipHover : (entrires, zoom : any ) => void;
    onTipOut : (evt : any ) => void;
    onResize : (evt : any ) => void;
    onAction : (evt : any ) => void;
    wait_for : Future<void>;
    currentFocus : CmCoqProvider;

    /**
     * Creates an instance of ProviderContainer.
     * 
     * @param {string} elementRefs
     * @param {object} options
     * @memberof ProviderContainer
     */
    constructor(elementRefs, options) {

        this.options = options ? options : {};

        /**
         * @name ProviderContainer#snippets
         * @type CmCoqProvider[]
         */
        this.snippets = [];

        // Event handlers (to be overridden by CoqManager)
        this.onInvalidate = (mark) => {};
        this.onMouseEnter = (stm, ev) => {};
        this.onMouseLeave = (stm, ev) => {};
        this.onTipHover = (entries, zoom) => {};
        this.onTipOut = () => {};
        this.onAction = (action) => {};
        this.wait_for = null;
        
        class WhileScrolling {
            handler : () => void;
            active : boolean;
            to : any;

            constructor() {
                this.handler = () => {
                    this.active = true;
                    if (this.to) clearTimeout(this.to);
                    this.to = setTimeout(() => this.active = false, 200);
                };
                window.addEventListener('scroll', this.handler, {capture: true});
            }
            destroy() {
                window.removeEventListener('scroll', this.handler);
            }
        }

        CmCoqProvider._set_keymap();

        // Create sub-providers.
        //   Do this asynchronously to avoid locking the page when there is
        //   a large number of snippets.
        (async () => {
            var i = 0, scroll = new WhileScrolling();

            for (let [idx, element] of this.findElements(elementRefs).entries()) {

                if (this.options.replace)
                    element = Deprettify.trim(element);

                // Init.
                let cm = new CmCoqProvider(element, this.options.editor, this.options.replace, idx);

                this.snippets.push(cm);

                // Track focus XXX (make generic)
                cm.editor.on('focus', ev => { this.currentFocus = cm; });

                // Track invalidate
                cm.onInvalidate = (stm)     => { this.onInvalidate(stm); };
                cm.onMouseEnter = (stm, ev) => { this.onMouseEnter(stm, ev); };
                cm.onMouseLeave = (stm, ev) => { this.onMouseLeave(stm, ev); };

                cm.onTipHover = (entries, zoom) => { this.onTipHover(entries, zoom); };
                cm.onTipOut   = (cm)            => { this.onTipOut(cm); }

                cm.onAction = (action) => { this.onAction({...action, snippet: cm}); };

                // Running line numbers
                if (this.options.line_numbers === 'continue') {
                    if (idx > 0) this.renumber(idx - 1);
                    cm.onResize = () => { this.renumber(idx); }
                }

                if (scroll.active || (++i) % 5 == 0) await this.yield();
            }

            scroll.destroy();
        })();
    }

    /**
     * Find elements in the page
     *
     * @param {*} elementRefs
     * @return {HTMLElement[]}
     * @memberof ProviderContainer
     */
    findElements(elementRefs) {
        var elements = [];
        for (let e of elementRefs) {
            var els = (typeof e === 'string') ?
                [document.getElementById(e), ...document.querySelectorAll(e)] : e;
            els = els.filter(x => x);
            if (els.length === 0) {
                console.warn(`[jsCoq] element(s) not found: '${e}'`);
            }
            elements.push(...els);
        }
        return elements;
    }

    /**
     * Readjust line numbering flowing from one editor to the next.
     * @param {number} startIndex index where renumbering should start
     */
    async renumber(startIndex) {
        let snippet = this.snippets[startIndex],
            line = snippet.editor.getOption('firstLineNumber') + snippet.lineCount;

        for (let index = startIndex + 1; index < this.snippets.length; index++) {
            let snippet = this.snippets[index];
            snippet.editor.setOption('firstLineNumber', line);
            line += snippet.lineCount;
        }
    }

    yield() {
        if (this.wait_for && !this.wait_for.isDone()) return this.wait_for.promise;
        return new Promise(resolve => setTimeout(resolve, 0));
    }

    configure(options) {
        for (let snippet of this.snippets)
            snippet.configure(options);
    }

    // Get the next candidate and mark it.
    getNext(prev, until) {

        // If we have no previous element start with the first
        // snippet, else continue with the current one.
        var spr = prev ? prev.sp : this.snippets[0];

        if (until && this.snippets.indexOf(spr) > this.snippets.indexOf(until.sp))
            return null;

        var next = spr.getNext(prev, (until && until.sp === spr) ? until.pos : null);

        // We got a snippet!
        if (next) {
            next.sp = spr;
            return next;
        } else if (until && until.sp === spr) {
            return null;
        } else {
            // Try the next snippet.
            var idx = this.snippets.indexOf(spr);
            while (idx < this.snippets.length - 1) {
                spr  = this.snippets[idx+1];
                next = spr.getNext(null);
                if (next) {
                    next.sp = spr;
                    return next;
                } else {
                    idx = this.snippets.indexOf(spr);
                }
            } // while
            // No next snippet :( !
            return null;
        }
    }

    mark(stm, mark, loc_focus) {
        stm.sp.mark(stm, mark, loc_focus);
    }

    highlight(stm, flag) {
        stm.sp.highlight(stm, flag);
    }

    retract() {
        for (let sp of this.snippets) sp.retract();
    }

    // Focus and movement-related operations.

    // Get the point of the current focused element.
    getAtPoint() {
        return this.currentFocus.getAtPoint();
    }

    // Indicates if stm is after the point.
    // XXX: Improve
    afterPoint(stm) {

        var idx_point = this.snippets.indexOf(this.currentFocus);
        var idx_cur   = this.snippets.indexOf(stm.sp);

        return (idx_point < idx_cur);

    }

    getCursor() {
        return {sp: this.currentFocus,
                pos: this.currentFocus.getCursor()}
    }

    cursorToStart(stm) {
        stm.sp.cursorToStart(stm);
    }

    cursorToEnd(stm) {
        stm.sp.cursorToEnd(stm);
    }

    _delegate(op) {
        var sp = this.currentFocus || this.snippets[0];
        if (sp) op(sp);
    }

    focus()                      { this._delegate(sp => sp.focus()); }
    load(text, filename, dirty)  { this._delegate(sp => sp.load(text, filename, dirty)); }
    openFile(file)               { this._delegate(sp => sp.openFile(file)); }
    openLocal(filename)          { this._delegate(sp => sp.openLocal(filename)); }

}
