// @ts-check
"use strict";

import { CmCoqProvider } from "./coq-editor-cm5.js";
import { Deprettify } from "./deprettify.js";

/**
 * A Provider Container aggregates several containers, presenting
 * a semblance of a single document.
 * The main issue here is to handle marks, which may reside in different
 * parts and may even span multiple parts.
 *
 * @class ProviderContainer
 */
export class ProviderContainer {

    /**
     * Creates an instance of ProviderContainer.
     * 
     * @param {(string | HTMLElement)[]} elementRefs
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
        this.onChange = () => {};
        this.onInvalidate = (mark) => {};
        this.onMouseEnter = (stm, ev) => {};
        this.onMouseLeave = (stm, ev) => {};
        this.onTipHover = (entries, zoom) => {};
        this.onTipOut = () => {};
        this.onAction = (action) => {};
        this.wait_for = null;
        
        class WhileScrolling {
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

        //CmCoqProvider._set_keymap();

        // Create sub-providers.
        //   Do this asynchronously to avoid locking the page when there is
        //   a large number of snippets.
        (async () => {
            var i = 0, scroll = new WhileScrolling();

            for (let [idx, element] of this.findElements(elementRefs).entries()) {

                if (this.options.replace)
                    element = Deprettify.trim(element);

                // Init.
                let cm = new CmCoqProvider(element, this.options, this.options.replace, idx);

                this.snippets.push(cm);

                // Track focus XXX (make generic)
                cm.editor.on('focus', ev => { this.currentFocus = cm; });

                // Track invalidate
                cm.onChange     = ()        => { this.onChange(); };
                cm.onInvalidate = (stm)     => { this.onInvalidate(stm); };
                cm.onMouseEnter = (stm, ev) => { this.onMouseEnter(stm, ev); };
                cm.onMouseLeave = (stm, ev) => { this.onMouseLeave(stm, ev); };

                cm.onTipHover = (entries, zoom) => { this.onTipHover(entries, zoom); };
                cm.onTipOut   = ()              => { this.onTipOut(); }

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
     * @param {(string | HTMLElement)[]} elementRefs
     * @return {HTMLElement[]}
     * @memberof ProviderContainer
     */
    findElements(elementRefs) {
        var elements = [];
        for (let e of elementRefs) {
            var els = (typeof e === 'string') ?
                [document.getElementById(e), ...document.querySelectorAll(e)] : [e];
            els = els.filter(x => x);
            if (els.length === 0) {
                console.warn(`[jsCoq] element(s) not found: '${e}'`);
            }
            elements.push(...els);
        }
        return /** @type {HTMLElement[]} */(elements);
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
