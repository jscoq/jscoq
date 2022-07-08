import { EventEmitter } from 'events';
import { Extension, StateField, StateEffect, EditorSelection } from '@codemirror/state';
import { EditorView, lineNumbers, keymap, highlightActiveLine,
         highlightActiveLineGutter, WidgetType, ViewPlugin,
         DecorationSet, Decoration } from '@codemirror/view';
import { syntaxHighlighting, defaultHighlightStyle,
         syntaxTree } from '@codemirror/language';
import { defaultKeymap, indentWithTab } from '@codemirror/commands';
import { coqLanguageSupport } from './mode/coq-lang';


const changeGeneration = StateField.define<number>({
    create(state) { return 0; },
    update(value, tr) { return value + 1; }
});

const events = StateField.define<EventEmitter>({
    create(state) { return new EventEmitter; },
    update(value, tr) {
        if (tr.newSelection !== tr.startState.selection)
            defer(() => value.emit('cursorActivity', tr));
        return value;
    }
});

const addMark = StateEffect.define<{
        from: number, to: number, class: string,
        obj: {}, attrs?: {[name: string]: string}
    }>();
const clearMark = StateEffect.define<{obj: {}}>();

const markField = StateField.define<DecorationSet>({
    create() {
        return Decoration.none
    },
    update(marks, tr) {
        marks = marks.map(tr.changes)
        for (let e of tr.effects) {
            if (e.is(addMark)) {
                let spec = Decoration.mark({class: e.value.class,
                            obj: e.value.obj, attributes: e.value.attrs});
                marks = marks.update({
                    add: [spec.range(e.value.from, e.value.to)],
                })
            }
            else if (e.is(clearMark)) {
                marks = marks.update({
                    filter: (from, to, value) => value.spec.obj !== e.value.obj
                })
            }
        }
        return marks;
    },
    provide: f => EditorView.decorations.from(f)
});


function setup(): Extension[] { return [
    keymap.of([{key: "Mod-Enter", run: () => true}]),
    keymap.of(defaultKeymap), keymap.of([indentWithTab]),
    lineNumbers(), highlightActiveLine(), highlightActiveLineGutter(),
    syntaxHighlighting(defaultHighlightStyle, {fallback: true}),
    coqLanguageSupport(),
    changeGeneration, events, markField
]; }




class EditorViewWithBenefits extends EditorView {

    getValue() { return this.state.sliceDoc(); }

    setCursor(pos: number | LineCh) {
        if (typeof pos !== 'number') pos = this.posToOffset(pos)
        this.dispatch({
            selection: EditorSelection.create([EditorSelection.cursor(pos)]),
            effects: EditorView.scrollIntoView(pos, {y: 'nearest'})
        });
    }

    getCursorOffset(w: 'head' | 'from' | 'to' = 'head') {
        return this.state.selection.asSingle().ranges[0][w];
    }

    getCursor(w?: 'head' | 'from' | 'to') {
        return this.offsetToPos(this.getCursorOffset(w));
    }

    posToOffset(pos: LineCh): number {
        return this.state.doc.line(pos.line).from + pos.ch;
    }

    offsetToPos(offset: number) {
        let line = this.state.doc.lineAt(offset);
        return {line: line.number, ch: offset - line.from};
    }

    scrollTo(scroll: {top?: number, left?: number}) {
        if (scroll.left !== undefined) this.scrollDOM.scrollLeft = scroll.left;
        if (scroll.top !== undefined) this.scrollDOM.scrollTop = scroll.top;
    }

    getScroll() {
        let s = this.scrollDOM;
        return {top: s.scrollTop, left: s.scrollLeft};
    }

    syntaxTree() {
        return syntaxTree(this.state);
    }

    on(eventType: string, handler: (...args: any[]) => void) {
        this.state.field(events).on(eventType, handler);
    }
}


type LineCh = {line: number, ch: number};


/** A crutch because LiveScript code cannot extend ES6 classes :/ */
function createWidgetPlugin(factory: () => HTMLElement) {
    class WidgetWrapper extends WidgetType {
        toDOM(view: EditorView): HTMLElement { return factory(); }
    }

    return ViewPlugin.fromClass(class {
        decorations: DecorationSet
        constructor(view: EditorView) {
            this.decorations = Decoration.set(Decoration.widget({
                widget: new WidgetWrapper,
                side: 1
            }).range(view.state.doc.length));
        }
    }, {decorations: v => v.decorations});
}


function defer<T>(op: () => T) { Promise.resolve().then(op); }


export { EditorState } from '@codemirror/state';
export { setup, changeGeneration, events, markField, addMark, clearMark,
         EditorViewWithBenefits, LineCh,
         createWidgetPlugin }