import { EditorState, Extension, StateField } from '@codemirror/state';
import { EditorView, Decoration, DecorationSet, WidgetType, ViewUpdate, ViewPlugin } from '@codemirror/view';
import { syntaxTree } from "@codemirror/language";


class CompanyCoq {
    scanDocument(state: EditorState) {
        let c = syntaxTree(state).cursor(),
            decorations = [];
        do {
            if (!c.node.firstChild) {
                let tok = state.sliceDoc(c.from, c.to);
                if (c.name === 'Keyword' && tok === 'exists') {
                    let spec = Decoration.replace({widget: new SymbolWidget('∃')});
                    decorations.push(spec.range(c.from, c.to));
                }
            }
        } while (c.next());
        return decorations;
    }

    static field = StateField.define<CompanyCoq>({
        create() { return new CompanyCoq; },
        update(value, transaction) { return value; }
    });

    static get(state: EditorState) {
        return state.field(CompanyCoq.field);
    }
}


class SymbolWidget extends WidgetType {
    constructor(public text: string) { super(); }
    toDOM(view: EditorView): HTMLElement {
        let span = document.createElement('span');
        span.textContent = this.text;
        return span;
    }
}


const decorateSymbols = ViewPlugin.fromClass(class {
    decorations: DecorationSet;

    constructor(view: EditorView) {
        this.decorations = this.scanDocument(view.state);
    }

    update(update: ViewUpdate) {
        /* (this is needed if decorations are updated incrementally)
        for (let tr of update.transactions)
            this.decorations = this.decorations.map(tr.changes);
        */
        this.decorations = this.scanDocument(update.state);
    }

    scanDocument(state: EditorState) {
        return Decoration.set(CompanyCoq.get(state).scanDocument(state));
    }
}, {
    decorations: v => v.decorations,
    provide: plugin => EditorView.atomicRanges.of(view => {
        let value = view.plugin(plugin)
        return value ? value.decorations : Decoration.none
    })
});

const companyCoq: Extension = [CompanyCoq.field, decorateSymbols];


export { CompanyCoq, companyCoq }