// CodeMirror implementation
import { EditorState, RangeSet, Facet, StateEffect, StateField } from "@codemirror/state";
import { EditorView, lineNumbers, Decoration, ViewPlugin } from "@codemirror/view";
import { Diagnostic } from "../../../backend/coq-worker";
import { ICoqEditor, editorAppend } from "./coq-editor";
import { CoqDocument } from "./coq-manager";

// import './mode/coq-mode.js';

const clearDiag = StateEffect.define<{}>({});
const addDiag = StateEffect.define<{ from: number, to : number, d : Decoration }>(
    { map: ({from, to, d}, change) => ({from: change.mapPos(from), to: change.mapPos(to), d}) });

const diagField = StateField.define({

  create() {
      return RangeSet.empty;
  },

  update(diags, tr) {

      diags = diags.map(tr.changes);

      for (let e of tr.effects) {
          if (e.is(addDiag)) {
              diags = diags.update({
                  add: [e.value.d.range(e.value.from, e.value.to)]
              })
          } else if (e.is(clearDiag)) {
              diags = RangeSet.empty;
          }
      };

      return diags;
  },
  provide: f => EditorView.decorations.from(f)
})

export class CoqCodeMirror6 implements ICoqEditor {
    private view : EditorView;

    // element e
    constructor(doc: CoqDocument, options) {

        var extensions =
            [diagField,
                lineNumbers(),
                EditorView.updateListener.of(v => {
                    if (v.docChanged) {
                        // Document changed
                        var newText = v.state.doc.toString();
                        doc.change(newText);
                    }
                    // Careful to run this _after_ doc is changed in the model
                    if (v.selectionSet) {
                        doc.updateCursor(v.state.selection.main.head);
                    }
                })
            ];

        var state = EditorState.create( { doc: doc.getValue(), extensions } );

        this.view = new EditorView(
            { state,
              parent: doc.container,
              extensions
            });
    }

    getValue() {
        return this.view.state.doc.toString();
    }

    clearDiagnostics() {
        var tr = { effects: clearDiag.of({}) };
        this.view.dispatch(tr);
    }

    markDiagnostic(d: Diagnostic) {

        var from = d.range.start.offset, to = d.range.end.offset;

        var mclass = (d.severity === 1) ? 'coq-eval-failed' : 'coq-eval-ok';
        const diagMark = Decoration.mark( { class: mclass } );

        var tr = { effects: addDiag.of({ from, to, d : diagMark }) };
        this.view.dispatch(tr);

        // Debug code.
        {
            let from = { line: d.range.start.line, ch: d.range.start.character },
                to = { line: d.range.end.line, ch: d.range.end.character };

            console.log(`mark from (${from.line},${from.ch}) to (${to.line},${to.ch}) class: ${mclass}`);
            if (d.extra) console.log('extra: ', d.extra);
        }
    }

    getCursorOffset(): number {
        return this.view.state.selection.main.head;
    }

    destroy() {
        this.view.destroy();
    }
    configure() {}
    openFile() {}
    focus() {}
}

// Local Variables:
// js-indent-level: 4
// End:
