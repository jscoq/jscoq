// CodeMirror implementation
import { EditorState, RangeSet, Facet, StateEffect, StateField } from "@codemirror/state";
import { EditorView, lineNumbers, Decoration, ViewPlugin } from "@codemirror/view";
import { Diagnostic } from "../../../backend";
import { ICoqEditor, editorAppend } from "./coq-editor";

// import './mode/coq-mode.js';

const clearDiag = StateEffect.define<{}>({});

const addDiag = StateEffect.define<{from : number, to: number, d : Decoration}>(
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
    view : EditorView;

    // element e
    constructor(eIds : string[]) {

        let { container, area } = editorAppend(eIds[0]);

        var obj_ref = this;

        // this._set_keymap();

        var extensions =
            [ diagField,
              lineNumbers(),
              EditorView.updateListener.of(v => {
                  if (v.docChanged) {
                      // Document changed
                      var newText = v.state.doc.toString();
                      area.value = newText;
                      obj_ref.onChange(newText);
                  }})
            ];

        var state = EditorState.create( { doc: area.value, extensions } );

        this.view = new EditorView(
            { state,
              parent: container,
              extensions
            });

    }

    // To be overriden by the manager
    onChange(cm) {
        return;
    }

    getValue() {
        return this.view.state.doc.toString();
    }

    clearMarks() {
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
        var from_ = { line: d.range.start.line, ch: d.range.start.character };
        var to_ = { line: d.range.end.line, ch: d.range.end.character };

        console.log(`mark from (${from_.line},${from_.ch}) to (${to_.line},${to_.ch}) class: ${mclass}`);

        // var d = new Decoration(from, to);
        // var doc = this.editor.getDoc();
        // doc.markText(from, to, {className: mclass});
    }

    getCursorOffset(): number {
        return this.view.state.selection.main.head;
    }

    configure() {}
    openFile() {}
    focus() {}
}
