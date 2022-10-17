//@ts-check
"use strict";

// CodeMirror implementation
import { EditorState, RangeSet, Facet, StateEffect, StateField } from "@codemirror/state";
import { EditorView, lineNumbers, Decoration, ViewPlugin } from "@codemirror/view";

import { editorAppend } from './coq-editor';

// import './mode/coq-mode.js';

const clearDiag = StateEffect.define({});

const addDiag = StateEffect.define(
    { map: ({from, to}, change) => ({from: change.mapPos(from), to: change.mapPos(to)}) });

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

/**
 * @typedef { import("./coq-editor").ICoqEditor } ICoqEditor
 */

/** Interface for CM5
 * @implements ICoqEditor
 */
export class CoqCodeMirror6 {

    /**
     * Initializes a CodeMirror 6 instance in the specified element.
     * @param {(string | HTMLElement)[]} elementRefs (must be of length 1)
     */
    constructor(elementRefs) {

        if (elementRefs.length != 1)
            throw new Error('not implemented: `cm6` frontend requires a single element')

        let { container, area } = editorAppend(elementRefs[0]);

        var cm = this;

        this.version = 1;

        // this._set_keymap();

        var extensions =
            [ diagField,
              lineNumbers(),
              EditorView.updateListener.of(v => {
                  if (v.docChanged) {
                      // Document changed
                      var newText = v.state.doc.toString();
                      area.value = newText;
                      cm.version++;
                      cm.onChangeRev(newText, cm.version);
                  }})
            ];

        var state = EditorState.create( { doc: area.value, extensions } );

        this.view = new EditorView(
            { state,
              parent: container,
              extensions
            });

    }

    // To be overriden by the manager as to provide diagnostics
    onChange() { }
    onChangeRev(newText, version) { }

    getValue() {
        return this.view.state.doc.toString();
    }

    clearMarks() {
        var tr = { effects: clearDiag.of({}) };
        this.view.dispatch(tr);
    }

    getCursorOffset() {
        return this.view.state.selection.main.head;
    }

    markDiagnostic(d, version) {

        if (version < this.version) { return; };

        var from = d.range.start.offset, to = d.range._end.offset;

        var mclass = (d.severity === 1) ? 'coq-eval-failed' : 'coq-eval-ok';
        const diagMark = Decoration.mark( { class: mclass } );

        var tr = { effects: addDiag.of({ from, to, d : diagMark }) };
        this.view.dispatch(tr);

        // Debug code.
        {
            let from = { line: d.range.start.line, ch: d.range.start.character },
                to = { line: d.range._end.line, ch: d.range._end.character };

            console.log(`mark from (${from.line},${from.ch}) to (${to.line},${to.ch}) class: ${mclass}`);
            if (d.extra) console.log('extra: ', d.extra);
        }

        // var d = new Decoration(from, to);
        // var doc = this.editor.getDoc();
        // doc.markText(from, to, {className: mclass});
    }
}

// Local Variables:
// js-indent-level: 4
// End:
