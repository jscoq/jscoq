//@ts-check
"use strict";

// CodeMirror implementation
import { EditorState, RangeSet, Facet, StateEffect, StateField } from "@codemirror/state";
import { EditorView, lineNumbers, Decoration, ViewPlugin } from "@codemirror/view";

import { editorAppend } from './coq-editor.js';

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

export class CoqCodeMirror {


    // element e
    constructor(eId) {

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

        let { container, area } = editorAppend(eId);

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

    // To be overriden by the manager as to provide diagnostics
    onChange(newText) {
        return;
    }

    getValue() {
        return this.view.state.doc.toString();
    }

    clearMarks() {
        var tr = { effects: clearDiag.of({}) };
        this.view.dispatch(tr);
    }

    markDiagnostic(d) {

        var from = d.range.start_pos, to = d.range.end_pos;

        var mclass = (d.severity === 1) ? 'coq-eval-failed' : 'coq-eval-ok';
        const diagMark = Decoration.mark( { class: mclass } );

        var tr = { effects: addDiag.of({ from, to, d : diagMark }) };
        this.view.dispatch(tr);

        // Debug code.
        var from = { line: d.range.start.line, ch: d.range.start.character };
        var to = { line: d.range._end.line, ch: d.range._end.character };

        console.log(`mark from (${from.line},${from.ch}) to (${to.line},${to.ch}) class: ${mclass}`);

        // var d = new Decoration(from, to);
        // var doc = this.editor.getDoc();
        // doc.markText(from, to, {className: mclass});
    }

    _set_keymap() {

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
    }
}

// Local Variables:
// js-indent-level: 4
// End:
