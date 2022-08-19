/* jsCoq
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2022 Shachar Itzhaky, Technion - Israel Institute of Technology, Haifa
 * Copyright (C) 2019-2022 Emilio J. Gallego Arias, Inria, Paris
 */

"use strict";

/**
 * Interface for Coq Editor's
 *
 * @interface
 */
class ICoqEditor {

    getValue() { }

    onChange(newContent) { }

    clearMarks() { }

    markDiagnostic(diag) { }
}

// Takes a textArea and will create an empty div to attach an editor
// to.
function editorAppend(eId) {

    var area = document.getElementById(eId);

    area.style.display = 'none';

    // Create container for editor
    const container = document.createElement('div');
    container.classList = area.classList;

    if (area.nextSibling) {
        area.parentElement.insertBefore(container, area.nextSibling);
    } else {
        area.parentElement.appendChild(container);
    }
    return { container, area };
}

// Prosemirror implementation
import { EditorView } from 'prosemirror-view';
import { EditorState } from 'prosemirror-state';
// import { DOMParser } from 'prosemirror-model';
import { schema, defaultMarkdownParser, defaultMarkdownSerializer } from 'prosemirror-markdown';
import { exampleSetup } from 'prosemirror-example-setup';

import 'prosemirror-view/style/prosemirror.css';
import 'prosemirror-menu/style/menu.css';
import 'prosemirror-example-setup/style/style.css';

export class CoqProseMirror {

    // eId must be a textarea
    constructor(eId) {

        let { container, area } = editorAppend(eId);

        var doc = PM.defaultMarkdownParser.parse(area.value);
        var obj_ref = this;

        this.view =
            new PM.EditorView(container, {
                state: PM.EditorState.create({
                    doc: doc,
                    plugins: PM.exampleSetup({schema: PM.schema})
                }),
                // We update the text area
                dispatchTransaction(tr) {
                    const { state } = this.state.applyTransaction(tr);
                    this.updateState(state);
                    // Update textarea only if content has changed
                    if (tr.docChanged) {
                        var newText = PM.defaultMarkdownSerializer.serialize(tr.doc);
                        area.value = newText;
                        obj_ref.onChange(newText);
                    }
                },
            });

        this.view.focus();
    }

    getValue() {
        return PM.defaultMarkdownSerializer.serialize(this.view.state.doc)
    }

    onChange(newText) {
        return;
    }

    clearMarks() {
        return;
    }

    markDiagnostic(d) {

        var from = d.range.start_pos, to = d.range.end_pos;

        console.log("mark from " + from.toString() + " to " + to.toString());
        return;

        var mark_class = (d.severity === 1) ? 'coq-eval-failed' : 'coq-eval-ok';

        // from prosemirror transform
        var tr = addMark(from, to, mark);

        this.view.state.dispatchTransaction(tr);

        return;
    }

}

// CodeMirror implementation
import { EditorState, RangeSet, Facet, StateEffect, StateField } from "@codemirror/state";
import { EditorView, lineNumbers, Decoration, ViewPlugin } from "@codemirror/view";

// import './mode/coq-mode.js';

const clearDiag = CM.StateEffect.define({});

const addDiag = CM.StateEffect.define(
    { map: ({from, to}, change) => ({from: change.mapPos(from), to: change.mapPos(to)}) });

const diagField = CM.StateField.define({

  create() {
      return CM.RangeSet.empty;
  },

  update(diags, tr) {

      diags = diags.map(tr.changes);

      for (let e of tr.effects) {
          if (e.is(addDiag)) {
              diags = diags.update({
                  add: [e.value.d.range(e.value.from, e.value.to)]
              })
          } else if (e.is(clearDiag)) {
              diags = CM.RangeSet.empty;
          }
      };

      return diags;
  },
  provide: f => CM.EditorView.decorations.from(f)
})
>>>>>>> c6d9877 ([codemirror] Very basic CM 6.x port)

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
              CM.lineNumbers(),
              CM.EditorView.updateListener.of(v => {
                  if (v.docChanged) {
                      // Document changed
                      var newText = v.state.doc.toString();
                      area.value = newText;
                      obj_ref.onChange(newText);
                  }})
            ];

        var state = CM.EditorState.create( { doc: area.value, extensions } );

        this.view = new CM.EditorView(
            { state,
              parent: container,
              extensions
            });

    }

    // To be overriden by the manager
    onChange(cm, evt) {
        return;
    }

    getValue() {
        return this.view.state.doc.toString();
    }

    clearMarks() {
        var tr = { effects: clearDiag.of({}) };
        this.view.dispatch(tr);
    }

    buildDecSet() {
        return this.decorationSet;
    }

    markDiagnostic(d) {

        var from = d.range.start_pos, to = d.range.end_pos;

        var mclass = (d.severity === 1) ? 'coq-eval-failed' : 'coq-eval-ok';
        const diagMark = CM.Decoration.mark( { class: mclass } );

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
