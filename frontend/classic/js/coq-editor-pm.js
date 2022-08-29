//@ts-check
"use strict";

// Prosemirror implementation
import { EditorView } from 'prosemirror-view';
import { EditorState } from 'prosemirror-state';
// import { DOMParser } from 'prosemirror-model';
import { schema, defaultMarkdownParser, defaultMarkdownSerializer } from 'prosemirror-markdown';
import { exampleSetup } from 'prosemirror-example-setup';

import 'prosemirror-view/style/prosemirror.css';
import 'prosemirror-menu/style/menu.css';
import 'prosemirror-example-setup/style/style.css';

import { editorAppend } from './coq-editor.js';

export class CoqProseMirror {

    // eId must be a textarea
    constructor(eId) {

        let { container, area } = editorAppend(eId);

        var doc = defaultMarkdownParser.parse(area.value);
        var obj_ref = this;

        this.view =
            new EditorView(container, {
                state: EditorState.create({
                    doc: doc,
                    plugins: exampleSetup({schema: schema})
                }),
                // We update the text area
                dispatchTransaction(tr) {
                    const { state } = this.state.applyTransaction(tr);
                    this.updateState(state);
                    // Update textarea only if content has changed
                    if (tr.docChanged) {
                        var newText = defaultMarkdownSerializer.serialize(tr.doc);
                        area.value = newText;
                        obj_ref.onChange(newText);
                    }
                },
            });

        this.view.focus();
    }

    getValue() {
        return defaultMarkdownSerializer.serialize(this.view.state.doc)
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

// Local Variables:
// js-indent-level: 4
// End:
