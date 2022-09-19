//@ts-check
"use strict";

// Prosemirror implementation
import { EditorView, Decoration, DecorationSet } from 'prosemirror-view';
import { EditorState, Plugin } from 'prosemirror-state';
import { DOMParser } from 'prosemirror-model';
import { schema, defaultMarkdownParser, defaultMarkdownSerializer } from 'prosemirror-markdown';
import { exampleSetup } from 'prosemirror-example-setup';

import 'prosemirror-view/style/prosemirror.css';
import 'prosemirror-menu/style/menu.css';
import 'prosemirror-example-setup/style/style.css';

import { editorAppend } from './coq-editor.js';

function diagNew(d) {
    var mark_class = (d.severity === 1) ? 'coq-eval-failed' : 'coq-eval-ok';
    return Decoration.inline(d.range.start_pos + 1, d.range.end_pos + 1, { class: mark_class });
}

function diagMap(tr) {
    return (d) => {
        var new_d = {...d};
        new_d.range.start_pos = tr.mapping.map(d.range.start_pos);
        new_d.range.end_pos = tr.mapping.map(d.range.end_pos);
        return new_d;
    }
}

function diagDecorations(doc, diags) {

    // console.log(diags);
    let ds = DecorationSet.create(doc, diags.map(diagNew));
    return ds;

}

let coqDiags = new Plugin({
    props: {
        decorations(st) {
            let diags = this.getState(st);
            return diagDecorations(st.doc, diags);
        }
    },
    state: {
        init(_config,_instance) { return [] },
        apply(tr, cur) {
            var m = tr.getMeta(coqDiags);
            if (m) {
                if(m == "clear") {
                    return [];
                } else {
                    return cur.concat([m])
                }
            } else {
                let mapping = diagMap(tr);
                return cur.map(mapping);
            }
        }
    }
})

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
                    plugins: [...exampleSetup({schema: schema}), coqDiags]
                }),
                // We update the text area
                dispatchTransaction(tr) {
                    const { state } = this.state.applyTransaction(tr);
                    this.updateState(state);

                    // Update textarea only if content has changed
                    if (tr.docChanged) {
                        let newDoc = CoqProseMirror.serializeDoc(tr.doc);
                        obj_ref.onChange(newDoc);

                        var newMarkdown = defaultMarkdownSerializer.serialize(tr.doc);
                        area.value = newMarkdown;
                    }
                },
            });

        this.view.focus();
    }

    static serializeDoc(doc) {
        var acc = [];
        doc.descendants(CoqProseMirror.process_node(acc));
        let res = CoqProseMirror.flatten_chunks(acc);
        return res;
    }

    getValue() {
        return CoqProseMirror.serializeDoc(this.view.state.doc);
    }

    onChange(newText) {
        return;
    }

    clearMarks() {
        var tr = this.view.state.tr;
        tr.setMeta(coqDiags, "clear");
        this.view.dispatch(tr);
    }

    markDiagnostic(d) {

        var from = d.range.start_pos, to = d.range.end_pos;

        console.log("mark from " + from.toString() + " to " + to.toString());

        var tr = this.view.state.tr;
        tr.setMeta(coqDiags, d);
        this.view.dispatch(tr);

    }

    static process_node(acc) {
        return (node, pos, parent, index) => {
            if (node.type.name == 'code_block') {
                let text = node.textContent;
                acc.push( { pos, text } );
                return true;
            }
        }
    }

    static flatten_chunks(acc) {
        var res = "";
        for (let c of acc) {
            let offset = c.pos - res.length;
            res += ' '.repeat(offset) + c.text;
        }
        return res;
    }
}

// Local Variables:
// js-indent-level: 4
// End:
