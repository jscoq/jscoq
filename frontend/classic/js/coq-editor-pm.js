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

import hljs from 'highlight.js/lib/core';
import coqhl from 'highlight.js/lib/languages/coq';
import { highlightPlugin } from "prosemirror-highlightjs"

hljs.registerLanguage('coq', coqhl);

import { editorAppend } from './coq-editor.js';

function diagNew(d) {
    var mark_class = (d.severity === 1) ? 'coq-eval-failed' : 'coq-eval-ok';
    return Decoration.inline(d.range.start_pos + 1, d.range.end_pos + 1, { class: mark_class });
}

// Implementation of Asynchronous diagnostics
//
// We use two transactions: `clear` to clear the diagnostics, and
// regular one that will just append to the DecorationSet.
//
// An interesting side-effect of cur.add taking a `doc` is that it is
// possible to have a race condition where a diagnostic transaction
// will revert a user-initiated one. We solve this with a guard on
// document versions. CM 6 doesn't see to suffer from this problem.
//
// The two entry points are:
//
// - onChange: this will notify the user the document has changed so
//   the linter can be called
// - markDiagnostic: used by the linter to notify a new diagnostic
// - clearMarks: clear all diagnostics, we put the logic in the user (for now)
let coqDiags = new Plugin({
    props: {
        decorations(st) {
            return this.getState(st);
        }
    },
    state: {
        init(_config,_instance) { return DecorationSet.empty },
        apply(tr, cur) {
            var d = tr.getMeta(coqDiags);
            if (d) {
                if(d === "clear") {
                    return DecorationSet.empty;
                } else {
                    return cur.add(tr.doc, [d])
                }
            } else {
                return cur.map(tr.mapping, tr.doc);
            }
        }
    }
})

export class CoqProseMirror {

    // eId must be a textarea
    constructor(eId) {

        let { container, area } = editorAppend(eId);

        var doc = defaultMarkdownParser.parse(area.value);
        var pm = this;

        this.version = 1;

        this.view =
            new EditorView(container, {
                state: EditorState.create({
                    doc: doc,
                    plugins: [...exampleSetup({schema: schema}), coqDiags]
                }),
                // We update the text area
                dispatchTransaction(tr) {
                    // Update textarea only if content has changed
                    if (tr.docChanged) {

                        // We update the version!
                        pm.version++;

                        let newDoc = CoqProseMirror.serializeDoc(tr.doc);
                        pm.onChange(newDoc, pm.version);

                        var newMarkdown = defaultMarkdownSerializer.serialize(tr.doc);
                        area.value = newMarkdown;
                    }

                    const { state } = this.state.applyTransaction(tr);
                    this.updateState(state);
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

    markDiagnostic(d, version) {
        // This is racy w.r.t. user edits if we don't check the
        // document version; async stuff, always fun :)
        if (version === this.version) {
            var tr = this.view.state.tr;
            tr.setMeta(coqDiags, diagNew(d));
            this.view.dispatch(tr);
        }
    }

    static process_node(acc) {
        return (node, pos, parent, index) => {
            if (node.type.name === schema.nodes.code_block.name) {
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
