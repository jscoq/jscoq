// Prosemirror implementation
import { EditorView } from 'prosemirror-view';
import { EditorState } from 'prosemirror-state';
// import { DOMParser } from 'prosemirror-model';
import { schema, defaultMarkdownParser, defaultMarkdownSerializer } from 'prosemirror-markdown';
import { exampleSetup } from 'prosemirror-example-setup';

import 'prosemirror-view/style/prosemirror.css';
import 'prosemirror-menu/style/menu.css';
import 'prosemirror-example-setup/style/style.css';
import { Diagnostic } from '../../../backend';

export class CoqProseMirror {
    view : EditorView;

    // eId must be a textarea
    constructor(eIds : string []) {

        var area = document.getElementById(eIds[0]) as HTMLTextAreaElement;

        area.style.display = 'none';

        // Create container for editor
        const container = document.createElement('div');
        container.classList = area.classList;

        if (area.nextSibling) {
            area.parentElement.insertBefore(container, area.nextSibling);
        } else {
            area.parentElement.appendChild(container);
        }

        var doc = defaultMarkdownParser.parse(area.value);

        var editor = this;
        this.view =
            new EditorView(container, {
                state: EditorState.create({
                    doc: doc,
                    plugins: exampleSetup({schema})
                }),
                // We update the text area
                dispatchTransaction(tr) {
                    const { state } = this.state.applyTransaction(tr);
                    this.updateState(state);
                    // Update textarea only if content has changed
                    if (tr.docChanged) {
                        var newText = defaultMarkdownSerializer.serialize(tr.doc);
                        area.value = newText;
                        editor.onChange(newText);
                    }
                },
            });

        this.view.focus();
    }

    getValue() {
        return defaultMarkdownSerializer.serialize(this.view.state.doc)
    }

    onChange(newText : string) {
        return;
    }

    clearMarks() {
        return;
    }

    markDiagnostic(d : Diagnostic) {

        var from = d.range.start.offset, to = d.range.end.offset;

        console.log("mark from " + from.toString() + " to " + to.toString());
        return;

        var mark_class = (d.severity === 1) ? 'coq-eval-failed' : 'coq-eval-ok';

        // from prosemirror transform
        var tr = addMark(from, to, mark);

        this.view.state.applyTransaction(tr);

        return;
    }
}

