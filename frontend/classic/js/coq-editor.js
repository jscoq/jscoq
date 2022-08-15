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
// CodeMirror
import CodeMirror from 'codemirror';
import 'codemirror/addon/hint/show-hint.js';
import 'codemirror/addon/edit/matchbrackets.js';
import 'codemirror/keymap/emacs.js';
import 'codemirror/addon/selection/mark-selection.js';
import 'codemirror/addon/edit/matchbrackets.js';
import 'codemirror/addon/dialog/dialog.js';

// CM medias
import 'codemirror/lib/codemirror.css';
import 'codemirror/theme/blackboard.css';
import 'codemirror/theme/darcula.css';
import 'codemirror/addon/hint/show-hint.css';
import 'codemirror/addon/dialog/dialog.css';

import '../external/CodeMirror-TeX-input/addon/hint/tex-input-hint.js';
import './mode/coq-mode.js';

export class CoqCodeMirror {

    // element e
    constructor(e) {

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

        e = document.getElementById(e);

        if (e.tagName !== 'TEXTAREA') {
            console.log('Error, element must be a textarea');
        }

        this._set_keymap();
        this.editor = CodeMirror.fromTextArea(e, cmOpts);
        this.editor.on('change', (cm, evt) => this.onChange(cm, evt) );
        e.style.height = 'auto';
    }

    // To be overriden by the manager
    onChange(cm, evt) {
        return;
    }

    getValue() {
        return this.editor.getValue();
    }

    clearMarks() {
        for (let m of this.editor.getAllMarks()) {
            m.clear();
        }
    }

    markDiagnostic(d) {

        var from = { line: d.range.start.line, ch: d.range.start.character };
        var to = { line: d.range._end.line, ch: d.range._end.character };

        var doc = this.editor.getDoc();
        var mclass = (d.severity === 1) ? 'coq-eval-failed' : 'coq-eval-ok';

        doc.markText(from, to, {className: mclass});
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
