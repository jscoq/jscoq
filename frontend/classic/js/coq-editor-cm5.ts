/**
 * An implementation of `CoqEditor` for CodeMirror 5.
 */
// CodeMirror implementation
import { Diagnostic } from '../../../backend';
import { ProviderContainer } from './cm-provider-container';
import { ICoqEditor } from './coq-editor';
import { CoqManager } from './coq-manager';

interface CM5Options {
    mode?: { "company-coq": boolean }
}

export class CoqCodeMirror5 extends ProviderContainer implements ICoqEditor {
    manager : CoqManager;

    constructor(eIds: (string|HTMLElement)[], options : any, manager : CoqManager) {

        // CoqCodeMirror5._set_keymap();
        super(eIds, options);
        this.manager = manager;

        this.onChangeAny = () => {
            let txt = this.getValue();
            this.onChange(txt);
        };

        // if (this.options.mode && this.options.mode['company-coq']) {
        //     this.company_coq = new CompanyCoq(this.manager);
        //     this.company_coq.attach(this.editor);
        // }
    }

    // To be overriden by the manager
    onChange(txt) { }

    // To be overriden by the manager
    getValue() {
        return this.snippets.map(part => part.getValue()).join('\n');
    }

    clearMarks() {
        for (let part of this.snippets)
            part.retract();
    }

    markDiagnostic(diag: Diagnostic) {
        console.log(diag);
        // Find the part that contains the target line
        let ln = 0, start_ln = diag.range.start.line;
        var in_part = this.snippets[0];
        for (let part of this.snippets) {
            let nlines = part.editor.lineCount();
            if (start_ln >= ln && start_ln < ln + nlines) {
                in_part = part;
                break;
            }
            else {
                ln += nlines;
            }
        }
        // Adjust the mark for the line offset
        diag.range.start.line -= ln;
        diag.range.end.line -= ln;
        in_part.mark(diag);
    }
}
