/**
 * An implementation of `CoqEditor` for CodeMirror 5.
 */
// CodeMirror implementation
import { Diagnostic } from '../../../backend';
import { ProviderContainer } from './cm-provider-container';
import { ManagerOptions } from './coq-manager';
import { ICoqEditor } from './coq-editor';

interface CM5Options {
    mode?: { "company-coq": boolean }
}

// Big TODO: A few operations only work for the first snippet, need to fix.
// Search for snippets[0]

/** Interface for CM5 */
export class CoqCodeMirror5 extends ProviderContainer implements ICoqEditor {

    constructor(eIds: (string | HTMLElement)[], options : ManagerOptions, onChange, onCursorUpdate) {

        super(eIds, options);

        this.onChangeAny = () => {
            let txt = this.getValue();
            onChange(txt);
        };
        this.onCursorUpdate = (cm) => {
            onCursorUpdate(this.getCursorOffset());
        }
        // if (this.options.mode && this.options.mode['company-coq']) {
        //     this.company_coq = new CompanyCoq(this.manager);
        //     this.company_coq.attach(this.editor);
        // }
    }

    getValue() {
        return this.snippets.map(part => part.editor.getValue()).join('\n');
    }

    clearDiagnostics() {
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

    getCursorOffset(): number {
        return this.snippets[0].getCursorOffset();
    }
}
