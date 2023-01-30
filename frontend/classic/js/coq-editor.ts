/* jsCoq
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2022 Shachar Itzhaky, Technion - Israel Institute of Technology, Haifa
 * Copyright (C) 2019-2022 Emilio J. Gallego Arias, Inria, Paris
 */
import { Diagnostic } from "../../../backend";
import { CoqManager, ManagerOptions } from "./coq-manager";

/**
 * Interface for Coq Editor's
 */
export interface ICoqEditor {
    getValue() : string
    markDiagnostic(diag : Diagnostic) : void
    getCursorOffset() : number
    configure(opts: any) : void
    openFile(file: File) : void
    focus() : void
}

// Would be great to use, but not enough typing so far...
export type DiagnosticEvent = {
    diags : Diagnostic[];
    version : number;
}

export interface ICoqEditorConstructor {
    new(elems : (string | HTMLElement)[],
        options: ManagerOptions,
        onChange: (newContent : string) => void,
        diagsSource: EventTarget,
        manager: CoqManager) : ICoqEditor;
    }

// Takes a textArea and will create an empty div to attach an editor
// to.
export function editorAppend(eId) : { container, area: HTMLTextAreaElement} {

    // var area = document.getElementById(eId) as HTMLTextAreaElement;

    var area : HTMLTextAreaElement =
        (eId instanceof HTMLTextAreaElement ? eId
             : document.getElementById(eId) as HTMLTextAreaElement);

    if (area.tagName !== 'TEXTAREA')
        throw new Error(`not implemented: '${eId}' must be a textarea`);

    area.style.display = 'none';

    // Create container for editor
    const container = document.createElement('div');
    container.setAttribute('spellCheck', "false");
    container.classList.add(...area.classList);

    if (area.nextSibling) {
        area.parentElement?.insertBefore(container, area.nextSibling);
    } else {
        area.parentElement?.appendChild(container);
    }
    return { container, area };
}
