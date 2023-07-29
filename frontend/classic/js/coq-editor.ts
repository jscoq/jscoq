/* jsCoq
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2023 Shachar Itzhaky, Technion - Israel Institute of Technology, Haifa
 * Copyright (C) 2019-2023 Emilio J. Gallego Arias, Inria, Paris
 */
import { Diagnostic } from "../../../backend";
import { CoqManager, ManagerOptions } from "./coq-manager";

/**
 * Interface for Coq Editor's
 */
export interface ICoqEditor {
    getValue() : string
    clearDiagnostics() : void
    markDiagnostic(diag : Diagnostic) : void
    getCursorOffset() : number
    destroy() : void
    configure(opts: any) : void
    openFile(file: File) : void
    focus() : void
}

// Would be great to use, but not enough typing so far...
export interface ICoqEditorConstructor {
    new(elems : (string | HTMLElement)[],
        options: ManagerOptions,
        onChange: (newContent : string) => void,
        onCursorUpdated: (offset : number) => void) : ICoqEditor;
    }
/**
 * Takes a textArea and will create an empty div to attach an editor to.
 */
export function editorAppend(eId) : { container : HTMLDivElement, area : HTMLTextAreaElement } {

    var area : HTMLTextAreaElement =
        (eId instanceof HTMLTextAreaElement ? eId
             : document.getElementById(eId) as HTMLTextAreaElement);

    if (! (area instanceof HTMLTextAreaElement))
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
