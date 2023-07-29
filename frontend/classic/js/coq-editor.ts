/* jsCoq
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2023 Shachar Itzhaky, Technion - Israel Institute of Technology, Haifa
 * Copyright (C) 2019-2023 Emilio J. Gallego Arias, Inria, Paris
 */
import { Diagnostic } from "../../../backend";
import { CoqDocument } from "./coq-document";
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

    doc : CoqDocument
    manager: CoqManager
    connectWorker() : void;

    // Clean up the editor view, removing its element from the
    // document, unregistering event handlers, and notifying clients.
    destroy() : void
}

export interface ICoqEditorConstructor {
    new(doc : CoqDocument,
        manager: CoqManager,
        container: HTMLDivElement,
        onChange: (doc: CoqDocument) => void,
        onCursorUpdated: (offset : number) => void) : ICoqEditor;
}

/**
 * Takes a textArea and will create an empty div to attach an editor to.
 */
function editorAppend(eId) : { container : HTMLDivElement, area : HTMLTextAreaElement } {

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

/**
 * Create an empty div to attach an editor.
 */
export function createEditorContainer() : HTMLDivElement {
    // Create container for editor
    const container = document.createElement('div');
    container.setAttribute('spellCheck', "false");
    const parent_id = 'editors';
    let parent = document.getElementById(parent_id);
    if (!parent) {
        const wrapper_id = 'ide-wrapper'
        const wrapper_elem = document.getElementById(wrapper_id);
        if (!wrapper_elem)
            throw new Error(`wrapper element '${wrapper_id}' not found`);
        let p = document.createElement('div');
        p.setAttribute('id', parent_id);
        wrapper_elem.appendChild(p);
        parent = p;
    }
    parent.appendChild(container);
    return container;
}
