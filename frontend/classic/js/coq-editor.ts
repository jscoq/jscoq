/* jsCoq
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2022 Shachar Itzhaky, Technion - Israel Institute of Technology, Haifa
 * Copyright (C) 2019-2022 Emilio J. Gallego Arias, Inria, Paris
 */
import { Diagnostic } from "../../../backend";

/**
 * Interface for Coq Editor's
 */
export interface ICoqEditor {
    getValue() : string;
    onChange() : void;
    onChangeRev(newContent, version) : void;
    clearMarks() : void;
    markDiagnostic(d : Diagnostic) : void;
    getCursorOffset() : number;
}

/**
 * Takes a textArea and will create an empty div to attach an editor to.
 * @param {(string | HTMLElement)} eId 
 * @returns {{container: HTMLDivElement, area: HTMLTextAreaElement}}
 */
export function editorAppend(eId) {

    var area = /** @type {HTMLTextAreaElement} */ 
        (eId instanceof HTMLElement ? eId : document.getElementById(eId));
    if (area.tagName !== 'TEXTAREA')
        throw new Error(`not implemented: '${eId}' must be a textarea`);

    area.style.display = 'none';

    // Create container for editor
    const container = document.createElement('div');
    container.setAttribute('spellCheck', "false");
    container.classList.add(...area.classList);

    if (area.nextSibling) {
        area.parentElement.insertBefore(container, area.nextSibling);
    } else {
        area.parentElement.appendChild(container);
    }
    return { container, area };
}

// Local Variables:
// js-indent-level: 4
// End:
