//@ts-check
"use strict";

/* jsCoq
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2022 Shachar Itzhaky, Technion - Israel Institute of Technology, Haifa
 * Copyright (C) 2019-2022 Emilio J. Gallego Arias, Inria, Paris
 */

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

// Takes a textArea and will create an empty div to attach an editor
// to.
export function editorAppend(eId) {

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
    return { container, area };
}

// Local Variables:
// js-indent-level: 4
// End:
