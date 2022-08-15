/* jsCoq
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2022 Shachar Itzhaky, Technion - Israel Institute of Technology, Haifa
 * Copyright (C) 2019-2022 Emilio J. Gallego Arias, Inria, Paris
 */

import { Diagnostic } from "../../../backend"

export interface ICoqEditor {
    getValue() : string
    onChange(newContent : string) : void
    clearMarks() : void
    markDiagnostic(diag : Diagnostic) : void
    configure(opts: any) : void
    openFile(file: File) : void
    focus() : void
}

// Local Variables:
// js-indent-level: 4
// End:
