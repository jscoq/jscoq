//@ts-check
"use strict"

import 'codemirror/addon/edit/matchbrackets.js';
import 'codemirror/keymap/emacs.js';
import 'codemirror/addon/selection/mark-selection.js';
import 'codemirror/addon/edit/matchbrackets.js';
import 'codemirror/addon/hint/show-hint.js';
import 'codemirror/addon/dialog/dialog.js';

export { default as CodeMirror } from 'codemirror';

export { default as $ } from 'jquery';
export { default as JSZip } from 'jszip';
export { default as localforage } from 'localforage';

// External module (which is not an NPM package)
import '../ui-external/CodeMirror-TeX-input/addon/hint/tex-input-hint.js';