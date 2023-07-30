import { ICoqEditor, ICoqEditorConstructor } from "./coq-editor";
import React from 'react';
import MarkdownPreview from '@uiw/react-markdown-preview';
import { Diagnostic } from "../../../backend";
import { Root, createRoot } from 'react-dom/client';
import { CoqDocument } from "./coq-manager";
import rehypeKatex from 'rehype-katex';
import remarkMath from 'remark-math';
import 'katex/dist/katex.css';
import { CoqCodeMirror5 } from "./coq-editor-cm5";

export class CoqMdViewEditor implements ICoqEditor {
    root : Root;
    editor : CoqCodeMirror5;

    constructor(doc : CoqDocument, options)  {
        this.root = createRoot(doc.container);
        this.root.render(<MarkdownPreview source={doc.area.value}
            remarkPlugins={[remarkMath]}
            rehypePlugins={[rehypeKatex]} />);

        // Replace this by emitting our own textarea (hidden?)
        let ids = doc.container.querySelectorAll('.copied');
        this.editor = new CoqCodeMirror5(doc, options)
    }

    destroy(): void {
        this.root.unmount();
        this.editor.destroy();
    }
    getValue(): string {
        return "";
    }
    getCursorOffset(): number {
        return 0;
    }
    clearDiagnostics(): void {
        
    }
    markDiagnostic(diag: Diagnostic): void {
        
    }
    configure(opts: any): void {
        
    }
    openFile(file: File): void {
        
    }
    focus(): void {
        
    }
}