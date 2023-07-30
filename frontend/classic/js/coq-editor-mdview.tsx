import { ICoqEditor, ICoqEditorConstructor } from "./coq-editor";
import React from 'react';
import MarkdownPreview from '@uiw/react-markdown-preview';
import { Diagnostic } from "../../../backend";
import { Root, createRoot } from 'react-dom/client';
import { CoqDocument } from "./coq-manager";
import rehypeKatex from 'rehype-katex';
import remarkMath from 'remark-math';
import 'katex/dist/katex.css';

export class CoqMdViewEditor implements ICoqEditor {
    root : Root;

    constructor(doc : CoqDocument, options)  {
        this.root = createRoot(doc.container);
        this.root.render(<MarkdownPreview source={doc.area.value}
            remarkPlugins={[remarkMath]}
            rehypePlugins={[rehypeKatex]} />);
    }
    destroy(): void {
        this.root.unmount();
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