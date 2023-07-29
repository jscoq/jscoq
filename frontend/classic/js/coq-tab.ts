import { CoqDocument } from "./coq-document";
import { createEditorContainer, ICoqEditor, ICoqEditorConstructor } from "./coq-editor";
import { CoqManager } from "./coq-manager";

export class CoqTab {
    tab: HTMLButtonElement;
    editor: ICoqEditor;
    container: HTMLDivElement;
    private connected: boolean = false;

    constructor(doc: CoqDocument,
                CoqEditor: ICoqEditorConstructor,
                onChange: (doc: CoqDocument) => void,
                onCursorUpdated: (offset: number) => void,
                manager: CoqManager,
                parent: HTMLElement) {
        this.container = createEditorContainer();
        this.editor = new CoqEditor(doc, manager, this.container, onChange, onCursorUpdated);
        // create tab button
        if (!manager.options.multiple_editors) {
            this.tab = null;
        } else {
            let tab = this.createTabButton(doc, manager);
            this.tab = tab;
            parent.appendChild(tab);
        }
    }

    private createTabButton(doc: CoqDocument, manager: CoqManager) {
        let tab = document.createElement('button');
        tab.classList.add('tab');
        tab.innerText = doc.getFilename();
        let tab_manager = manager.tab_manager;
        tab.addEventListener('click', (ev: MouseEvent) => {
            if (ev.target !== tab)
                return;
            if (this !== tab_manager.current_tab) {
                tab_manager.setCurrent(this);
            }
        });
        // to close tab
        let onClickClose = (ev: MouseEvent) => {
            tab_manager.closeTab(this);
            if (this === tab_manager.current_tab) {
                tab_manager.setCurrent((tab_manager.tabs.length > 0) ? tab_manager.tabs[0] : null);
            }
        };
        let s = this.createCloseButton(onClickClose);
        tab.appendChild(s);
        return tab;
    }

    private createCloseButton(onClickClose: (ev: MouseEvent) => void) {
        let s = document.createElement('span');
        s.classList.add('closable-button');
        s.textContent = '×';
        s.addEventListener('click', onClickClose);
        return s;
    }

    connectWorker() {
        if (this.connected) return;
        this.connected = true;
        this.editor.connectWorker();
    }

    addSelectedStyle() {
        if (this.tab)
            this.tab.classList.add('selected');
    }

    removeSelectedStyle() {
        if (this.tab)
            this.tab.classList.remove('selected');
    }

    show() {
        this.container.style.display = '';
    }

    hide() {
        this.container.style.display = 'none';
    }

    close() {
        this.container.remove();
        this.tab.remove();
        this.editor.destroy();
    }
}