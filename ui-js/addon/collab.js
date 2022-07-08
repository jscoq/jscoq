import './public-path';
import { haste, HasteUI } from '@corwin.amber/hastebin/client';
import '@corwin.amber/hastebin/client/application.css';
export { CollabP2P } from './collab-p2p';

/**
 * Hastebin collaboration client
 */
class Hastebin {
    constructor() {
        this.haste = new haste('jsCoq', {baseURL: 'https://hbin.herokuapp.com'});
        this.haste.ui = new HasteUIAdapter(this.haste.config);
        this.haste.embed();
        this.haste.newDocument();
    }

    withCoqManager(coq) {
        this.editor = coq.provider.snippets[0];
        this.haste.view = {
            get: () => this.editor.editor.getValue(),
            set: (text, mode) => {
                this.editor.load(text, 'from hastebin');
                if (mode === 'r')
                    this._onceChange(this.editor.editor, () => this.haste.unlockDocument());
            }
        };
        return this;
    }

    load(key) {
        this.haste.loadDocument(key);
    }

    save() {
        return new Promise(resolve => this.haste.lockDocument(resolve));
    }

    _onceChange(cm, op) {
        var h;
        cm.on('change', h = () => { cm.off('change', h); op(); });
    }

    static attach(coq, key) {
        var collab = new Hastebin().withCoqManager(coq);
        if (key)
            collab.load(key.replace(/^hb-/, ''));
        return collab;
    }
}

/**
 * Hastebin toolbar customized for use "over" the jsCoq UI.
 */
class HasteUIAdapter extends HasteUI {
    mkURL(key) {
        var u = new URL(window.location),
            q = new URLSearchParams(u.search);
        q.set('share', key ? `hb-${key}` : '');
        u.search = q.toString().replace(/=($|&)/g, '');
        return u;
    }
}


export { haste, Hastebin }