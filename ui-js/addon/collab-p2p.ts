import type { Editor } from 'codemirror';
import { DocumentClient } from 'ronin-p2p/src/net/client-docs';
import { SyncPad } from 'ronin-p2p/src/addons/syncpad';

Object.assign(window, {DocumentClient, SyncPad});


class CollabP2P {
    client: DocumentClient
    provider: {editor: Editor, openLocal: (filename: string) => Promise<any>}
    syncpad: SyncPad

    constructor() {
        this.client = new DocumentClient();
    }

    withCoqManager(coq: any) {
        this.provider = coq.provider.snippets[0];
        return this;
    }

    async open(channel: string, docId: string) {
        await this.provider.openLocal(`p2p:${channel}/${docId}`);
        await this.client.join(channel);
        this.syncpad = new SyncPad(this.provider.editor, this.client.sync.path(docId, 'syncpad'));
    }

    static attach(coq: any) {
        return new CollabP2P().withCoqManager(coq);
    }
}


export { CollabP2P }