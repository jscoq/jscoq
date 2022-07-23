import $ from 'jquery'
import type { Editor } from 'codemirror';
import { DocumentClient } from 'ronin-p2p/src/net/client-docs';
import { SyncPad } from 'ronin-p2p/src/addons/syncpad';
import './collab.css';


class CollabP2P {
    client: DocumentClient
    ui: CollabP2PUI
    provider: {editor: Editor, openLocal: (filename: string) => Promise<any>}
    syncpad: SyncPad
    uri: {channel: string, docId: string}

    shown = false

    constructor() {
        this.client = new DocumentClient();
        this.ui = new CollabP2PUI(this);
    }

    withCoqManager(coq: any) {
        this.provider = coq.provider.snippets[0];
        return this;
    }

    async open(channel: string, docId: string) {
        this.ui.show();
        this.ui.waitingStart();
        this.uri = {channel, docId};
        await this.provider.openLocal(`p2p:${channel}⋮${docId}`);
        await this.client.join(channel);
        this.syncpad = new SyncPad(this.provider.editor, this.client.sync.path(docId, 'syncpad'));
        this.syncpad.ready.then(() => this.ui.waitingEnd());
        this.ui.update();
    }

    static attach(coq: any) {
        return new CollabP2P().withCoqManager(coq);
    }
}

/**
 * A minimal, ad-hoc status panel.
 */
class CollabP2PUI {
    p2p: CollabP2P
    $el: JQuery
    $refs: Refs
    shown = false

    dialog: {close: () => void}

    constructor(owner: CollabP2P) {
        this.p2p = owner;
        let _ = this.$refs = new Refs();
        this.$el = h('div.collab-p2p-ui',
            _.button = h('button'), _.status = h('span'),
            _.peers = h('ul.list-of-peers'));

        this.$refs = _;
        this.update();
        this.p2p.client.activeChannels.observe(() => this.update());
        this.p2p.client.on('peer:ready', () => this.update());
        this.p2p.client.on('peer:leave', () => this.update());
    }

    show() {
        if (!this.shown) {
            document.body.append(this.$el[0]);
            this.shown = true;
        }
    }

    get status() {
        return this.p2p.client.activeChannels.size > 0 ? 'connected' : 'disconnected';
    }

    get peers(): string[] {
        return this.p2p.client.getPeers().map(p => p.id);
    }

    update() {
        let _ = this.$refs;
        _.button.text(this.status === 'disconnected' ? 'Join' : 'Leave');
        _.status.text(this.status);
        _.peers.empty().append(this.peers.map(pid => h('li').text(pid)));
    }

    newDoc() {
        this.p2p.syncpad.new();
    }

    openDialog(content: HTMLElement) {
        let opts = {closeOnEnter: false, closeOnBlur: false};
        return (<any>this.p2p.provider.editor).openDialog(content, undefined, opts);
    }

    waitingStart() {
        let dialog = h('span',
            h('span').text("📡 ⋯ Connecting to P2P document... "),
            h('button').text('📄 Create new').on('click', () => this.newDoc()));
        this.dialog = {
            close: this.openDialog(dialog[0])
        };
    }

    waitingEnd() {
        this.dialog?.close();
        this.dialog = undefined;
    }
}

function h(tag: string, ...children: JQuery[]): JQuery {
    let [tagName, ...classNames] = tag.split('.');
    return $(document.createElement(tagName))
                .addClass(classNames).append(children);
}

class Refs {
    [name: string]: JQuery
}


export { CollabP2P }