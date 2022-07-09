import $ from 'jquery'
import type { Editor } from 'codemirror';
import { DocumentClient } from 'ronin-p2p/src/net/client-docs';
import { SyncPad } from 'ronin-p2p/src/addons/syncpad';
import './collab.css';


class CollabP2P {
    client: DocumentClient
    ui: CollabP2PUI
    provider: {
        editor: Editor, filename: string,
        getText: () => string,
        openLocal: (filename: string) => Promise<any>
    }
    syncpad: SyncPad
    uri: {channel: string, docId: string}

    constructor() {
        this.client = new DocumentClient();
        this.ui = new CollabP2PUI(this);
    }

    withCoqManager(coq: any) {
        this.provider = coq.provider.snippets[0];
        return this;
    }

    async join() {
        await this.client.join(this.uri.channel);
        this.syncpad = new SyncPad(this.provider.editor,
            this.client.sync.path(this.uri.docId, 'syncpad'));
    }

    get localFilename() {
        return `p2p:${this.uri.channel}⋮${this.uri.docId}`;
    }

    async save() {
        this.ui.show();
        this.uri = {channel: 'jscoq/demo-1', docId: 'root'};
        let text = this.provider.getText();
        await this.join();
        this.syncpad.new(text);
        this.provider.filename = this.localFilename;
        console.log(this.uri, this.localFilename);
    }

    async open(channel: string, docId?: string) {
        this.ui.show();
        this.ui.waitingStart();
        this.uri = docId ? {channel, docId} : this.parseUri(channel);
        await this.provider.openLocal(this.localFilename);
        await this.join();
        this.syncpad.ready.then(() => this.ui.waitingEnd());
        this.ui.update();
    }

    parseUri(spec: string) {
        let mo = spec.match(/^(.*?)⋮(.*)$/);
        return mo ? {channel: mo[1], docId: mo[2]}
                  : {channel: spec, docId: 'root'};
    }

    close() {
        this.uri = undefined;
        this.syncpad?.destroy();
        this.ui.hide();
    }

    static attach(coq: any, openUri?: string) {
        let p2p = new CollabP2P().withCoqManager(coq);
        if (openUri) p2p.open(openUri);
        return p2p;
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

    hide() {
        this.$el.remove();
        this.shown = false;
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