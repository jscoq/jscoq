import $ from 'jquery'
import type { Editor } from 'codemirror';
import { DocumentClient, SyncPad } from './p2p-chunk';
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
        this.client = undefined; // loaded lazily
        this.ui = new CollabP2PUI(this);
    }

    withCoqManager(coq: any) {
        this.provider = coq.provider.snippets[0];
        return this;
    }

    /**
     * Load libraries and create client.
     */
    async init() {
        if (!this.client) {
            let { DocumentClient } = await import(/* webpackChunkName: "p2p" */ './p2p-chunk');
            this.client = new DocumentClient();
            this.ui.loaded();
        }
    }

    join() {
        return this.client.join(this.uri.channel);
    }

    async setup(opts?: any) {
        await this.init();
        await this.join();
        let { SyncPad } = await import('./p2p-chunk');
        this.syncpad = new SyncPad(this.provider.editor,
            this.client.sync.path(this.uri.docId, 'syncpad'), opts);
    }

    get localFilename() {
        return `p2p:${this.stringifyUri(this.uri)}`;
    }

    async save() {
        this.ui.show();
        this.uri = {channel: 'jscoq/demo-1', docId: 'root'};
        let text = this.provider.getText();
        await this.setup({pin: true});
        this.syncpad.new(text);
        this.provider.filename = this.localFilename;
        this.ui.enterDocument(this.stringifyUri(this.uri));
    }

    async open(channel: string, docId?: string) {
        this.ui.show();
        this.ui.waitingStart();
        this.uri = docId ? {channel, docId} : this.parseUri(channel);
        await this.provider.openLocal(this.localFilename);
        await this.setup();
        this.syncpad.ready.then(() => this.ui.waitingEnd());
        this.ui.update();
    }

    parseUri(spec: string) {
        let mo = spec.match(/^(.*?)⋮(.*)$/);
        return mo ? {channel: mo[1], docId: mo[2]}
                  : {channel: spec, docId: 'root'};
    }

    stringifyUri(uri: {channel: string, docId: string}) {
        return uri.docId === 'root' ? uri.channel
                    : `${uri.channel}⋮${uri.docId}`;
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
            _.button = h('button').on('click', () => this.buttonAction()),
            _.status = h('span'),
            _.peers = h('ul.list-of-peers'));

        this.$refs = _;
        this.update();
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

    loaded() {
        this.p2p.client.activeChannels.observe(() => this.update());
        this.p2p.client.on('peer:ready', () => this.update());
        this.p2p.client.on('peer:leave', () => this.update());
        this.update();
    }

    enterDocument(key: string) {
        window.history.pushState(null, document.title, this.mkURL(key));
    }

    get status() {
        if (!this.p2p.client) return 'loading';
        return this.p2p.client.activeChannels.size > 0 ? 'connected' : 'disconnected';
    }

    get peers(): string[] {
        if (!this.p2p.client) return [];
        return this.p2p.client.getPeers().map(p => p.id);
    }

    update() {
        let _ = this.$refs;
        _.button.text(this.status === 'disconnected' ? 'Join' : 'Leave');
        _.status.text(this.status);
        _.peers.empty().append(this.peers.map(pid => h('li').text(pid)));
    }

    buttonAction() {
        if (this.status === 'disconnected') this.p2p.join();
        else this.p2p.client.close();
    }

    newDoc() {
        this.p2p.syncpad.new();
    }

    mkURL(key: string) {
        var u = new URL(window.location.href),
            q = new URLSearchParams(u.search);
        q.set('p2p', key);
        u.search = q.toString().replace(/=($|&)/g, '');
        return u;
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