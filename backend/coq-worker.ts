type backend = 'js' | 'wa';

import { Future, PromiseFeedbackRoute } from './future';

/**
 * Main Coq Worker Class
 *
 * @class CoqWorker
 * @property {Worker} worker
 * @property {Function} CoqWorker#defaultScriptPath
 */
export class CoqWorker {
    options: any;
    backend: backend;
    is_npm: boolean;
    observers: any[];
    routes: any[];
    sids: Future<void>[];
    load_progress: (ratio: number, ev: ProgressEvent) => void;
    when_created: Promise<void>;
    _boot : Future<void>;
    _worker_script: string;
    worker: Worker;
    _handler: (msg : any) => void;
    _gen_rid : number;
    intvec: Int32Array;
    base_path : string | URL;

    /**
     * Creates an instance of CoqWorker.
     */
    constructor(base_path : (string | URL), scriptPath : URL, worker, backend : backend, is_npm : boolean) {
        this.options = {
            debug: false,
            warn: true
        };
        this.base_path = base_path;
        this.backend = backend || 'js';
        this.is_npm = is_npm || false;

        this.observers = [this];
        this.routes = [this.observers];
        this.sids = [, new Future()];

        this.load_progress = (ratio, ev) => {};

        if (worker) {
            this.attachWorker(worker);
            this.when_created = Promise.resolve();
        }
        else {
            this.when_created =
                this.createWorker(scriptPath ||
                                  CoqWorker.defaultScriptPath(base_path, backend, is_npm));
        }
    }

    /**
     * Default location for worker script -- computed relative to the URL
     * from which this script is loaded.
     *
     */
    static defaultScriptPath(base_path, backend, is_npm) {
        var nmPath = is_npm ? '..' : 'node_modules';
        return new URL({'js': "backend/jsoo/jscoq_worker.bc.cjs",
                        'wa':`${nmPath}/wacoq-bin/dist/worker.js`}[backend],
                      base_path).href;
    }

    /**
     * Adjusts a given URI so that it can be requested by the worker.
     * (the worker may have a different base path than the page.)
     * @param {string | URL} uri
     */
    resolveUri(uri) {
        return new URL(uri, window.location.href).href;
    }

    /**
     * Creates the worker object
     *
     * @param {string} script_path
     * @return {Promise<Worker>}
     * @async
     * @memberof CoqWorker
     */
    async createWorker(script_path) {
        this._worker_script = script_path;

        this.attachWorker(await
            this.newWorkerWithProgress(this._worker_script));

        if (typeof window !== 'undefined')
            window.addEventListener('unload', () => this.end());

        if (this.backend == 'wa') {
            this._boot = new Future();
            return this._boot.promise;
        }
    }

    /**
     * @param {string} url
     */
    async newWorkerWithProgress(url) {
        await prefetchResource(url, (pc, ev) => this.load_progress(pc, ev));
        // have to use `url` again so that the worker has correct base URI;
        // should be cached at this point though.
        return new Worker(url);
    }

    /**
     * @param {Worker} worker
     */
    attachWorker(worker) {
        this.worker = worker;
        this.worker.addEventListener('message',
            this._handler = (/** @type {any} */ evt) => this.coq_handler(evt));
    }

    /**
     * Sends a Command to Coq worker
     *
     * @param {object[]} msg
     * @memberof CoqWorker
     */
    sendCommand(msg) {
        if(this.options.debug) {
            console.log("Posting: ", msg);
        }
        this.worker.postMessage(this.backend === 'wa' ? JSON.stringify(msg) : msg);
    }

    /**
     * @param {any[]} msg
     */
    sendDirective(msg) {   // directives are intercepted by the JS part of the worker
        this.worker.postMessage(msg);    // for this reason, they are not stringified
    }

    /**
     * Send Init Command to Coq
     *
     * @param {object} coq_opts
     * @param {object} doc_opts
     * @memberof CoqWorker
     */
    init(coq_opts, doc_opts) {
        this.sendCommand(["Init", coq_opts]);
        if (doc_opts)
            this.sendCommand(["NewDoc", doc_opts]);
    }

    getInfo() {
        this.sendCommand(["GetInfo"]);
    }

    /**
     * @param {any} ontop_sid
     * @param {string | number} new_sid
     * @param {any} stm_text
     * @param {boolean} resolve
     */
    add(ontop_sid, new_sid, stm_text, resolve = false) {
        this.sids[new_sid] = new Future();
        this.sendCommand(["Add", ontop_sid, new_sid, stm_text, resolve]);
    }

    /**
     * @param {any} ontop_sid
     * @param {any} new_sid
     * @param {any} stm_text
     */
    resolve(ontop_sid, new_sid, stm_text) {
        this.add(ontop_sid, new_sid, stm_text, true);
    }

    /**
     * @param {any} sid
     */
    exec(sid) {
        this.sendCommand(["Exec", sid]);
    }

    /**
     * @param {number} sid
     */
    cancel(sid) {
        for (let i in this.sids)
            if (+i >= sid && this.sids[i]) { this.sids[i]?.reject(); delete this.sids[i]; }
        this.sendCommand(["Cancel", sid]);
    }

    /**
     * @param {any} sid
     */
    goals(sid) {
        this.sendCommand(["Query", sid, 0, ["Goals"]]);
    }

    /**
     * @param {number} sid
     * @param {any} rid
     * @param {any[]} query
     */
    query(sid, rid, query) {
        if (typeof query == 'undefined') { query = rid; rid = undefined; }
        if (typeof rid == 'undefined')
            rid = this._gen_rid = (this._gen_rid || 0) + 1;
        this.sendCommand(["Query", sid, rid, query]);
        return rid;
    }

    /**
     * @param {any} sid
     * @param {undefined} rid
     * @param {any} search_query
     */
    inspect(sid, rid, search_query) {
        if (typeof search_query == 'undefined') { search_query = rid; rid = undefined; }
        return this.query(sid, rid, ['Inspect', search_query])
    }

    /**
     * @param {string | string[]} option_name
     */
    getOpt(option_name) {
        if (typeof option_name === 'string')
            option_name = option_name.split(/\s+/);
        this.sendCommand(["GetOpt", option_name]);
    }

    /**
     * @param {{base_path: string, pkg: string} | string} url
     */
    loadPkg(url) {
        switch (this.backend) {
        case 'js':
            if (typeof url !== 'object') throw new Error('invalid URL for js mode (object expected)');
            this.sendCommand(["LoadPkg", this.resolveUri(url.base_path), url.pkg]);
            break;
        case 'wa':
            if (url instanceof URL) url = url.href;
            this.sendDirective(["LoadPkg", url]); break;
        }
    }

    /**
     * @param {any} base_path
     * @param {any} pkgs
     */
    infoPkg(base_path, pkgs) {
        this.sendCommand(["InfoPkg", this.resolveUri(base_path), pkgs]);
    }

    /**
     * @param {any} load_path
     */
    refreshLoadPath(load_path) {
        switch (this.backend) {
        case 'js': this.sendCommand(["ReassureLoadPath", load_path]); break;
        case 'wa': this.sendCommand(["RefreshLoadPath"]); break;
        }
    }

    /**
     * @param {string} filename
     * @param {Buffer} content
     */
    put(filename, content, transferOwnership=false) {
        /* Access ArrayBuffer behind Node.js Buffer */
        var abuf = /** @type {Buffer | ArrayBufferLike} */ (content);
        if (typeof Buffer !== 'undefined' && content instanceof Buffer) {
            abuf = this.arrayBufferOfBuffer(content);
            content = new Buffer(abuf);
        }

        var msg = ["Put", filename, content];
        if(this.options.debug) {
            console.debug("Posting file: ", msg);
        }
        this.worker.postMessage(msg, transferOwnership ? [abuf] : []);
        /* Notice: when transferOwnership is true, the 'content' buffer is
         * transferred to the worker (for efficiency);
         * it becomes unusable in the original context.
         */
    }

    /**
     * @param {Buffer} buffer
     */
    arrayBufferOfBuffer(buffer) {
        return (buffer.byteOffset === 0 &&
                buffer.byteLength === buffer.buffer.byteLength) ?
            buffer.buffer :
            buffer.buffer.slice(buffer.byteOffset,
                                buffer.byteOffset + buffer.byteLength);
    }

    /**
     * @param {any} filename
     */
    register(filename) {
        this.sendCommand(["Register", filename]);
    }

    interruptSetup() {
        if (typeof SharedArrayBuffer !== 'undefined') {
            this.intvec = new Int32Array(new SharedArrayBuffer(4));
            try {
                this.sendDirective(["InterruptSetup", this.intvec]);
            }
            catch (e) {  /* this fails in Firefox 72 even with SharedArrayBuffer enabled */
                console.warn('SharedArrayBuffer is available but not serializable -- interrupts disabled');
            }
        }
        else {
            console.warn('SharedArrayBuffer is not available -- interrupts disabled');
        }
    }

    interrupt() {
        if (this.intvec)
            Atomics.add(this.intvec, 0, 1);
        else
            console.warn("interrupt requested but has not been set up");
    }

    async restart() {
        this.sids = [, new Future()];

        this.end();  // kill!

        await this.createWorker(this._worker_script);
    }

    end() {
        if (this.worker) {
            this.worker.removeEventListener('message', this._handler);
            this.worker.terminate();
            this.worker = undefined;
        }
    }

    // Promise-based APIs

    /**
     * @param {string | number} sid
     */
    execPromise(sid) {
        this.exec(sid);

        if (!this.sids[sid]) {
            console.warn(`exec'd sid=${sid} that was not added (or was cancelled)`);
            this.sids[sid] = new Future();
        }
        return this.sids[sid].promise;
    }

    /**
     * @param {any} sid
     * @param {any} rid
     * @param {any} query
     */
    queryPromise(sid, rid, query) {
        return this._wrapWithPromise(
            rid = this.query(sid, rid, query));
    }

    /**
     * @param {any} sid
     * @param {any} rid
     * @param {any} search_query
     */
    inspectPromise(sid, rid, search_query) {
        return this._wrapWithPromise(
            this.inspect(sid, rid, search_query));
    }

    /**
     * @param {string | number} rid
     */
    _wrapWithPromise(rid) {
        let pfr = new PromiseFeedbackRoute();
        this.routes[rid] = [pfr];
        pfr.atexit = () => { delete this.routes[rid]; };
        return pfr.promise;
    }

    spawn(base_path) {
        this.worker.removeEventListener('message', this._handler);
        return new CoqWorker(base_path, null, this.worker, this.backend, this.is_npm);
    }

    /**
     * @param {{ _handler: any; }} child
     */
    join(child) {
        this.worker.removeEventListener('message', child._handler);
        this.worker.addEventListener('message', this._handler);
    }

    // Internal event handling

    /**
     * @param {{ data: any; }} evt
     */
    coq_handler(evt) {

        var msg     = evt.data;
        var msg_tag = msg[0];
        var msg_args = msg.slice(1);
        var handled = false;

        if(this.options.debug) {
            if (msg_tag === 'LibProgress' || msg_tag === 'Log' && msg_args[0][0] === 'Debug')
                console.debug("Coq message", msg); // too much spam :\
            else
                console.log("Coq message", msg);
        }

        // We call the corresponding method coq$msg_tag(msg[1]..msg[n])
        for (let o of this.observers) {
            let handler = o['coq'+msg_tag];
            if (handler) {
                handler.apply(o, msg_args);
                handled = true;
            }
         }

         if (!handled && this.options.warn) {
            console.warn('Message ', msg, ' not handled');
        }
    }

    coqBoot() {
        if (this._boot)
            this._boot.resolve(null);
    }

    /**
     * @param {{ contents: string | any[]; route: number; span_id: any; }} fb_msg
     * @param {any} in_mode
     */
    coqFeedback(fb_msg, in_mode) {

        var feed_tag = fb_msg.contents[0];
        var feed_route = fb_msg.route || 0;
        var feed_args = [fb_msg.span_id, ...fb_msg.contents.slice(1), in_mode];
        var handled = false;

        if(this.options.debug)
            console.log('Coq Feedback message', fb_msg.span_id, fb_msg.contents);

        // We call the corresponding method feed$feed_tag(sid, msg[1]..msg[n])
        for (let o of this.routes[feed_route] || []) {
            let handler = o['feed'+feed_tag];
            if (handler) {
                handler.apply(o, feed_args);
                handled = true;
            }
        }

        if (!handled && this.options.warn) {
            console.warn(`Feedback type ${feed_tag} not handled (route ${feed_route})`);
        }
    }

    /**
     * @param {string | number} rid
     * @param {any} bunch
     */
    coqSearchResults(rid, bunch) {

        var handled = false;

        for (let o of this.routes[rid] || []) {
            var handler = o['feedSearchResults'];
            if (handler) {
                handler.call(o, bunch);
                handled = true;
            }
        }

        if (!handled && this.options.warn) {
            console.warn(`SearchResults not handled (route ${rid})`);
        }
    }

    /**
     * @param {string | number} sid
     */
    feedProcessed(sid) {
        var fut = this.sids[sid];
        if (fut) { fut.resolve(null); }
    }
}

/**
 * This class is meant to support running the worker as a native subprocess,
 * available in waCoq through the `subproc` module.
 */
export class CoqSubprocessAdapter extends CoqWorker {
    constructor(base_path, backend, is_npm) {
        /* Emilio: the require here fails, this is a fixme!
        const subproc = require('wacoq-bin/dist/subproc'),
              icoq = new subproc.IcoqSubprocess();
        super(base_path, null, icoq, backend, is_npm);
        window.addEventListener('beforeunload', () => icoq.end());
        */
       super(base_path, null, null, backend, is_npm);
    }

    coq_handler(evt) {
        setTimeout(() => super.coq_handler(evt), 0); // force window context
    }
}

// some boilerplate from https://stackoverflow.com/questions/51734372/how-to-prefetch-video-in-a-react-application
function prefetchResource(url, progress = (pc :number,ev:ProgressEvent)=>{}) {
    var xhr = new XMLHttpRequest();
    xhr.open("GET", url, true);
    xhr.responseType = "blob";

    return new Promise((resolve, reject) => {
        xhr.addEventListener("load", () =>
            (xhr.status === 200) ? resolve(xhr.response)
               : reject(new Error(`status ${xhr.status}`)));

        xhr.addEventListener("progress", (event) => {
            if (event.lengthComputable)
                progress(event.loaded / event.total, event);
            else
                progress(undefined, event);
        });
        xhr.send();
    });
}

// Local Variables:
// js-indent-level: 4
// End:
