//@ts-check
"use strict";

import { JsCoq } from './index.js';

/**
 * Main Coq Worker Class
 *
 * @class CoqWorker
 * @property {Function} CoqWorker#defaultScriptPath
 */
export class CoqWorker {

    /**
     * Creates an instance of CoqWorker.
     * @param {string} scriptPath
     * @param {Worker} worker
     * @memberof CoqWorker
     * @constructor
     */
    constructor(scriptPath, worker) {
        this.options = {
            debug: false,
            warn: true
        };
        this.observers = [this];
        this.routes = [this.observers];
        this.sids = [, new Future()];

        this.load_progress = (pc) => {};

        if (worker) {
            this.attachWorker(worker);
            this.when_created = Promise.resolve();
        }
        else {
            this.when_created = 
                this.createWorker(scriptPath ||
                                  this.constructor.defaultScriptPath());
        }
    }

    /**
     * Default location for worker script -- computed relative to the URL
     * from which this script is loaded.
     * 
     */
    static defaultScriptPath() {
        var nmPath = JsCoq.is_npm ? '../..' : '../node_modules';
        return new URL({'js': "../coq-js/jscoq_worker.bc.cjs",
                        'wa':`${nmPath}/wacoq-bin/dist/worker.js`}[JsCoq.backend],
                       this.scriptUrl).href;
    }

    /**
     * Adjusts a given URI so that it can be requested by the worker.
     * (the worker may have a different base path than the page.)
     * @param {string | URL} uri
     */
    resolveUri(uri) {
        return new URL(uri, window.location).href;
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
            this.newWorkerWithProgress(this._worker_script)); // this._worker_script));

        if (typeof window !== 'undefined')
            window.addEventListener('unload', () => this.end());

        if (JsCoq.backend == 'wa') {
            this._boot = new Future();
            return this._boot.promise;
        }
    }

    /**
     * @param {string} url
     */
    async newWorkerWithProgress(url) {
        await prefetchResource(url, pc => this.load_progress(pc));
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
        if (JsCoq.backend === 'wa') msg = JSON.stringify(msg);
        this.worker.postMessage(msg);
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
     * @param {string} coq_opts
     * @param {string} doc_opts
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
    add(ontop_sid, new_sid, stm_text, resolve) {
        this.sids[new_sid] = new Future();
        this.sendCommand(["Add", ontop_sid, new_sid, stm_text, resolve || false]);
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
            if (i >= sid && this.sids[i]) { this.sids[i].reject(); delete this.sids[i]; }
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
     * @param {{ base_path: string, pkg: string}} url
     */
    loadPkg(url) {
        switch (JsCoq.backend) {
        case 'js':
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
        switch (JsCoq.backend) {
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
        var abuf = content;
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

    restart() {
        this.sids = [, new Future()];

        this.end();  // kill!

        this.createWorker(this._worker_script);
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

    spawn() {
        this.worker.removeEventListener('message', this._handler);
        return new CoqWorker(null, this.worker);
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
            this._boot.resolve();
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
        if (fut) { fut.resolve(); }
    }
}


export class Future {
    constructor() {
        this.promise = new Promise((resolve, reject) => {
            this._resolve = resolve;
            this._reject = reject;
        });
        this._done = false;
        this._success = false;
    }

    /**
     * @param {any[] | undefined} [val]
     */
    resolve(val) { if (!this._done) { this._done = this._success = true; this._resolve(val); } }
    /**
     * @param {any[] | undefined} [err]
     */
    reject(err) { if (!this._done) { this._done = true; this._reject(err); } }

    /**
     * @param {((value: any) => any) | null | undefined} cont
     */
    then(cont)      { return this.promise.then(cont); }

    isDone()        { return this._done; }
    isSuccessful()  { return this._success; }
    isFailed()      { return this._done && !this._success; }
}


class PromiseFeedbackRoute extends Future {
    constructor() {
        super();
        this.atexit = () => {};
        this.messages = [];
        this._got_processed = false;
        this._done = false;
    }

    /**
     * @param {any} sid
     * @param {any[]} lvl
     * @param {any} loc
     * @param {any} msg
     */
    feedMessage(sid, lvl, loc, msg) {
        this.messages.push({sid: sid, lvl: lvl[0], loc: loc, msg: msg});
    }

    /**
     * @param {any} sid
     */
    feedComplete(sid) {
        this.resolve(this.messages);
        this._done = true;
        if (this._got_processed) this.atexit();
    }

    /**
     * @param {any} sid
     */
    feedIncomplete(sid) {
        this.reject(this.messages);
        this._done = true;
        if (this._got_processed) this.atexit();
    }

    /**
     * @param {any} sid
     */
    feedProcessed(sid) {
        this._got_processed = true;
        if (this._done) this.atexit();
    }

    /**
     * @param {any} bunch
     */
    feedSearchResults(bunch) {
        this.resolve(bunch);
        this.atexit();
    }
}

export class CoqSubprocessAdapter extends CoqWorker {
    constructor() {
        const subproc = require('wacoq-bin/dist/subproc');
        super(null, new subproc.IcoqSubprocess());
        window.addEventListener('beforeunload', () => this.worker.end());
    }
    /**
     * @param {any[]} a
     */
    coq_handler(...a) {
        setTimeout(() => super.coq_handler(...a), 0); // force window context
    }
}

// some boilerplate from https://stackoverflow.com/questions/51734372/how-to-prefetch-video-in-a-react-application
/**
 * @param {string | URL} url
 */
function prefetchResource(url, progress=()=>{}) {
    var xhr = new XMLHttpRequest();
    xhr.open("GET", url, true);
    xhr.responseType = "blob";

    return new Promise((resolve, reject) => {
        xhr.addEventListener("load", () =>
            (xhr.status === 200) ? resolve(xhr.response)
               : reject(new Error(`status ${xhr.status}`)));

        xhr.addEventListener("progress", (event) => {
            if (event.lengthComputable)
                progress(event.loaded / event.total);
        });
        xhr.send();
    });
}

CoqWorker.scriptUrl = new URL(import.meta.url);

// Local Variables:
// js-indent-level: 4
// End:
