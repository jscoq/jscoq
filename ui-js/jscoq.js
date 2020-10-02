"use strict";

class CoqWorker {

    constructor(scriptPath, worker) {
        this.options = {
            debug: false,
            warn: true
        };
        this.observers = [this];
        this.routes = [this.observers];
        this.sids = [, new Future()];

        if (worker) {
            this.worker = worker;
            this.when_created = Promise.resolve();
        }
        else {
            this.when_created = 
                this.createWorker(scriptPath ||
                                  this.constructor.defaultScriptPath());
        }

        this.worker.addEventListener('message', 
            this._handler = evt => this.coq_handler(evt));
    }

    /**
     * Default location for worker script -- computed relative to the URL
     * from which this script is loaded.
     */
    static defaultScriptPath() {
        var nmPath = JsCoq.is_npm ? '../..' : '../node_modules';
        return new URL(`${nmPath}/wacoq-bin/dist/worker.js`, this.scriptUrl).href;
    }

    /**
     * Adjusts a given URI so that it can be requested by the worker.
     * (the worker may have a different base path than the page.)
     */
    resolveUri(uri) {
        return new URL(uri, window.location).href;
    }

    createWorker(script_path) {
        this._worker_script = script_path;

        this.worker = new Worker(this._worker_script);

        if (typeof window !== 'undefined')
            window.addEventListener('unload', () =>
                this.worker && this.worker.terminate());

        this._boot = new Future();
        return this._boot.promise;
    }

    sendCommand(msg) {
        if(this.options.debug) {
            console.log("Posting: ", msg);
        }
        this.worker.postMessage(JSON.stringify(msg));
    }

    sendDirective(msg) {   // directives are intercepted by the JS part of the worker
        this.worker.postMessage(msg);    // for this reason, they are not stringified
    }

    init(coq_opts, doc_opts) {
        this.sendCommand(["Init", coq_opts]);
        if (doc_opts)
            this.sendCommand(["NewDoc", doc_opts]);
    }

    getInfo() {
        this.sendCommand(["GetInfo"]);
    }

    add(ontop_sid, new_sid, stm_text, resolve) {
        this.sids[new_sid] = new Future();
        this.sendCommand(["Add", ontop_sid, new_sid, stm_text, resolve || false]);
    }

    resolve(ontop_sid, new_sid, stm_text) {
        this.add(ontop_sid, new_sid, stm_text, true);
    }

    exec(sid) {
        this.sendCommand(["Exec", sid]);
    }

    cancel(sid) {
        for (let i in this.sids)
            if (i >= sid && this.sids[i]) { this.sids[i].reject(); delete this.sids[i]; }
        this.sendCommand(["Cancel", sid]);
    }

    goals(sid) {
        this.sendCommand(["Goals", sid]);
    }

    query(sid, rid, query) {
        if (typeof query == 'undefined') { query = rid; rid = undefined; }
        if (typeof rid == 'undefined')
            rid = this._gen_rid = (this._gen_rid || 0) + 1;
        this.sendCommand(["Query", sid, rid, query]);
        return rid;
    }

    inspect(sid, rid, search_query) {
        if (typeof search_query == 'undefined') { search_query = rid; rid = undefined; }
        if (typeof rid == 'undefined')
            rid = this._gen_rid = (this._gen_rid || 0) + 1;
        this.sendCommand(["Inspect", sid, rid, search_query]);
        return rid;
    }

    getOpt(option_name) {
        if (typeof option_name === 'string')
            option_name = option_name.split(/\s+/);
        this.sendCommand(["GetOpt", option_name]);
    }

    loadPkg(url) {
        if (url instanceof URL) url = url.href;
        this.sendDirective(["LoadPkg", url]);
    }

    infoPkg(base_path, pkgs) {
        this.sendCommand(["InfoPkg", this.resolveUri(base_path), pkgs]);
    }

    refreshLoadPath(load_path) {
        this.sendCommand(["RefreshLoadPath"]);
    }

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

    arrayBufferOfBuffer(buffer) {
        return (buffer.byteOffset === 0 && 
                buffer.byteLength === buffer.buffer.byteLength) ?
            buffer.buffer :
            buffer.buffer.slice(buffer.byteOffset, 
                                buffer.byteOffset + buffer.byteLength);
    }

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

        this.worker.removeEventListener('message', this._handler);
        this.worker.terminate();  // kill!

        // Recreate worker
        this.createWorker(this._worker_script);
    }

    end() {
        this.worker.terminate();
    }

    // Promise-based APIs

    execPromise(sid) {
        this.exec(sid);

        if (!this.sids[sid]) {
            console.warn(`exec'd sid=${sid} that was not added (or was cancelled)`);
            this.sids[sid] = new Future();
        }
        return this.sids[sid].promise;
    }

    queryPromise(sid, rid, query) {
        return this._wrapWithPromise(
            rid = this.query(sid, rid, query));
    }

    inspectPromise(sid, rid, search_query) {
        return this._wrapWithPromise(
            this.inspect(sid, rid, search_query));
    }

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

    join(child) {
        this.worker.removeEventListener('message', child._handler);
        this.worker.addEventListener('message', this._handler);
    }

    // Internal event handling

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

    feedProcessed(sid) {
        var fut = this.sids[sid];
        if (fut) { fut.resolve(); }
    }
}


class Future {
    constructor() {
        this.promise = new Promise((resolve, reject) => {
            this._resolve = resolve;
            this._reject = reject;
        });
        this._done = false;
        this._success = false;
    }

    resolve(val) { if (!this._done) { this._done = this._success = true; this._resolve(val); } }
    reject(err) { if (!this._done) { this._done = true; this._reject(err); } }

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

    feedMessage(sid, lvl, loc, msg) {
        this.messages.push({sid: sid, lvl: lvl[0], loc: loc, msg: msg});
    }

    feedComplete(sid) {
        this.resolve(this.messages);
        this._done = true;
        if (this._got_processed) this.atexit();
    }

    feedIncomplete(sid) {
        this.reject(this.messages);
        this._done = true;
        if (this._got_processed) this.atexit();
    }

    feedProcessed(sid) {
        this._got_processed = true;
        if (this._done) this.atexit();
    }

    feedSearchResults(bunch) {
        this.resolve(bunch);
        this.atexit();
    }
}


class CoqSubprocessAdapter extends CoqWorker {
    constructor() {
        const subproc = require('wacoq-bin/dist/subproc');
        super(null, new subproc.IcoqSubprocess());
        window.addEventListener('beforeunload', () => this.worker.end());
    }
    coq_handler(...a) {
        setTimeout(() => super.coq_handler(...a), 0); // force window context
    }
}


if (typeof document !== 'undefined' && document.currentScript)
    CoqWorker.scriptUrl = new URL(document.currentScript.attributes.src.value, window.location);

if (typeof module !== 'undefined')
    module.exports = {CoqWorker, CoqSubprocessAdapter, Future, PromiseFeedbackRoute}

// Local Variables:
// js-indent-level: 4
// End:
