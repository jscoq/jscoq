"use strict";


class CoqWorker {
    constructor(scriptPath) {
        this.options = {
            debug: false
        };
        this.observers = [this];
        this.routes = [this.observers];
        this.sids = [, new Future()];

        // Create actual worker. Ideally, CoqWorker would extend Worker, but this is
        // not supported at the moment.
        this.worker = new Worker(scriptPath || (CoqWorker.scriptDir + "jscoq_worker.js"))
        this.worker.onmessage = evt => this.coq_handler(evt);

        window.addEventListener('unload', () => this.worker.terminate());
    }

    sendCommand(msg) {
        if(this.options.debug) {
            console.log("Posting: ", msg);
        }
        this.worker.postMessage(msg);
    }

    init(implicit, lib_init, lib_path) {
        this.sendCommand(["Init", implicit, lib_init, lib_path]);
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

    loadPkg(base_path, pkg) {
        this.sendCommand(["LoadPkg", base_path, pkg]);
    }

    infoPkg(base_path, pkgs) {
        this.sendCommand(["InfoPkg", base_path, pkgs]);
    }

    reassureLoadPath(load_path) {
        this.sendCommand(["ReassureLoadPath", load_path]);
    }

    put(filename, content) {
        /* Access ArrayBuffer behind Node.js Buffer */
        if (content.buffer && 
            content.byteOffset === 0 && content.byteLength === content.buffer.byteLength)
            content = content.buffer;

        var msg = ["Put", filename, content];
        if(this.options.debug) {
            console.log("Posting file: ", msg);
        }
        this.worker.postMessage(msg, [content]);
        /* Notice: ownership of the 'content' buffer is transferred to the worker 
         * (for efficiency)
         */
    }

    register(filename) {
        this.sendCommand(["Register", filename]);
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
        let pfr = new PromiseFeedbackRoute();
        rid = this.query(sid, rid, query);

        this.routes[rid] = [pfr];
        pfr.atexit = () => { delete this.routes[rid]; };
        return pfr.promise;
    }

    // Internal event handling

    coq_handler(evt) {

        var msg     = evt.data;
        var msg_tag = msg[0];
        var msg_args = msg.slice(1);
        var handled = false;

        if(this.options.debug) {
            if (msg_tag === 'LibProgress')
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
         
         if (!handled) {
            console.warn('Message ', msg, ' not handled');
        }
    }

    coqFeedback(fb_msg) {

        var feed_tag = fb_msg.contents[0];
        var feed_route = fb_msg.route || 0;
        var feed_args = [fb_msg.span_id].concat(fb_msg.contents.slice(1));
        var handled = false;

        if(this.options.debug)
            console.log('Coq Feedback message', fb_msg.span_id, fb_msg.contents);

        // We call the corresponding method feed$msg_tag(sid, msg[1]..msg[n])
        for (let o of this.routes[feed_route] || []) {
            let handler = o['feed'+feed_tag];
            if (handler) {
                handler.apply(o, feed_args);
                handled = true;
            }
        }

        if (!handled) {
            console.warn(`Feedback type ${feed_tag} not handled (route ${feed_route})`);
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

    isDone()        { return this._done; }
    isSuccessful()  { return this._success; }
    isFailed()      { return this._done && !this._success; }
}


class PromiseFeedbackRoute extends Future {
    constructor() {
        super();
        this.atexit = () => {};
        this._got_message = false;
        this._got_processed = false;
    }

    feedMessage(sid, lvl, loc, msg) {
        this._got_message = true;
        if (this._got_processed) this.atexit();

        if (lvl[0] === 'Error')
            this.reject(msg);
        else
            this.resolve(msg);
    }

    feedProcessed(sid) {
        this._got_processed = true;
        if (this._got_message) this.atexit();
    }
}


if (typeof document !== 'undefined' && document.currentScript)
    CoqWorker.scriptDir = document.currentScript.attributes.src.value.replace(/[^/]*$/, '');

if (typeof module !== 'undefined')
    module.exports = {CoqWorker}
