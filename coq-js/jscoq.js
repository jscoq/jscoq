"use strict";


class CoqWorker {
    constructor(scriptPath) {
        this.options = {
            debug: false
        };
        this.observers = [this];
        this.routes = [this.observers];
        this.sids = [];

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
        this.sendCommand(["Add", ontop_sid, new_sid, stm_text, resolve || false]);
    }

    resolve(ontop_sid, new_sid, stm_text) {
        this.add(ontop_sid, new_sid, stm_text, true);
    }

    exec(sid) {
        this.sendCommand(["Exec", sid]);
    }

    cancel(sid) {
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

    queryPromise(sid, rid, query) {
        let pfr = new PromiseFeedbackRoute();
        rid = this.query(sid, rid, query);

        this.routes[rid] = [pfr];
        pfr.atexit = () => { delete this.routes[rid]; };
        return pfr.promise;
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
}


class PromiseFeedbackRoute {
    constructor() {
        this.promise = new Promise((resolve, reject) => {
            this.resolve = resolve;
            this.reject = reject;
        });
        this.atexit = () => {};
    }

    feedMessage(sid, lvl, loc, msg) {
        this.atexit();
        if (lvl[0] === 'Error')
            this.reject(msg);
        else
            this.resolve(msg);
    }

    feedProcessed(sid) {
        /* ignore */
    }
}


if (typeof document !== 'undefined' && document.currentScript)
    CoqWorker.scriptDir = document.currentScript.attributes.src.value.replace(/[^/]*$/, '');

if (typeof module !== 'undefined')
    module.exports = {CoqWorker}
