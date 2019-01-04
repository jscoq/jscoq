"use strict";


class CoqWorker {
    constructor(scriptPath) {
        this.options = {
            debug: false
        };
        this.observers = [];

        // Create actual worker. Ideally, CoqWorker would extend Worker, but this is
        // not supported at the moment.
        this.worker = new Worker(scriptPath || (CoqWorker.scriptDir + "jscoq_worker.js"))
        this.worker.onmessage = evt => this.coq_handler(evt);
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

    add(ontop_sid, new_sid, stm_text) {
        this.sendCommand(["Add", ontop_sid, new_sid, stm_text]);
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

    loadPkg(base_path, pkg) {
        this.sendCommand(["LoadPkg", base_path, pkg]);
    }

    infoPkg(base_path, pkgs) {
        this.sendCommand(["InfoPkg", base_path, pkgs]);
    }

    coq_handler(evt) {

        var msg     = evt.data;
        var msg_tag = msg[0];
        var msg_args = msg.slice(1);
        var handled = false;

        if(this.options.debug)
            console.log("coq_evt", msg);

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
}


CoqWorker.scriptDir = document.currentScript.attributes.src.value.replace(/[^/]*$/, '');
