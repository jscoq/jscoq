/* jsCoq
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2022 Shachar Itzhaky, Technion - Israel Institute of Technology, Haifa
 * Copyright (C) 2019-2022 Emilio J. Gallego Arias, Inria, Paris
 */

export type backend = 'js' | 'wa';

// Needs to be in sync with jscoq_proto.ml, maybe some day automatically
export interface Point {
    line : number,
    character : number,
    offset : number
}

export interface Range {
    start: Point
    end_: Point
}

export interface Diagnostic {
    range: Range
    severity: number
    message: string
    extra: any[]
}

interface CoqInitOptions {
  implicit_libs?: boolean,
  coq_options?: [string[], any[]][],
  debug?: { coq?: boolean, stm?: boolean }
}

interface DocumentOptions {
  top_name?: string,
  lib_path?: [string[], string[]][],
  lib_init?: string[]
}

export interface info {
    evar: number
    name?: any // Id.t option
}

type Block_type =
    ['Pp_hbox']
  | ['Pp_vbox', number]
  | ['Pp_hvbox', number]
  | ['Pp_hovbox', number];

export type Pp =
    ['Pp_empty']
  | ['Pp_string', string]
  | ['Pp_glue', Pp[]]
  | ['Pp_box', Block_type, Pp]
  | ['Pp_tag', string, Pp]
  | ['Pp_print_break', number, number]
  | ['Pp_force_newline']
  | ['Pp_comment', string[]];

export interface Hyp {
    names : string[],
    def?: Pp,
    ty: Pp
}

export interface Goal {
    info: info
    ty: Pp
    hyps: Hyp[]
}

export interface Goals {
    goals: Goal[]
    stack: [Goal[],Goal[]][]
    bullet?: Pp
    shelf: Goal[]
    given_up: Goal[]
}

import { InformationEvent } from 'http';
import { ppid } from 'process';
import { Future, PromiseFeedbackRoute } from './future';

/**
 * Main Coq Worker Class
 *
 */
type CoqEventObserver = Object

export class CoqWorkerConfig {

    path: URL;
    preload: URL[];
    backend: backend;
    debug: boolean;
    warn: boolean;

    // TODO: add smart constructor?
    constructor(basePath: string | URL, backend: backend) {
        this.path = CoqWorkerConfig.determineWorkerPath(basePath, backend);
        this.preload = this.getPreloads(basePath, backend)
        this.backend = backend;
        this.debug = false;
        this.warn = true;
    }

    /**
     * Default location for worker script -- computed relative to the URL
     * from which this script is loaded.
     */
    static determineWorkerPath(basePath: string | URL, backend: backend): URL {
        return new URL({'js': "backend/jsoo/jscoq_worker.bc.cjs",
                        'wa': "dist/wacoq_worker.js"
                       }[backend], basePath);
    }

    getPreloads(basePath: string | URL, backend: backend) {
        return {'js': [this.path],
                'wa': [new URL("backend/wasm/wacoq_worker.bc", basePath)]
               }[backend];
    }
}

// XXX: not sure we want to allow subclassing of the worker method,
// use case is pretty small to actually expose the internals here.
export class CoqWorker {

    config: CoqWorkerConfig;

    // No reason to access the worker
    protected worker: Worker;

    intvec: Int32Array;

    private load_progress: (ratio: number, ev: ProgressEvent) => void;

    // Misc
    private _boot : Future<void>;
    protected when_created: Promise<void>;
    protected _handler: (msg : any) => void;

    // Needs work to move to a standard typed registration mechanism
    // The protected here is not respected by the {package,coq}-manager(s), thus we have commented it out.
    /* protected */ observers: CoqEventObserver[];

    // Private stuff to handle our implementation of requests
    private request_pending: Future<object>[] = [];
    private request_nextid = 0;

    constructor(base_path : (string | URL), scriptPath : URL, worker, backend : backend) {

        this.config = new CoqWorkerConfig(base_path, backend);
        this.config.path = scriptPath || this.config.path;

        this.observers = [this];

        this.load_progress = (ratio, ev) => {};

        if (worker) {
            this.attachWorker(worker);
            this.when_created = Promise.resolve();
        }
        else {
            this.when_created = this.createWorker(this.config.path);
        }
    }

    /**
     * Adjusts a given URI so that it can be requested by the worker.
     * (the worker may have a different base path than the page.)
     */
    resolveUri(uri: string | URL) {
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

        this.attachWorker(await
            this.newWorkerWithProgress(this.config.path, this.config.preload));

        if (typeof window !== 'undefined')
            window.addEventListener('unload', () => this.end());

        if (this.config.backend == 'wa') {
            this._boot = new Future();
            return this._boot.promise;
        }
    }

    /**
     * @param {string} url
     */
    async newWorkerWithProgress(url: URL, preload: URL[]) {
        for (let uri of preload)
            await prefetchResource(uri, (pc, ev) => this.load_progress(pc, ev));
        // have to use `url` here so that the worker has correct base URI;
        // if it is big, it should be cached at this point though.
        return new Worker(url);
    }

    /**
     * @param {Worker} worker
     */
    attachWorker(worker) {
        this.worker = worker;
        this.worker.addEventListener('message',
            this._handler = evt => this.coq_handler(evt));
    }

    /**
     * Sends a Command to Coq worker
     *
     * @param {object[]} msg
     * @memberof CoqWorker
     */
    sendCommand(msg) {
        if(this.config.debug) {
            console.log("Posting: ", msg);
        }
        if (this.config.backend === 'wa') msg = JSON.stringify(msg);
        this.worker.postMessage(msg);
    }

    /**
     * @param {any[]} msg
     */
    sendDirective(msg) {   // directives are intercepted by the JS part of the worker
        this.worker.postMessage(msg);    // for this reason, they are not stringified
    }

    sendRequest(loc: number, req: object) {
        let id = this.request_nextid++,
            fut = this.request_pending[id] = new Future;
        this.sendCommand(["Request", {id, loc, v: req}]);
        return fut.promise;
    }

    coqResponse(resp: {id: number, res: object}) {
        console.warn(resp);
        let fut = this.request_pending[resp.id];
        delete this.request_pending[resp.id];
        fut?.resolve(resp.res);
    }

    /*--- jsCoq Protocol Commands ---*/

    init(coq_opts : CoqInitOptions) {
        this.sendCommand(["Init", coq_opts]);
    }

    newDoc(doc_opts : DocumentOptions, text : string) {
        this.sendCommand(["NewDoc", doc_opts, text]);
    }

    update(text : string, version : number) {
        this.sendCommand(["Update", text, version]);
    }

    loadPkg(url) {
        switch (this.config.backend) {
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
        this.sendCommand(["ReassureLoadPath", load_path]);
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
        if(this.config.debug) {
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

        this.end();  // kill!

        await this.createWorker(this.config.path);
    }

    end() {
        if (this.worker) {
            this.worker.removeEventListener('message', this._handler);
            this.worker.terminate();
            this.worker = undefined;
        }
    }

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

        if(this.config.debug) {
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

         if (!handled && this.config.warn) {
            console.warn('Message ', msg, ' not handled');
        }
    }

    coqBoot() {
        if (this._boot)
            this._boot.resolve(null);
    }
}

/**
 * This class is meant to support running the worker as a native subprocess,
 * available in waCoq through the `subproc` module.
 */
export class CoqSubprocessAdapter extends CoqWorker {
    constructor(base_path, backend) {
        /* Emilio: the require here fails, this is a fixme!
        const subproc = require('wacoq-bin/dist/subproc'),
              icoq = new subproc.IcoqSubprocess();
        super(base_path, null, icoq, backend, is_npm);
        window.addEventListener('beforeunload', () => icoq.end());
        */
       super(base_path, null, null, backend);
    }

    coq_handler(evt) {
        setTimeout(() => super.coq_handler(evt), 0); // force window context
    }
}

// some boilerplate from https://stackoverflow.com/questions/51734372/how-to-prefetch-video-in-a-react-application
function prefetchResource(url, progress = (pc:number,ev:ProgressEvent)=>{}) {
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
