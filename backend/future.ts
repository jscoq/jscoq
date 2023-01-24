export class Future<A> {

    promise: Promise<A>;
    _resolve: (value : A | PromiseLike<A>) => void;
    _reject: (reason? : any) => void;
    _done: boolean;
    _success: boolean;

    constructor() {
        this.promise = new Promise((resolve, reject) => {
            this._resolve = resolve;
            this._reject = reject;
        });
        this._done = false;
        this._success = false;
    }

    resolve(val) { if (!this._done) { this._done = this._success = true; this._resolve(val); } }
    reject(err?) { if (!this._done) { this._done = true; this._reject(err); } }

    then(cont)      { return this.promise.then(cont); }

    isDone()        { return this._done; }
    isSuccessful()  { return this._success; }
    isFailed()      { return this._done && !this._success; }
}

type RouteMessage = { sid: number; lvl: string; loc: any; msg: string }

export class PromiseFeedbackRoute<A> extends Future<A> {
    atexit: (_ : void) => void;
    messages: RouteMessage[];
    _got_processed: boolean;

    constructor() {
        super();
        this.atexit = () => {};
        this.messages = [];
        this._got_processed = false;
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
