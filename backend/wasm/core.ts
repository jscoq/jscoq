import { EventEmitter } from 'events';
import { isBrowser, isWebWorker } from 'browser-or-node';
import { OCamlExecutable, OCamlCAPI } from './ocaml_exec';
import { WorkerInterrupts } from './interrupt';
import { IO, FetchMode } from './io';
import { PackageManager } from './pkgs';

export class IcoqPod extends EventEmitter {

    core: OCamlExecutable
    intr: WorkerInterrupts

    binDir: string
    nmDir: string
    io: IO
    pkgs: PackageManager

    constructor(binDir?: string, nmDir?: string, fetchMode: FetchMode = DEFAULT_FETCH_MODE) {
        super();
        binDir = binDir || (fetchMode === 'fs' ? './bin' : '../bin');
        this.binDir = binDir;
        this.nmDir = nmDir ?? '../node_modules';

        this.core = new OCamlExecutable({stdin: false, tty: false, binDir: `${nmDir}/ocaml-wasm/bin`});

        var utf8 = new TextDecoder();
        this.core.on('stream:out', ev => console.log(utf8.decode(ev.data)));

        this.io = new IO(fetchMode);
        this.intr = new WorkerInterrupts();

        this.pkgs = new PackageManager(this.emit, this.answer, this.putFile, this.io, this.binDir);
    }

    get fs() { return this.core.fs; }

    async boot() {
        await this.upload(`../backend/wasm/wacoq_worker.bc`, '/lib/icoq.bc');
        // await this.findlibStartup(); /* @todo */

        this._preloadStub();

        await this.core.run('/lib/icoq.bc', [], ['wacoq_post']);
    }

    async upload(fromUri: string, toPath: string) {
        var content = await this.io._fetch(fromUri);
        this.putFile(toPath, content);
    }

    putFile(filename: string, content: Uint8Array | string) {
        if (!filename.startsWith('/')) filename = `/lib/${filename}`;
        // needs to be synchronous
        this.fs.mkdirpSync(filename.replace(/[/][^/]+$/, ''))
        this.fs.writeFileSync(filename, content);
    }

    getFile(filename: string) {
        if (!filename.startsWith('/')) filename = `/lib/${filename}`;
        var buf: Uint8Array = null;
        try { buf = <any>this.fs.readFileSync(filename); } catch { }
        this.answer([['Got', filename, buf]]);
    }

    command(cmd: any[]) {
        switch (cmd[0]) {
        case 'LoadPkg':        this.pkgs.loadPackages(cmd[1]);          return;
        }

        const wacoq_post = this.core.callbacks && this.core.callbacks.wacoq_post;
        if (!wacoq_post) return;

        var json = (typeof cmd === 'string') ? cmd : JSON.stringify(cmd),
            answer = wacoq_post(this.core.to_caml_string(json));
        this._answer(answer);
    }

    answer(msgs: any[][]) {
        for (let msg of msgs) this.emit('message', msg);
    }

    _answer(ptr: number) {
        var cstr = this.core.proc.userGetCString(ptr);
        this.answer(JSON.parse(<any>cstr));
    }

    _interrupt_pending() {
        return OCamlCAPI.Val_bool(this.intr.pending());
    }

    /**
     * (internal) Initializes the dllcoqrun_stub shared library.
     */
    _preloadStub() {
        this.core.proc.dyld.preload(
            'dllzarith.so', `${this.nmDir}/@ocaml-wasm/4.12--zarith/bin/dllzarith.wasm`);
        this.core.proc.dyld.preload(
            'dllbase_stubs.so', `${this.nmDir}/@ocaml-wasm/4.12--janestreet-base/bin/dllbase_stubs.wasm`);
        this.core.proc.dyld.preload(
            'dllbase_internalhash_types_stubs.so', `${this.nmDir}/@ocaml-wasm/4.12--janestreet-base/bin/dllbase_internalhash_types_stubs.wasm`);
        this.core.proc.dyld.preload(
            'dllcoqrun_stubs.so', `${this.binDir}/dllcoqrun_stubs.wasm`);
        /** @ouch these null stubs are needed because of some spurious dependency */
        this.core.proc.dyld.preload(
            'dllbigstringaf_stubs.so', `${this.binDir}/dlllib_stubs.wasm`,
            {
                js: {
                    bigstringaf_blit_to_bytes: (vsrc, vsrc_off, vdst, vdst_off, vlen) => { },
                    bigstringaf_blit_to_bigstring: (vsrc, vsrc_off, vdst, vdst_off, vlen) => {},
                    bigstringaf_blit_from_bytes: (vsrc, vsrc_off, vdst, vdst_off, vlen) => {},
                    bigstringaf_memcmp_bigstring: (vba1, vba1_off, vba2, vba2_off, vlen) => {},
                    bigstringaf_memcmp_string: (vba, vba_off, vstr, vstr_off, vlen) => {},
                    bigstringaf_memchr: (vba, vba_off, vchr, vlen) => {},
                }
            });
        this.core.proc.dyld.preload(
            'dlllib_stubs.so', `${this.binDir}/dlllib_stubs.wasm`,
            {
                js: {
                    wacoq_emit: (s:number) => this._answer(s),
                    interrupt_pending: (_:number) => this._interrupt_pending(),
                    interrupt_setup: (opaque) => this.intr.setup(opaque),
                    read_file: (name) => this.getFile(name),
                    write_file: (name, content) => this.putFile(name, content),
                    coq_vm_trap: (u:void) => console.warn('coq vm trap!')
                }
            }
        );
    }
}

const DEFAULT_FETCH_MODE: FetchMode = (isBrowser || isWebWorker) ? 'browser' : 'fs';
