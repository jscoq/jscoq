import { ExecCore, ExecCoreOptions } from 'wasi-kernel';
import type { DynamicLibrary } from 'wasi-kernel/lib/kernel/bits/dyld';

import { Environ } from 'wasi-kernel/lib/kernel/exec';


interface OCamlCAPI {
    malloc(sz: i32): i32;
    free(p: i32): void;
    caml_alloc_string(len: i32): i32;
    caml_named_value(name: i32): i32;
    caml_callback(closure: i32, arg: i32): i32;
}

namespace OCamlCAPI {
    export function Val_int(v: number): i32 { return (v << 2) | 1; }
    export function Val_bool(b: boolean): i32 { return Val_int(+b); }
    export function Int_val(v: i32) { return v >> 1; }
    export function Bool_val(v: i32) { return !!Int_val(v); }
    export const Val_unit = Val_int(0);
    export const Val_false = Val_int(0);
    export const Val_true = Val_int(1);
}

type i32 = number;


class OCamlExecutable extends ExecCore {

    opts: OCamlExecutableOptions
    api: OCamlCAPI
    callbacks: {[name: string]: (arg: i32) => i32}

    constructor(opts: OCamlExecutableOptions) {
        super(opts);
    }

    initialEnv(): Environ {
        return {...super.initialEnv(),
            'OCAMLFIND_CONF': '/lib/findlib.conf', 'COQLIB': '/lib'};
    }

    async run(bytecodeFile: string, args: string[], callbacks: string[] = []) {
        var bin = this.opts.binDir || '../bin';

        for (let p of this.preloads())
            await this.proc.dyld.preload(p.name, p.uri, p.reloc);

        await this.start(`${bin}/ocamlrun.wasm`,
                         ['ocamlrun', bytecodeFile, ...args], this.env);

        this.api = <any>this.wasm.instance.exports as OCamlCAPI;
        this.callbacks = this._getCallbacks(callbacks);
    }

    preloads() {
        var bin = this.opts.binDir || '../bin';
        return ['dllcamlstr', 'dllunix', 'dllthreads'].map(b => ({
            name: `${b}.so`, uri: `${bin}/${b}.wasm`, reloc: STDLIB_STUBS[b]
        } as {name: string, uri: string, reloc?: any}));
    }

    to_caml_string(s: string) {
        var bytes = new TextEncoder().encode(s),
            a = this.api.caml_alloc_string(bytes.length);
        this.proc.membuf.set(bytes, a);
        return a;
    }

    _getCallbacks(names: string[]) {
        var callbacks: {[name: string]: (arg: i32) => i32} = {},
            x = this.api.malloc(Math.max(...names.map(s => s.length)) + 1);;
        for (let name of names) {
            this.proc.membuf.write(name + "\0", x);
            let closure_f = this.api.caml_named_value(x);
            if (closure_f) {
                callbacks[name] = (arg: i32) =>
                    this.api.caml_callback(this.proc.mem.getUint32(closure_f, true), arg);
            }
        }
        this.api.free(x);
        return callbacks;     
    }

}


type OCamlExecutableOptions = ExecCoreOptions & {
    binDir?: string
};


/**
 * These symbols from `dllunix` are present in `wasi-libc`, but
 * unfortunately not linked into `ocamlrun`, and `wasi-libc` cannot
 * be linked to dynamic libraries.
 * So these symbols are replaced with stubs to silence some warnings;
 * hopefully that won't be too bad for Coq.
 */
const UNIX_STUBBED = ['fstat', 'fsync', 'strchr', 'fcntl', 'ftruncate',
    'getgrnam', 'gmtime', 'localtime', 'mktime', 'lockf', 'pwrite',
    'sysconf', 'mmap', 'munmap', 'putenv', 'rewinddir', 'select',
    'nanosleep', 'tcgetattr', 'tcsetattr', 'time', 'truncate'];

const STDLIB_STUBS: {[lib: string]: DynamicLibrary.Relocations} = {
    'dllunix': {
        js: mapAllTo(UNIX_STUBBED, () => 0)
    }
}

function mapAllTo<T>(keys: string[], value: T) {
    return Object.fromEntries(keys.map(nm => [nm, value]));
}



export { OCamlExecutable, OCamlCAPI }
