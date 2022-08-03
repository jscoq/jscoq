import path from 'path';
import arreq from 'array-equal';
import { EventEmitter } from 'events';
import { FSInterface } from './fsif';
import { SearchPathElement, CoqProject, InMemoryVolume, JsCoqCompat } from './project';



abstract class Batch {

    volume: FSInterface = null
    loadpath: LoadPath = []

    abstract command(cmd: any[]): void;
    abstract expect(yes: (msg: any[]) => boolean,
                    no?: (msg: any[]) => boolean): Promise<any[]>;

    async do(...actions: (any[] | ((msg: any[]) => boolean))[]) {
        var replies = [];

        for (let action of actions)
            if (typeof action === 'function')
                replies.push(await this.expect(action));
            else this.command(action);

        return replies;
    }

    isError(msg: any[]) {
        return ['JsonExn', 'CoqExn'].includes(msg[0]);
    }    

    async loadPackages(pkgs: Set<string>): Promise<LoadPath> {
        if (pkgs.size > 0)
            await this.do(
                ['LoadPkg', [...pkgs].map(pkg => `+${pkg}`)],
                msg => msg[0] == 'LoadedPkg'
            );
        return undefined;
    }

    async init() {
        await this.do(['Init', {lib_path: this.loadpath}]);
    }

    docOpts(mod: SearchPathElement, outfn: string) {
        /* @todo why does `mode: ['Vo']` end up producing an incorrect module name? */
        return { top_name: mod.logical.join('.'), // mode: ['Vo'],
                 lib_init: PRELUDE };
    }

    async install(mod: SearchPathElement, volume: FSInterface, root: string, outfn: string, compiledfn: string, content?: Uint8Array) {
        console.warn('Batch.install not implemented; mod =', mod);
    }
}


class BatchWorker extends Batch {

    worker: Worker

    constructor(worker: Worker) {
        super();
        this.worker = worker;
    }

    command(cmd: any[]) {
        console.log('batch', cmd);
        this.worker.postMessage(cmd);
    }

    expect(yes: (msg: any[]) => boolean,
           no:  (msg: any[]) => boolean = m => this.isError(m)) {
        const worker = this.worker;
        return new Promise<any[]>((resolve, reject) => {
            function h(ev: {data: any[]}) {
                if (yes(ev.data))       { cleanup(); resolve(ev.data); }
                else if (no(ev.data))   { cleanup(); reject(ev.data); }
            }
            worker.addEventListener('message', h);
            function cleanup() { worker.removeEventListener('message', h); }
        });
    }    

}


class CompileTask extends EventEmitter {

    batch: Batch
    inproj: CoqProject
    outproj: CoqProject
    infiles: SearchPathElement[] = [];
    outfiles: SearchPathElement[] = [];
    volume: FSInterface

    opts: CompileTaskOptions

    _stop = false;

    constructor(batch: Batch, inproj: CoqProject, opts: CompileTaskOptions = {}) {
        super();
        this.batch = batch;
        this.inproj = inproj;
        this.opts = {...CompileTask.DEFAULT_OPTIONS, ...opts};

        this.volume = batch.volume || new InMemoryVolume();
    }

    async run(outname?: string) {
        if (this._stop) return;

        var coqdep = this.inproj.computeDeps(),
            plan = coqdep.buildOrder();

        await this.batch.loadPackages(coqdep.extern);
        await this.batch.init();

        for (let mod of plan) {
            if (this._stop) break;
            if (mod.physical.endsWith('.v') && this.alreadyDone(coqdep.depsOf(mod)))
                await this.compile(mod);
        }
    
        return this.output(outname);
    }

    alreadyDone(modules: SearchPathElement[]) {
        return modules.every(mod => !mod.volume ||
            this.outfiles.some(cmod => arreq(cmod.logical, mod.logical)));
    }

    async compile(mod: SearchPathElement, opts=this.opts) {
        var {volume, logical, physical} = mod,
            root = opts.buildDir || '/lib',
            infn = `${path.join(root, ...logical)}.v`, outfn = `${infn}o`;
        this.infiles.push(mod);

        this.emit('progress', [{filename: physical, status: 'compiling'}]);

        try {
            let [, [, outfn_, vo]] = await this.batch.do(
                ['Put',     infn, volume.fs.readFileSync(physical)],
                ['NewDoc',  this.batch.docOpts(mod, outfn)],
                ['ReassureLoadPath', this.batch.loadpath],
                ['Load',    infn],         msg => msg[0] == 'Loaded',
                ['Compile', outfn],        msg => msg[0] == 'Compiled');

            await this.batch.install(mod, this.volume, root, outfn, outfn_, vo);

            this.outfiles.push({volume: this.volume, 
                                logical, physical: outfn});

            this.emit('progress', [{filename: physical, status: 'compiled'}]);
        }
        catch (e) {
            console.error(e);
            this.emit('report', e, mod);
            this.emit('progress', [{filename: physical, status: 'error'}]);
            if (!opts.keepGoing) throw e;
        }
    }

    stop() { this._stop = true; }

    output(name?: string) {
        this.outproj = new CoqProject(name || this.inproj.name || 'out',
                                      this.volume);
        for (let mod of this.outfiles) {
            mod.pkg = this.outproj.name;
            this.outproj.searchPath.add({
                physical: path.dirname(mod.physical), 
                logical: mod.logical.slice(0, -1)
            });
        }
        this.outproj.setModules(this._files());
        return this.outproj;
    }
        
    toPackage(filename?: string, extensions?: string[]) {
        return this.outproj.toPackage(filename, extensions,
            this.opts.jscoq ? JsCoqCompat.transpilePluginsJs : undefined,
            this.opts.jscoq ? JsCoqCompat.backportManifest : undefined);
    }

    _files(): SearchPathElement[] {
        return [].concat(this.infiles, this.outfiles);
    }

    static DEFAULT_OPTIONS : CompileTaskOptions = {
        buildDir: "/lib", resume: false, keepGoing: true, jscoq: false
    }
}

type CompileTaskOptions = {
    buildDir?: string
    resume?: boolean     // pick up from previous build
    keepGoing?: boolean  // carry on in face of compile errors
    jscoq?: boolean      // jsCoq package format (compatibility mode)
};

type LoadPath = [string[], string[]][];

const PRELUDE = ["Coq.Init.Prelude"];


class AnalyzeTask {

    batch: Batch

    constructor(batch: Batch) {
        this.batch = batch;
    }

    async prepare() {
        await this.batch.do(
            ['Init', {}],
            ['NewDoc', {}],   msg => msg[0] === 'Ready'
        );
    }

    async runVernac(cmds: string[]) {
        let add = (st: string) => ['Add', null, null, st, true],
            vernac = (st: string) => [add(st), msg => msg[0] === 'Added'];

        try {
            var vr = await this.batch.do(...([].concat(...cmds.map(vernac))));
        }
        catch { console.log('> vernac execution failed.'); throw new BuildError(); }

        var tip = vr.length > 0 ? vr.slice(-1)[0][1] : 0;
        if (tip)
            await this.batch.do(['Exec', tip]);  /** @todo wait for `Processed`? */
        return tip;
    }

    async inspectSymbolsOfModules(pkgs: {[pkg: string]: string[]}) {
        var modules = [].concat(...Object.values(pkgs)) as string[],
            tip = await this.runVernac(modules.map(mp => `Require Import ${mp}.`));

        var sr = await this.batch.do(
            ['Query', tip, 0, ['Inspect', ['All']]],
            msg => msg[0] === 'SearchResults'
        );

        var symb = Object.fromEntries(Object.keys(pkgs).map(k => [k, []]));

        for (let r of sr) {
            for (let entry of r[2]) {
                var label = entry.basename[1],
                    dp = entry.prefix.dp[1].map(x => x[1]).reverse(),
                    prefix = dp.concat(entry.prefix.mod_ids.map(id => id[1])),
                    mod = dp.join('.');
                for (let [pkg, mns] of Object.entries(pkgs))
                    if (mns.includes(mod)) symb[pkg].push({prefix, label});
            }
        }

        return symb;
    }

}


class BuildError { }



export { Batch, BatchWorker, CompileTask, CompileTaskOptions, AnalyzeTask, BuildError }
