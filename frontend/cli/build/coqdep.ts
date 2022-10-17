import { FSInterface, fsif_native } from './fsif';
import { SearchPath, SearchPathElement } from './project';



class CoqDep {

    volume: FSInterface
    searchPath: SearchPath
    deps: {from: SearchPathElement, to: SearchPathElement[]}[]
    extern: Set<string>

    constructor(volume: FSInterface = fsif_native) {
        this.volume = volume;
        this.searchPath = new SearchPath(volume);
        this.deps = [];
        this.extern = new Set();
    }

    processPackage(pkg: string) {
        this.processModules(this.searchPath.modulesOf(pkg));
    }

    processModules(modules: Iterable<SearchPathElement>) {
        for (let mod of modules) this.processModule(mod);
    }

    processModule(mod: SearchPathElement) {
        if (mod.physical.endsWith('.v'))
            this.processVernacFile(mod.physical, mod);
    }

    processVernacFile(filename: string, mod?: SearchPathElement) {
        mod = mod || {volume: this.volume,
                      logical: this.searchPath.toLogical(filename),
                      physical: filename};
        if (mod.logical) {
            this.processVernac(mod.volume.fs.readFileSync(filename, 'utf-8'), 
                               mod);
        }
    }

    processVernac(v_text: string, mod: SearchPathElement) {
        var deps = [...this._extractImports(v_text)];
        if (deps.length > 0)
            this.deps.push({from: mod, to: deps});
        for (let pkg of this._getExtern(deps))
            this.extern.add(pkg);
    }

    /**
     * Gets the list of modules that `mod` depends on.
     * @note looks for the module by physical filename.
     */
    depsOf(mod: SearchPathElement) {
        var d = this.deps.find(d => d.from.physical === mod.physical);
        return d ? d.to : [];
    }

    depsToJson() {
        var d = {},
            key = (mod: SearchPathElement) => mod.logical.join('.');

        for (let entry of this.deps)
            d[key(entry.from)] = entry.to.map(key);

        return d;
    }

    /**
     * Basically, topological sort.
     * @todo allow parallel builds?
     */
    buildOrder(modules?: SearchPathElement[] | Generator<SearchPathElement>) {
        if (!modules) modules = this.searchPath.modules();

        // Prepare graph
        var adj: Map<string, string[]> = new Map(),
            modulesByKey: Map<string, SearchPathElement> = new Map(),
            key = (mod: SearchPathElement) => mod.logical.join('.');

        for (let {from, to} of this.deps) {
            let ku = key(from);
            for (let v of to) {
                let kv = key(v);
                adj.set(kv, (adj.get(kv) || []).concat([ku]));
            }
        }

        for (let mod of modules) {
            var k = key(mod);
            if (mod.physical.endsWith('.v') || !modulesByKey.has(k))
                modulesByKey.set(k, mod);
        }

        // Now the topological sort
        var scan = this._topologicalSort([...modulesByKey.keys()], adj);
        return scan.map(k => modulesByKey.get(k));
    }

    _topologicalSort(vertices: string[], adj: Map<string, string[]>) {
        var indegrees: Map<string, number> = new Map();
    
        for (let v of vertices)
            indegrees.set(v,
                vertices.filter(u => (adj.get(u) || []).includes(v)).length);

        // Start scan
        var scan = [],
            worklist = vertices.filter(k => !indegrees.get(k));  // roots

        while (worklist.length > 0) {
            var u = worklist.shift();
            scan.push(u);
            for (let v of adj.get(u) || []) {
                let r = indegrees.get(v) - 1;
                indegrees.set(v, r);
                if (r == 0) worklist.push(v);
            }
        }

        if (scan.length < vertices.length)
            console.warn('coqdep: cyclic dependency detected',
                vertices.filter(k => scan.indexOf(k) == -1));

        return scan;
    }

    _extractImports(v_text: string) {
        return this._uniqBy(this._extractImportsBase(v_text),
                            mod => mod.logical.join('.'));
    }

    *_extractImportsBase(v_text: string) {
        // Strip comments
        v_text = v_text.replace(/\(\*[^]*?\*\)/g, ' '); /** @todo nested comments */

        // Split sentences
        for (let sentence of v_text.split(/[.](?:\s|$)/)) {
            var mo = /^\s*(?:From\s+(.*?)\s+)?Require(\s+(?:Import|Export))*\s+(.*)/
                     .exec(sentence);
            if (mo) {
                var [_, prefix, import_export, modnames] = mo,
                    lmodnames = modnames.split(/\s+/);

                for (let modname of lmodnames) {
                    for (let mod of this._resolve(prefix, modname))
                        yield mod;
                }
            }
        }
    }

    _resolve(prefix: string, suffix: string) {
        return this.searchPath.findModules(prefix, suffix);
    }

    *_getExtern(deps: SearchPathElement[]) {
        var pi = this.searchPath.packageIndex;
        if (pi) {
            for (let mod of deps)
                yield* pi.findPackageDeps(null, mod.logical, true);
        }
    }

    *_uniqBy<T>(gen: Generator<T>, key: (v:T) => string) {
        var seen: Set<string> = new Set();
        for (let v of [...gen]) {
            var k = key(v);
            if (!seen.has(k)) {
                seen.add(k); yield v;
            }
        }
    }

}



export { CoqDep }
