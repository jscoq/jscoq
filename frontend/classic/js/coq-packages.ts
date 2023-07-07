// Backend imports
import { ArrayFuncs } from '../../common/etc.js';
import { CoqWorker, backend } from '../../../backend';

// Frontend imports (not so clear for the package manager
import JSZip from 'jszip';
import $ from 'jquery';

interface BundleInfo {
    row : string;
}

export class PackageManager {

    /**
     * Creates the packages UI and loading manager.
     *
     * @param {Element} panel_dom <div> element to hold the package entries
     * @param {object} packages an object containing package URLs and lists of 
     *   names in the format
     *   `{'base_uri1', ['pkg_name1', 'pkg_name2', ...], 'base_uri2': ...}`.
     * @param {object} pkg_path_aliases mnemonic for specific base URIs
     * @param {CoqWorker} coq reference to the `CoqWorker` instance to send
     *   load requests to
     */
    backend : backend;
    panel : any;
    bundles : Map<string, BundleInfo>;
    loaded_pkgs: string[];
    coq : CoqWorker;
    packages : CoqPkgInfo[];
    packages_by_name: any;
    packages_by_uri: any;
    index ?: PackageIndex;

    constructor(panel_dom, packages, pkg_path_aliases, coq, backend=coq.config.backend) {

        this.backend = backend;
        this.panel         = panel_dom;
        this.bundles       = new Map();
        this.loaded_pkgs   = [];
        this.coq           = coq;

        this.coq.observers.push(this);
        this.packages = [];
        this.packages_by_name = {};
        this.packages_by_uri = {};

        this.initializePackageList(packages, pkg_path_aliases);
    }

    /**
     * Creates CoqPkgInfo objects according to the paths in names in the given
     * `packages` object.
     * @param {object} packages (see constructor)
     * @param {object} aliases (ditto)
     */
    initializePackageList(packages : string[], aliases={}) {
        this.packages = [];
        this.packages_by_name = {};
        this.packages_by_uri = {};

        // normalize all URI paths to end with a slash
        /** @type {(path: string) => string} */
        let mkpath = path => path && path.replace(/([^/])$/, '$1/');

        for (let [key, pkg_names] of Object.entries(packages)) {
            let base_uri = mkpath(aliases[key] || key);

            for (let pkg of pkg_names) {
                var uri = mkpath(aliases[`${key}/${pkg}`]) || base_uri;
                this.addPackage(new CoqPkgInfo(pkg, uri));
            }
        }
    }

    /**
     * Returns the default package path
     *
     * @param {string} base_path root path of jscoq package
     * @return {string}
     * @memberof PackageManager
     */
    static defaultPkgPath(base_path) {
        return new URL('coq-pkgs', base_path).href;
    }

    populate() {
        this.index = new PackageIndex(this.backend);

        return Promise.all(this.packages.map(async pkg => {
            var manifest = await pkg.fetchInfo();
            if (manifest) this.addBundleInfo(pkg.name, manifest);
            else this.coqLibError(pkg.name);
        }));
    }

    /**
     * Adds a package
     *
     * @param {*} pkg
     * @memberof PackageManager
     */
    addPackage(pkg) {
        this.packages.push(pkg);
        this.packages_by_name[pkg.name] = pkg;
        (this.packages_by_uri[pkg.base_uri] = 
            this.packages_by_uri[pkg.base_uri] || []).push(pkg.name);
    }

    getPackage(pkg_name) {
        var pkg = this.packages_by_name[pkg_name];
        if (!pkg) throw new Error(`internal error: unrecognized package '${pkg_name}'`);
        return pkg;
    }

    hasPackageInfo(pkg_name) {
        var pkg = this.packages_by_name[pkg_name];
        return pkg && pkg.info;
    }

    addRow(bname, desc = bname, parent) {
        var row = $('<div>').addClass('package-row').attr('data-name', bname)
            .append($('<button>').addClass('download-icon')
                    .attr('title', "Download package")
                    .on('click', () => { this.loadPkg(bname); }))
            .append($('<span>').addClass('desc').text(desc)
                    .on('click', () => { this._expandCollapseRow(row); }));

        if (parent) {
            parent.row.append(row);
        }
        else {
            // Find bundle's proper place in the order among existing entries
            var pkg_names = this.packages.map(p => p.name),
                place_before = null, idx = pkg_names.indexOf(bname);

            if (idx > -1) {
                for (let e of $(this.panel).children()) {
                    let eidx = pkg_names.indexOf($(e).attr('data-name'));
                    if (eidx == -1 || eidx > idx) {
                        place_before = e;
                        break;
                    }
                }
            }

            this.panel.insertBefore(row[0], place_before /* null == at end */ );
        }

        return this.bundles[bname] = { row };
    }

    addBundleInfo(bname : string, pkg_info : CoqPkgInfo, parent? : { row : JQuery<HTMLElement>}) {

        var bundle = this.addRow(bname, pkg_info.name, parent);

        var pkg = this.getPackage(bname);
        pkg.info = pkg_info;

        if (pkg_info.chunks) {
            pkg.chunks = [];

            for (let chunk of pkg_info.chunks) {
                var subpkg = new CoqPkgInfo(chunk.name, pkg.base_uri);
                subpkg.info = chunk;
                this.addPackage(subpkg);
                this.addBundleInfo(subpkg.name, chunk, bundle);
                pkg.chunks.push(subpkg);
                subpkg.parent = pkg;
            }
        }
        else {
            pkg.setArchive(pkg_info.archive);
        }

        if (pkg.archive) {
            pkg.archive.onProgress = evt => this.showPackageProgress(bname, evt);
        }
        else {
            /** @todo is this case even needed? */
            if (!pkg.chunks)
                throw new Error("packages without archives are obsolete");
        }

        this.index.add(pkg_info);

        this.dispatchEvent(new Event('change'));
    }

    async addBundleZip(bname: string, resource: any, pkg_info?: CoqPkgInfo) {
        // @ts-expect-error
        var pkg_info = pkg_info || {};

        var archive = await new CoqPkgArchive(resource).load();

        return archive.getPackageInfo().then(pi => {
            bname = bname || pi.name;

            if (!bname) throw new Error('invalid archive: missing package manifest (coq-pkg.json)');
            if (this.packages_by_name[bname] && this.packages_by_name[bname].info)
                throw new Error(`package ${bname} is already present`);

            for (let k in pi)
                if (!pkg_info[k]) pkg_info[k] = pi[k];

            var pkg = new CoqPkgInfo(bname, '');
            this.packages.push(pkg);
            this.packages_by_name[bname] = pkg;

            this.addBundleInfo(bname, pkg_info);
            pkg.archive = archive;
            return pkg;
        });
    }

    waitFor(init_pkgs) {
        let all_set = () => init_pkgs.every(x => this.hasPackageInfo(x));

        return new Promise((resolve, reject) => {
            var observe = () => {
                if (all_set()) {
                    this.removeEventListener('change', observe);
                    resolve({});
                    return true;
                }
            };
            if (!observe())
                this.addEventListener('change', observe);
            /** @todo reject the promise if there are no more packages whose infos are pending */
        });
    }

    getUrl(pkg_name, resource) {
        return this.packages_by_name[pkg_name].getUrl(resource);
    }

    getLoadPath() {
        let prefix = m => m.replace(/[.][^.]+$/, ''),
            pkgs = (ms : string[]) => [...new Set(ms.map(prefix))].map(pkg => pkg.split('.'));

        return ArrayFuncs.flatten(this.loaded_pkgs.map(pkg_name => {
            let pkg = this.getPackage(pkg_name),
                phys = pkg.archive ? ['/lib'] : [];
            return pkgs(Object.keys(pkg.info.modules)).map(pkg => [pkg, phys]);
        }));
    }

    showPackage(bname) {
        var bundle = this.bundles[bname];
        if (bundle && bundle.row) {
            bundle.row.parents('div.package-row').addClass('expanded');
            this._scrollTo(bundle.row[0]);
        }
    }

    _scrollTo(el) {
        if (el.scrollIntoViewIfNeeded) el.scrollIntoViewIfNeeded();
        else el.scrollIntoView();
    }

    /**
     * Updates the download progress bar on the UI.
     * @param {string} bname package bundle name
     * @param {object} info? {loaded: <number>, total: <number>}
     */
    showPackageProgress(bname, info) {
        var bundle = this.bundles[bname];

        if (!bundle.bar) {
            // Add the progress bar if it does not exist already
            bundle.bar = $('<div>').addClass('progressbar');
            bundle.egg = $('<div>').addClass('progress-egg');

            bundle.bar.append(bundle.egg);
            bundle.row.append($('<div>').addClass('rel-pos').append(bundle.bar));
        }

        if (info && info.total) {
            var progress = (info.downloaded || info.loaded) / info.total,
                angle    = (progress * 1500) % 360;
            bundle.egg.css('transform', `rotate(${angle}deg)`);
            bundle.bar.css('width', `${Math.min(1.0, progress) * 100}%`);
        }
    }

    /**
     * Marks the package download as complete, removing the progress bar.
     * @param {string} bname package bundle name
     */
    showPackageCompleted(bname) {
        var bundle = this.bundles[bname];

        bundle.row.children('.rel-pos').remove();
        bundle.row.children('button.download-icon').addClass('checked')
                  .attr('title', 'Downloaded');

        var pkg = this.getPackage(bname);
        pkg.status = 'loaded';
        if (pkg.parent) this.showLoadedChunks(pkg.parent);
    }

    showLoadedChunks(pkg) {
        var bundle = this.bundles[pkg.name];
        bundle.row.addClass('has-chunks');

        var span = bundle.row.find('.loaded-chunks');
        if (span.length === 0)
            span = $('<span>').addClass('loaded-chunks')
                              .insertAfter(bundle.row.children('.desc'));

        var prefix = pkg.name + '-',
            shorten = name => name.startsWith(prefix) ? 
                              name.substr(prefix.length) : name;

        span.empty();
        for (let chunk of pkg.chunks) {
            if (chunk.status === 'loaded')
                span.append($('<span>').text(shorten(chunk.name)));
        }
        if (pkg.chunks.every(chunk => chunk.status === 'loaded'))
            this.showPackageCompleted(pkg.name);
    }

    /**
     * Adds a package from a dropped file and immediately downloads it.
     * @param {File} file a dropped File or a Blob that contains an archive
     */
    dropPackage(file) {
        this.expand();
        this.addBundleZip(undefined, file).then(pkg => {
            this._scrollTo(this.bundles[pkg.name].row[0]);
            this.loadPkg(pkg.name);
        })
        .catch(err => { alert(`${file.name}: ${err}`); });
    }

    _packageByURL(url) {
        var s = this._absoluteURL(url);
        for (let pkg of this.packages) {
            if (pkg.archive && s == pkg.archive.url) return pkg.name;
        }
    }

    _absoluteURL(url) {
        return new URL(url, this.coq.config.path).toString();
    }

    coqLibProgress(evt) {
        var pkg_name = this._packageByURL(evt.uri);

        if (pkg_name) {
            this.showPackageProgress(pkg_name, evt.download);
        }
    }

    coqLibLoaded(pkg) {
        var pkg_name = this._packageByURL(pkg) || pkg;
        this.loaded_pkgs.push(pkg_name);

        try {
            var pkg = this.getPackage(pkg_name);
            if (pkg._resolve) pkg._resolve();
            else pkg.promise = Promise.resolve();

            this.showPackageCompleted(pkg_name);
        }
        catch(e) { console.warn(e); }
    }

    coqLibError(pkg) {
        var pkg_name = this._packageByURL(pkg) || pkg;

        try {
            var pkg = this.getPackage(pkg_name),
                err = {msg: `error loading package '${pkg_name}'`};
            if (pkg._reject) pkg._reject(err);
            else pkg.promise = Promise.reject(err);
        }
        catch(e) { console.warn(e);  /* do we even care? */ }
    }
    /**
     * Loads a package from the preconfigured path.
     * @param {string} pkg_name name of package (e.g., 'init', 'mathcomp')
     * @param {boolean} show if `true`, the package is exposed in the list
     */
    loadPkg(pkg_name, show=true) {
        var pkg = this.getPackage(pkg_name), promise;

        if (pkg.promise) return pkg.promise;  /* load issued already */

        if (pkg.info.chunks) {
            promise = this.loadDeps(pkg.info.chunks.map(x => x.name), show);
        }
        else {
            promise = Promise.all([this.loadDeps(pkg.info.deps || [], show),
                                   this.loadArchive(pkg)]);
        }

        if (show) this.showPackage(pkg_name);

        pkg.promise = promise;
        return promise.then(() => pkg);
    }

    async loadDeps(deps, show=true) {
        await this.waitFor(deps);
        return Promise.all(
            deps.map(pkg => this.loadPkg(pkg, show)));
    }

    loadArchive(pkg) {
        switch (this.backend) {
        case 'js':
            return pkg.archive.unpack(this.coq)
                              .then(() => this.coqLibLoaded(pkg.name));
        case 'wa':
            return new Promise((resolve, reject) => {
                pkg._resolve = resolve; pkg._reject = reject;
                this.coq.loadPkg(pkg.getDownloadURL());
            });
        }
    }

    /**
     * Make all loaded packages unloaded.
     * This is called after the worker is restarted.
     * Does not drop downloaded/cached archives.
     */
    reset() {
        for (let pkg of this.packages) {
            delete pkg.promise;
        }
    }

    collapse() {
        this.panel.parentElement.classList.add('collapsed');
    }

    expand() {
        this.panel.parentElement.classList.remove('collapsed');
    }

    _expandCollapseRow(row) {
        row.toggleClass('expanded');
        if (row.hasClass('expanded')) {
            // account for CSS transition
            var anim = setInterval(() => row[0].scrollIntoViewIfNeeded(), 40);
            setTimeout(() => clearInterval(anim), 600);
        }
    }

    /**
     * (auxiliary method) traverses a graph spanned by a list of roots
     * and an adjacency functor. Implements DFS.
     * @param {array} roots starting points
     * @param {function} adjacent_out u => array of successors
     */
    _scan(roots, adjacent_out) {
        var collect = new Set(),
            work = roots.slice();
        while (work.length) {
            var u = work.pop();
            if (!collect.has(u)) {
                collect.add(u);
                for (let v of adjacent_out(u)) work.push(v);
            }
        }
        return collect;
    }

    // No portable way to create EventTarget instances of our own yet;
    // hijack the panel DOM element :\
    dispatchEvent(evt)             { this.panel.dispatchEvent(evt); }
    addEventListener(type, cb)     { this.panel.addEventListener(type, cb); }
    removeEventListener(type, cb)  { this.panel.removeEventListener(type, cb); }
}


/**
 * Holds list of modules in packages and resolves dependencies.
 */
class PackageIndex {
    backend : backend;
    moduleIndex : Map<any,any>;
    intrinsicPrefix : string;

    constructor(backend) {
        this.backend = backend;
        this.moduleIndex = new Map();
        this.intrinsicPrefix = "Coq";
    }

    add(pkgInfo) {
        for (let mod in pkgInfo.modules || {})
            this.moduleIndex.set(mod, pkgInfo);
    }

    *findModules(prefix, suffix, exact=false) {
        if (Array.isArray(prefix)) prefix = prefix.join('.');
        if (Array.isArray(suffix)) suffix = suffix.join('.');

        if (exact) {
            prefix = prefix ? prefix + '.' : '';
            if (this.moduleIndex.has(prefix + suffix)) yield prefix + suffix;
        }
        else {
            var dotsuffix = '.' + suffix,
                dotprefix = (prefix || this.intrinsicPrefix) + '.';
            for (let k of this.moduleIndex.keys()) {
                if (!prefix && k == suffix ||
                        k.startsWith(dotprefix) && k.endsWith(dotsuffix))
                    yield k;
            }
        }
    }

    findPackageDeps(prefix, suffix, exact=false) {
        var pdeps = new Set();
        for (let m of this.alldeps(this.findModules(prefix, suffix, exact)))
            pdeps.add(this.moduleIndex.get(m).name);
        return pdeps;
    }

    alldeps(mods) {
        return closure(new Set(mods), mod => {
            let pkg = this.moduleIndex.get(mod),
                o = (pkg && pkg.modules || {})[mod];
            return (o && o.deps) || [];
        });
    }
    
}


// function closure<T>(s: Set<T>, tr: (t: T) => T[]) {
function closure(s, tr) {
    var wl = [...s];
    while (wl.length > 0) {
        var u = wl.shift();
        for (let v of tr(u))
            if (!s.has(v)) { s.add(v); wl.push(v); }
    }
    return s;
}


class CoqPkgInfo {
    name: string;
    base_uri: string;
    info?: any;
    archive?: any;
    chunks?: any;
    parent?: any;
    promise?: any;

    constructor(name, base_uri) {
        this.name = name;
        this.base_uri = base_uri;

        this.info = undefined;
        this.archive = undefined;
        this.chunks = undefined;
        this.parent = undefined;
    }

    getUrl(resource) {
        // Generate URL with the package's base_uri as the base
        return new URL(resource, new URL(this.base_uri, location.href));
    }

    getDownloadURL() {
        // @todo create blob url for dropped files
        return this.archive && this.archive.url;
    }

    async fetchInfo(resource = `${this.name}.json`) {
        var req = await fetch(this.getUrl(resource));
        if (req.status == 200)
            return await req.json();
    }

    setArchive(resource = `${this.name}.coq-pkg`) {
        this.archive = new CoqPkgArchive(this.getUrl(resource));
    }
}


/**
 * Represents a bundle stored in a Zip archive; either a remote
 * file that has to be downloaded or a local one.
 */
class CoqPkgArchive {
    url ?: URL | string;
    blob : Blob;
    zip : JSZip;
    onProgress : ((evt : any) => void);

    constructor(resource) {
        if (resource instanceof URL || typeof resource === 'string')
            this.url = resource;
        else if (resource instanceof Blob)
            this.blob = resource;
        else if (resource.file /* JSZip-like */)
            this.zip = resource;
        else
            throw new Error(`invalid resource for archive: '${resource}'`);

        /** @type {(ev: any) => void} */
        this.onProgress = () => {};
    }

    load() {
        return this.zip ? Promise.resolve(this) :
            this.download().then(data =>
                JSZip.loadAsync(data)).then(zip =>
                    { this.zip = zip; return this; });
    }

    download() : Promise<any> {
        if (this.blob) {
            return this.blob.arrayBuffer();
        }
        else {
            // Here comes some boilerplate
            return new Promise((resolve, reject) => {
                var xhr = new XMLHttpRequest();
                xhr.responseType = 'arraybuffer';
                xhr.onload = () => resolve(xhr.response);
                xhr.onprogress = (evt) => requestAnimationFrame(() => this.onProgress(evt));
                xhr.onerror = () => reject(new Error("download failed"));
                xhr.open('GET', this.url);
                xhr.send();
            });
        }
    }

    readManifest() {
        var manifest = this.zip.file('coq-pkg.json');
        return manifest ?
                manifest.async('text').then(data => JSON.parse(data))
                .catch(err => {
                    console.warn(`malformed 'coq-pkg.json' in bundle ${this.url || ''} (${err})`);
                    return {}; 
                })
              : Promise.resolve({});
    }

    getPackageInfo() {
        return this.readManifest().then(pkg_info => {

            var entries_by_dir = {};

            this.zip.forEach((rel_path, entry) => {
                var mo = /^(?:(.*)[/])(.*[.](?:vo|vio|cm[ao]))$/.exec(rel_path);
                if (mo) {
                    var [, dir, fn] = mo;
                    (entries_by_dir[dir] = entries_by_dir[dir] || []).push(fn);
                }
            });

            var pkgs = [];
            for (let dir in entries_by_dir) {
                pkgs.push({
                    pkg_id: dir.split('/'),
                    vo_files: entries_by_dir[dir].map(x => [x])
                });
            }

            pkg_info.pkgs = pkgs;
            return pkg_info;
        });
    }

    async unpack(worker) {
        await this.load();

        var asyncs = [];
        this.zip.forEach((rel_path, entry) => {
            if (!entry.dir)
                asyncs.push((async () => {
                    var content = await entry.async('arraybuffer');
                    await worker.put(`/lib/${rel_path}`, content, 
                            /*transferOwnership=*/true);
                })());
        });
        await Promise.all(asyncs);
    }
}

// Local Variables:
// js-indent-level: 4
// End:
