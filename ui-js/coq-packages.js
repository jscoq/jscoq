"use strict";

class PackageManager {

    /**
     * Creates the packages UI and loading manager.
     *
     * @param {Element} panel_dom <div> element to hold the package entries
     * @param {object} packages an object containing package URLs and lists of 
     *   names in the format
     *   `{'base_uri1', ['pkg_name1', 'pkg_name2', ...], 'base_uri2': ...}`.
     * @param {object} pkg_path_aliases mnemonic for specific base URIs
     * @param {CoqWorker} coq reference to the Coq worker instance to send
     *   load requests to
     */
    constructor(panel_dom, packages, pkg_path_aliases, coq) {
        this.panel         = panel_dom;
        this.bundles       = {};
        this.loaded_pkgs   = [];
        this.coq           = coq;

        this.coq.observers.push(this);

        this.initializePackageList(packages, pkg_path_aliases);
    }

    /**
     * Creates CoqPkgInfo objects according to the paths in names in the given
     * `packages` object.
     * @param {object} packages (see constructor)
     * @param {object} aliases (ditto)
     */
    initializePackageList(packages, aliases={}) {
        this.packages = [];
        this.packages_by_name = {};
        this.packages_by_uri = {};

        // normalize all URI paths to end with a slash
        let mkpath = path => aliases[path] || path.replace(/([^/])$/, '$1/');

        for (let [key, pkg_names] of Object.entries(packages)) {
            let base_uri = mkpath(key);
            this.packages_by_uri[base_uri] = pkg_names;

            for (let pkg of pkg_names) {
                let pkg_info = new CoqPkgInfo(pkg, base_uri);
                this.packages.push(pkg_info);
                this.packages_by_name[pkg] = pkg_info;
            }
        }
    }

    static defaultPkgPath() {
        return new URL('../bin/coq/', CoqWorker.defaultScriptPath()).href;
    }

    populate() {
        this.index = new PackageIndex();

        return Promise.all(this.packages.map(async pkg => {
            var manifest = await pkg.fetchInfo();
            pkg.setArchive();
            this.addBundleInfo(pkg.name, manifest);
            this.index.add(manifest);
        }));
    }

    getPackage(pkg_name) {
        var pkg = this.packages_by_name[pkg_name];
        if (!pkg) throw new Error(`internal error: unrecognized package '${pkg_name}'`);
        return pkg;
    }

    addBundleInfo(bname, pkg_info) {

        var div  = document.createElement('div');
        var row = $(div);

        bname = bname || pkg_info.name;

        row.attr('data-name', bname);
        row.data('info', pkg_info);

        row.append($('<button>').addClass('download-icon')
                   .click(() => { this.loadPkg(bname); }));

        row.append($('<span>').text(pkg_info.name));

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

        this.panel.insertBefore(div, place_before /* null == at end */ );

        this.bundles[bname] = { div: div };

        this.dispatchEvent(new Event('change'));
    }

    async addBundleZip(bname, resource, pkg_info) {
        pkg_info = pkg_info || {};

        var archive = await new CoqPkgArchive(resource).load();

        return archive.getPackageInfo().then(pi => {
            bname = bname || pi.desc;

            if (!bname) throw new Error('invalid archive: missing package manifest (coq-pkg.json)');
            if (this.packages_by_name[bname]) throw new Error(`package ${bname} is already present`);

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
        let all_set = () => init_pkgs.every(x => this.getPackage(x).info);

        return new Promise((resolve, reject) => {
            var observe = () => {
                if (all_set()) {
                    this.removeEventListener('change', observe);
                    resolve();
                    return true;
                }
            };
            if (!observe())
                this.addEventListener('change', observe);
        });
    }

    searchBundleInfo(prefix, module_name, exact=false) {
        // Look for a .vo file matching the given prefix and module name
        var implicit = (prefix.length === 0),
            suffix = module_name.slice(0, -1),
            basename = module_name.slice(-1)[0],
            possible_filenames = ['.vo', '.vio'].map(x => basename + x);

        let startsWith = (arr, prefix) => arr.slice(0, prefix.length).equals(prefix);
        let endsWith = (arr, suffix) => suffix.length == 0 || arr.slice(-suffix.length).equals(suffix);

        let isIntrinsic = (arr) => arr[0] === 'Coq';

        let pkg_matches = exact ? pkg_id => pkg_id.equals(suffix)
                                : pkg_id => (implicit ? isIntrinsic(pkg_id)
                                                      : startsWith(pkg_id, prefix)) &&
                                            endsWith(pkg_id, suffix);

        for (let pkg of this.packages) {
            if (!pkg.info) continue;
            for (let prefix of pkg.info.pkgs) {
                if (pkg_matches(prefix.pkg_id) &&
                    prefix.vo_files.some(entry => possible_filenames.indexOf(entry[0]) > -1))
                    return { pkg: pkg.name,
                             info: pkg.info, 
                             module: prefix.pkg_id.concat([basename]) };
            }
        }
    }

    getUrl(pkg_name, resource) {
        return this.packages_by_name[pkg_name].getUrl(resource);
    }

    getLoadPath() {
        return this.loaded_pkgs.map( pkg_name => {
            let pkg = this.getPackage(pkg_name),
                phys = pkg.archive ? ['/lib'] : [];
            return pkg.info.pkgs.map( pkg => [pkg.pkg_id, phys] );
        }).flatten();
    }

    /**
     * Updates the download progress bar on the UI.
     * @param {string} bname package bundle name
     * @param {object} info {loaded: <number>, total: <number>}
     */
    showPackageProgress(bname, info) {
        var bundle = this.bundles[bname];

        if (!bundle.bar) {
            // Add the progress bar if it does not exist already
            bundle.bar = $('<div>').addClass('progressbar');
            bundle.egg = $('<div>').addClass('progress-egg');

            bundle.bar.append(bundle.egg);
            $(bundle.div).append($('<div>').addClass('rel-pos').append(bundle.bar));
        }

        if (info && info.total) {
            var progress = info.downloaded / info.total,
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

        $(bundle.div).find('.rel-pos').remove();
        $(bundle.div).find('button.download-icon').addClass('checked');
    }

    /**
     * Adds a package from a dropped file and immediately downloads it.
     * @param {Blob} file a dropped File or a Blob that contains an archive
     */
    dropPackage(file) {
        this.expand();
        this.addBundleZip(undefined, file).then(pkg => {
            this.bundles[pkg.name].div.scrollIntoViewIfNeeded();
            this.loadPkg(pkg.name);
        })
        .catch(err => { alert(`${file.name}: ${err}`); });
    }

    _packageByURL(url) {
        var s = url.toString();
        for (let pkg of this.packages) {
            if (pkg.archive && s == pkg.archive.url) return pkg.name;
        }
    }

    coqLibProgress(evt) {
        var url = new URL(evt.uri, new URL(this.coq._worker_script)),
            pkg_name = this._packageByURL(url);

        if (pkg_name) {
            if (evt.done) {
                this.onBundleLoad(pkg_name);
            }
            else {
                this.showPackageProgress(pkg_name, evt.download);
            }
        }
    }

    onBundleStart(bname) {
        this.showPackageProgress(bname);
    }

    onPkgProgress(evt) {
        var info = this.getPackage(evt.bundle).info;
        ++info.loaded; // this is not actually the number of files loaded :\

        this.showPackageProgress(evt.bundle, info);
    }

    onBundleLoad(bname) {
        this.loaded_pkgs.push(bname);

        var pkg =  this.getPackage(bname);
        if (pkg._resolve) pkg._resolve();
        else pkg.promise = Promise.resolve();

        this.showPackageCompleted(bname);
    }

    /**
     * Loads a package from the preconfigured path.
     * @param {string} pkg_name name of package (e.g., 'init', 'mathcomp')
     */
    loadPkg(pkg_name) {
        var pkg = this.getPackage(pkg_name);

        if (pkg.promise) return pkg.promise;  /* load issued already */

        var pre = this.loadDeps(pkg.info.deps || []),
            load = new Promise((resolve, reject) => {
                       pkg._resolve = resolve 
                       this.coq.loadPkg(pkg.getDownloadURL());
                   });

        pkg.promise = Promise.all([pre, load]);
        return pkg.promise;
    }

    async loadDeps(deps) {
        await this.waitFor(deps);
        return Promise.all(
            deps.map(pkg => this.loadPkg(pkg)));
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
        this.panel.parentNode.classList.add('collapsed');
    }

    expand() {
        this.panel.parentNode.classList.remove('collapsed');
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

    constructor() {
        this.moduleIndex = new Map();
    }

    add(pkgInfo) {
        for (let mod in pkgInfo.modules || {})
            this.moduleIndex.set(mod, pkgInfo);
    }

    *findModules(prefix, suffix, exact=false) {
        if (Array.isArray(prefix)) prefix = prefix.join('.');
        if (Array.isArray(suffix)) suffix = suffix.join('.');

        prefix = prefix ? prefix + '.' : '';
        if (exact) {
            if (this.moduleIndex.has(prefix + suffix)) yield prefix + suffix;
        }
        else {
            var dotsuffix = '.' + suffix;
            for (let k of this.moduleIndex.keys()) {
                if (k.startsWith(prefix) && (k == suffix || k.endsWith(dotsuffix)))
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
    constructor(name, base_uri) {
        this.name = name;
        this.base_uri = base_uri;

        this.info = undefined;
        this.archive = undefined;
    }

    getUrl(resource) {
        // Generate URL with the package's base_uri as the base
        return new URL(resource,
                  new URL(this.base_uri, PackageManager.scriptUrl));
    }

    getDownloadURL() {
        // @todo create blob url for dropped files
        return this.archive && this.archive.url.href;
    }

    async fetchInfo(resource = `${this.name}.json`) {
        var req = await fetch(this.getUrl(resource));
        return this.info = await req.json();
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
    constructor(resource) {
        if (resource instanceof URL)
            this.url = resource;
        else if (resource instanceof Blob)
            this.blob = resource;
        else if (resource.file /* JSZip-like */)
            this.zip = resource;
        else
            throw new Error(`invalid resource for archive: '${resource}'`);

        this.onProgress = () => {};
    }

    load() {
        return this.zip ? Promise.resolve(this) :
            this.download().then(data =>
                JSZip.loadAsync(data)).then(zip =>
                    { this.zip = zip; return this; });
    }

    download() {
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

// EG: This will be useful once we move file downloading to javascript.
// PackagesManager

class PackageDownloader {

    constructor(row, panel) {
        this.row = row;
        this.bar = null;
        this.egg = null;
        this.bundle_name = row.datum().desc;
        this.panel = panel;
        this.progress = 0; // percent
    }

    // This method setups the download handling.
    download() {

        // Allow re-download
        // this.row.select('img').on('click', null);

        this.bar = this.row.append('div')
            .attr('class', 'rel-pos')
            .append('div')
            .attr('class', 'progressbar');

        this.egg = this.bar
            .append('img')
            .attr('src', 'ui-images/egg.png')
            .attr('class', 'progress-egg');

        var files_total_length = 0;
        var files_loaded_cpt = 0;
        var pkgs = this.row.datum().pkgs;

        // Proceed to the main download.
        for(var i = 0; i < pkgs.length; i++)
            files_total_length += pkgs[i].no_files;

        document.body.addEventListener('pkgProgress',
            (evt) => {
                if(evt.detail.bundle_name === this.bundle_name) {
                    this.progress = ++files_loaded_cpt / files_total_length;
                    this.updateProgress();
                    if (files_loaded_cpt === files_total_length)
                        this.finishDownload();
                }
            }
        );

        jsCoq.add_pkg(this.bundle_name);

    }

    updateProgress() {
        var angle = (this.progress * 360 * 15) % 360;
        this.egg.style('transform', 'rotate(' + angle + 'deg)');
        this.bar.style('width', this.progress * 100 + '%');
    }

    finishDownload() {
        this.row.select('.rel-pos').remove();
        this.row.select('img')
            .attr('src', 'ui-images/checked.png');
    }
}


if (typeof document !== 'undefined' && document.currentScript)
    PackageManager.scriptUrl = new URL(document.currentScript.attributes.src.value, window.location);

if (typeof module !== 'undefined')
    module.exports = {CoqPkgArchive}

// Local Variables:
// js-indent-level: 4
// End:
