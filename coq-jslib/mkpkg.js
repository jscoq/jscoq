/**
 * Used to create a zip bundle out of a JSON files that
 * contains a list of .vo and .cmo filenames.
 */

const fs = require('fs'),
      path = require('path'),
      JSZip = require('jszip'),
      neatjson = require('neatjson');



class PackageDefinition {
    constructor(manifest, base_path, manifest_filename /*optional*/) {
        this.manifest = manifest;
        this.base_path = base_path;
        this.manifest_filename = manifest_filename;

        this.json_format_opts = 
            { padding: 1, afterColon: 1, afterComma: 1, wrap: 80 };

        this.zip_file_opts = 
            {date: new Date("1/1/2000 UTC"), // dummy date (otherwise, zip changes every time it is created...)
             createFolders: false};
    }

    static fromFile(manifest_filename, base_path /*optional*/) {
        var manifest = JSON.parse(fs.readFileSync(manifest_filename, 'utf-8'));
        return new PackageDefinition(manifest, 
            base_path || path.dirname(manifest_filename), manifest_filename);
    }

    listFiles() {
        var files = [];
        for (let pkg of this.manifest.pkgs) {
            for (let file_entry of (pkg.vo_files || []).concat(pkg.cma_files || [])) {
                files.push(path.join(...pkg.pkg_id, file_entry[0]));
                // include compiled .js counterpart of .cmo/.cma
                if (/[.]cm[ao]$/.exec(file_entry[0]))
                    files.push(path.join(...pkg.pkg_id, `${file_entry[0]}.js`));
            }
        }
        return files;
    }

    listModules() {
        var modules = [];
        for (let pkg of this.manifest.pkgs) {
            for (let file_entry of (pkg.vo_files || [])) {
                let modlabel = file_entry[0].replace(/[.](vo|cm[oa])$/, '');
                modules.push([...pkg.pkg_id, modlabel].join('.'));
            }
        }
        return modules;
    }

    toZip(save_as) {
        var z = new JSZip(), fopts = this.zip_file_opts;
        z.file("coq-pkg.json", this.toJSON(), fopts);
        for (let fn of this.listFiles()) {
            let phys = path.join(this.base_path, fn);
            if (/[.]cm[ao]$/.exec(fn))
                z.file(fn, '', fopts) // stub the actual objects; a bit ugly but saves space
            else
                z.file(fn, fs.createReadStream(phys)
                    .on("error", () => console.error(`error reading '${phys}'.`)), fopts);
        }
        if (save_as) {
            return new Promise((resolve, reject) =>
              z.generateNodeStream()
                .pipe(fs.createWriteStream(save_as))
                .on('finish', () => { console.log(`wrote '${save_as}'.`); resolve(z); }));
        }
        else
            return Promise.resolve(z);
    }

    toJSON() {
        return neatjson.neatJSON(this.manifest, this.json_format_opts);
    }

    writeManifest(to_file) {
        to_file = to_file || this.manifest_filename;

        if (!to_file)
            console.error("Cannot write package manifest back: filename not given.");
        else
            fs.writeFileSync(to_file, this.toJSON());
    }
}



module.exports = {PackageDefinition};


// Usage:
//  node mkpkg.js <json filenames...>
if (module.id == '.') {
    // Using promise chaining instead of async/await to support older Node.js
    process.argv.slice(2).map(json_fn => () => {
        let pd = PackageDefinition.fromFile(json_fn),
            zip_fn = json_fn.replace(/([.]json|)$/, '.coq-pkg');
        return pd.toZip(zip_fn).then(() => {
            pd.manifest.archive = path.basename(zip_fn);
            pd.writeManifest();
        });
    })
    .reduce((promise, action) => promise.then(action), Promise.resolve());
}
