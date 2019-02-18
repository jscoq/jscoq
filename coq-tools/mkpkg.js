/**
 * Used to create a zip bundle out of a JSON files that
 * contains a list of .vo and .cmo filenames.
 */

const fs = require('fs'),
      path = require('path'),
      JSZip = require('jszip');

class PackageDefinition {
    constructor(manifest, base_path) {
        if (typeof manifest == 'string') {
            this.manifest = JSON.parse(fs.readFileSync(manifest, 'utf-8'));
            this.base_path = base_path || path.dirname(manifest);
        }
        else {
            this.manifest = manifest;
            this.base_path = base_path; // a required argument in this case
        }
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

    toZip(save_as) {
        var z = new JSZip();
        z.file("coq-pkg.json", JSON.stringify(this.manifest, null, 2));
        for (let fn of this.listFiles()) {
            let phys = path.join(this.base_path, fn);
            if (/[.]cm[ao]$/.exec(fn))
                z.file(fn, '') // stub the actual objects; a bit ugly but saves space
            else
                z.file(fn, fs.createReadStream(phys)
                    .on("error", () => console.error(`error reading '${phys}'.`)));
        }
        if (save_as) {
            return z.generateNodeStream()
                .pipe(fs.createWriteStream(save_as))
                .on('finish', () => console.log(`wrote '${save_as}'.`));
        }
        else
            return z;
    }
}

// Usage:
//  node mkpkg.js <json filenames...>
if (module.id == '.') {
    for (let json_fn of process.argv.slice(2)) {
        var pd = new PackageDefinition(json_fn),
            zip_fn = json_fn.replace(/([.]json|)$/, '.coq-pkg');
        pd.toZip(zip_fn);
    }
}