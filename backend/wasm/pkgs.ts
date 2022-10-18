import { IO } from './io';

type DownloadProgress = { total: number, downloaded: number };

export class PackageManager {

    emit : (event: string, args: any) => any;
    answer : (msgs: any) => any;
    putFile : (name: any, contents: any) => any;
    io : IO;
    binDir : string;

    constructor(emit, answer, putFile, io, binDir) {
        this.emit = emit;
        this.answer = answer;
        this.putFile = putFile;
        this.io = io;
        this.binDir = binDir;
    }

    loadPackage(uri: string, refresh: boolean = true) {
        return this.loadPackages([uri], refresh);
    }

    async loadPackages(uris: string | string[], refresh: boolean = true) {
        if (typeof uris == 'string') uris = [uris];

        await Promise.all(uris.map(async uri => {
            try {
                await this.unzip(uri, '/lib');
                this.answer([['LibLoaded', uri]]);
            }
            catch (e) {
                this.answer([['LibError', uri, e.toString()]]);
                throw e;
            }
        }));

        //if (refresh)
        //    this.command(['RefreshLoadPath']);

        this.answer([['LoadedPkg', uris]]);
    }

    unzip(uri: string, dir: string) {
        return this.io.unzip(this._pkgUri(uri),
                    (fn, ui8a) => this.putFile(`${dir}/${fn}`, ui8a),
                    p => this._progress(uri, p));
    }

    async loadSources(uri: string, dirpath: string) {
        var subdir = dirpath.replace(/[.]|([^/])$/g, '$1/');
        this.unzip(uri, `/src/${subdir}`);
    }

    async findlibStartup() {
        this.putFile('/lib/findlib.conf', `path="/lib/ocaml"`);

        // await this.unzip('/scratch/lib.zip', '/lib/ocaml');
    }

    _pkgUri(uri: string) {
        return (uri[0] == '+') ?
            `${this.binDir}/coq/${uri.substring(1)}.coq-pkg` : uri;
    }

    _progress(uri: string, download: DownloadProgress) {
        this.emit('progress', {uri, download});
    }

}
