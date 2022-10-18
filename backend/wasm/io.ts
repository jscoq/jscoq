import { unzipSync } from 'fflate';

export type FetchMode = 'browser' | 'fs';

export class IO {

    pending = new Set<ReadableStreamDefaultReader<Uint8Array>>()

    constructor(public fetchMode: FetchMode) { }

    async unzip(uri: string, put: (filename: string, content: Uint8Array) => void, progress?: (p: any) => void) {
        var zip = unzipSync(await this._fetch(uri, progress));

        for (let [filename, data] of Object.entries(zip)) {
            if (data.length > 0)  /* regular file; assumes no empty files? */
                put(filename, data);
        }
    }

    async _fetch(uri: string, progress?: (p: any) => void) : Promise<Uint8Array> {
        if (progress && this.fetchMode === 'browser') {
            return this._toU8A(this._fetchWithProgress(uri, progress));
        }
        else return this._fetchSimple(uri);
    }

    async _toU8A(blob: Promise<Blob>) {
        return new Uint8Array(await (await blob).arrayBuffer());
    }

    async _fetchSimple(uri: string) {
        switch (this.fetchMode) {
        case 'browser':
            return new Uint8Array(await (await fetch(uri)).arrayBuffer());
        case 'fs':
            const fs = require('fs');
            return (0||fs.readFileSync)(uri);
        }
    }

    // boilerplate
    async _fetchWithProgress(uri: string, progress: (p: any) => void) {
        var response = await fetch(uri),
            total = +response.headers.get('Content-Length') || 1000,
            r = response.body.getReader(), chunks = [], downloaded = 0;
        this.pending.add(r); // prevent reader from being disposed
        try {
            for(;;) {
                var {value, done} = await r.read();
                if (done) break;
                chunks.push(value);
                downloaded += value.length;
                progress({total, downloaded})
            }
            return new Blob(chunks);
        }
        finally { this.pending.delete(r); }
    }
}


