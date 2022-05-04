import fs from 'fs';


function cat(fn: string) {
    try {
        return fs.readFileSync(fn, 'utf-8');
    }
    catch { return undefined; }
}

/**
 * If `fn` contains `expectedValue`, do nothing;
 * Otherwise run `whenNeq` and update `fn`.
 * @returns `true` iff `fn` already contained `expectedValue`.
 */
async function cas(fn: string, expectedValue: string, whenNeq: () => void | Promise<void>) {
    if (cat(fn) === expectedValue) return true;
    else {
        await whenNeq();
        fs.writeFileSync(fn, expectedValue);
        return false;
    }
}

function dirstamp(fn: string) {
    try { var s = fs.statSync(fn).mtime.toISOString(); } catch { s = '??'; }
    return `${fn} @ ${s}`;
}

function ln_sf(target: string, source: string) {
    try { fs.unlinkSync(source); }
    catch { }
    fs.symlinkSync(target, source);
}

function existsExec(p) {
    try {
        let stat = fs.statSync(p);
        return stat && stat.isFile() && (stat.mode & fs.constants.S_IXUSR);
    }
    catch (e) { return false; }
}

function existsDir(p) {
    try {
        let stat = fs.statSync(p);
        return stat && stat.isDirectory();
    }
    catch (e) { return false; }        
}

export { cat, cas, dirstamp, ln_sf, existsExec, existsDir }