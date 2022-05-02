
const fs = require('fs'), path = require('path'), os = require('os'),
      child_process = require('child_process'),
      sdk = require('./sdk');

const ME = 'jscoq',
      SDK_FLAGS = (process.env['JSCOQ'] || '').split(',').filter(x => x);


class Phase {

    constructor(basedir='/tmp/jscoq-sdk') {
        this.basedir = basedir;
    }

    which(progname, skipSelf=false) {
        if (progname.indexOf('/') >= 0) return progname;

        for (let pe of process.env['PATH'].split(':')) {
            if (skipSelf && pe.startsWith(this.basedir)) continue;
            var full = path.join(pe, progname);
            if (this.existsExec(full)) return full;
        }
        throw new Error(`${progname}: not found`);
    }
    
    _exec(prog, args) {
        if (SDK_FLAGS.includes('verbose')) {
            console.log(`[${ME}-sdk]  `, prog, args.join(' '));
        }
        return child_process.execFileSync(prog, args, {stdio: 'inherit'});
    }
}

class Hijack extends Phase {

    progs = ['coqc', 'coqdep', 'coqtop']

    run(prog, args) {
        this.mkBin();
        if (args.length > 0)
            this._exec(this.which(args[0]), args.slice(1));
    }

    mkBin(bindir=path.join(this.basedir, 'hijack'), script=__filename) {
        if (!fs.existsSync(bindir)) {
            fs.mkdirSync(bindir, {recursive: true});
            for (let tool of this.progs) {
                fs.symlinkSync(script, path.join(bindir, tool));
            }
        }
        process.env['PATH'] = `${bindir}:${process.env['PATH']}`;
    }

    existsExec(p) {
        try {
            let stat = fs.statSync(p);
            return stat && stat.isFile() && (stat.mode & fs.constants.S_IXUSR);
        }
        catch (e) { return false; }
    }

    existsDir(p) {
        try {
            let stat = fs.statSync(p);
            return stat && stat.isDirectory();
        }
        catch (e) { return false; }        
    }
}

class DockerTool extends Phase {
    dockerImage = `${ME}:sdk`
    incdir = '/opt/jscoq/lib/coq-core';  /* points to Docker image */

    async run(prog, args) {
        const cfg = await sdk.sdk(this.basedir, false);
        cfg.include = this.incdir;
        this.runInContainer(prog, args, cfg);
    }

    mounts(cfg) {
        var cwd = process.cwd(),
            mnt = cwd.match(/[/][^/]+/)[0],
            coqlib = cfg.coqlib;
    
        if (!mnt)
            console.warn(`[${ME}-sdk] cannot detect working directory root for '${cwd}';\n` +
                         `            this will probably not work.`)
    
        return [mnt, coqlib].filter(x => x).map(d => `-v${d}:${d}`);
    }
    
    user() {
        if (os.platform() === 'darwin') return [];  // seems to not work in macOS, and also unneeded
        else {
            var {uid, gid} = os.userInfo();
            return ['-e', `LOCAL_USER_ID=${uid}`, '-e', `LOCAL_GROUP_ID=${gid}`];
        }
    }
    
    env(cfg) {
        var e = {COQLIB: cfg.coqlib, COQCORELIB: cfg.include};
        return [].concat(...Object.entries(e).map(
            ([k, v]) => v ? ['-e', `${k}=${v}`] : []));
    }
    
    runInContainer(prog, args, cfg={}) {
        this._exec('docker', [
            'run', ...this.mounts(cfg), ...this.user(), ...this.env(cfg),
            `-w${process.cwd()}`, '--rm', this.dockerImage,
            prog, ...args
        ]);
    }
}


async function main() {
    var prog = path.basename(process.argv[1]),
        args = process.argv.slice(2);

    var Phase = {
            'coqc': DockerTool, 'coqdep': DockerTool, 'coqtop': DockerTool
        }[prog] ?? Hijack;

    try {
        await new Phase().run(prog, args);
    }
    catch (e) {
        if (typeof e.status === 'number') process.exit(e.status);
        console.error(`[${ME}-sdk]`, e);
        process.exit(1);
    }
}

main(); 