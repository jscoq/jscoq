import fs from 'fs';
import path from 'path';
import os from 'os';
import child_process from 'child_process';
import { existsExec, cat, cas, ln_sf, dirstamp } from './shutil.ts';
import * as sdk from './setup.ts';

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
            if (existsExec(full)) return full;
        }
        throw new Error(`${progname}: not found`);
    }

    _exec(prog, args, stdio='inherit') {
        if (SDK_FLAGS.includes('verbose')) {
            log(`[${ME}-sdk]  ${prog} ${args.join(' ')}`);
        }
        return child_process.execFileSync(prog, args, {stdio});
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
        fs.mkdirSync(bindir, {recursive: true});
        for (let tool of this.progs) {
            ln_sf(script, path.join(bindir, tool));
        }
        process.env['PATH'] = `${bindir}:${process.env['PATH']}`;
    }
}

class DockerTool extends Phase {

    dockerImage = `${ME}:sdk`
    dockerVolume = {name: 'jscoq-sdk', mnt: '/opt/jscoq-sdk'}
    incdir = '/opt/jscoq/lib/coq-core';  /* points to Docker image */

    async run(prog, args) {
        const cfg = await sdk.setup(this.basedir, false);
        cfg.include = this.incdir;
        await this.copyToVolume(cfg);
        this.runInContainer(prog, args, cfg);
    }

    mounts(cfg) {
        var cwd = process.cwd(),
            mnt = cwd.match(/^[/][^/]+/)?.[0],
            coqlib = cfg.coqlib,
            vol = this.dockerVolume;
    
        if (!mnt)
            console.warn(`[${ME}-sdk] cannot detect working directory root for '${cwd}';\n` +
                         `            this will probably not work.`)
        if (mnt.match(/^[/](Users|home)$/))
            mnt = cwd.match(/^[/][^/]+[/][^/]+/)?.[0] ?? mnt; /* this is highly heuristic */
    
        if (coqlib?.startsWith('/opt')) coqlib = undefined;

        return [...[mnt, coqlib].filter(x => x).map(d => `-v${d}:${d}`),
                `-v${vol.name}:${vol.mnt}`];
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
    
    async copyToVolume(cfg) {
        let {name, mnt} = this.dockerVolume,
            stamp = cat(path.join(cfg.coqlib, '_coq-pkgs')) ?? dirstamp(cfg.coqlib);
        await cas(path.join(cfg.coqlib, '_volume'), stamp, () => {
            if (SDK_FLAGS.includes('verbose'))
                log(`[${ME}-sdk] creating volume ${name}`);
            this._exec('docker',  ['volume', 'rm', '-f', name], ['ignore', 'ignore', 'inherit']);
            this._exec('docker',  ['volume', 'create', name], ['ignore', 'ignore', 'inherit']);
            this.runInContainer('sudo', ['cp', '-rf', cfg.coqlib, mnt], cfg);
        });
        cfg.coqlib = path.join(mnt, path.basename(cfg.coqlib));
    }

    runInContainer(prog, args, cfg={}) {
        this._exec('docker', [
            'run', ...this.mounts(cfg), ...this.user(), ...this.env(cfg),
            `-w${process.cwd()}`, '--rm', this.dockerImage,
            prog, ...args
        ]);
    }
}

/** logs to stderr to avoid cluttering output, esp. for coqdep */
function log(msg) {
    process.stderr.write(msg + '\n');
}


async function main(prog, args) {
    var Phase = {
            'coqc': DockerTool, 'coqdep': DockerTool, 'coqtop': DockerTool
        }[prog] ?? Hijack;

    try {
        await new Phase().run(prog, args);
    }
    catch (e) {
        if (typeof e.status === 'number') process.exit(e.status);
        console.error(`[${ME}-sdk]`, e.err ?? e);
        process.exit(1);
    }
}

function installCommand(commander/*: commander.CommanderStatic*/) {
    commander.command('sdk')
        .description("Runs a shell command with `coqc` redirected to jsCoq SDK.")
        .allowUnknownOption(true)
        .action(async opts => { await main('sdk', opts.args); });
}


export { main, installCommand }
