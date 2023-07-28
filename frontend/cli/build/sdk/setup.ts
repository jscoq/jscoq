// UNTIL THIS IS MERGED INTO THE CLI:
//   tsc --allowSyntheticDefaultImports --esModuleInterop bin/sdk.ts
import path from 'path';
import mkdirp from 'mkdirp';
import findUp from 'find-up';
import glob from 'glob';
// There is some esbuild issue with this package
import unzip from 'fflate-unzip/src/index';
import chld from 'child-process-promise';
import type commander from 'commander';
import { cas, dirstamp, ln_sf, existsDir } from './shutil';


const ME = 'jscoq',
      SDK = `/tmp/${ME}-sdk`,
      SDK_FLAGS = (process.env['JSCOQ'] || '').split(',').filter(x => x);

const DEFAULT_PKGS_LOCATION = ['jscoq/coq-pkgs', 'wacoq-bin/bin/coq']


async function setup(basedir = SDK, includeNative = true) {
    mkdirp.sync(basedir);

    // Locate `coq-pkgs`
    var flag = SDK_FLAGS.map(s => s.match(/^coq-pkgs=(.*)$/)?.[1]).filter(x => x),
        nm = findNM(),
        coqpkgsDir: string;
    for (let sp of flag.concat(DEFAULT_PKGS_LOCATION)) {
        if (existsDir(sp)) { coqpkgsDir = sp; break; }
        var fp = path.join(nm, sp);
        if (existsDir(fp)) { coqpkgsDir = fp; break; }
    }
    if (!coqpkgsDir) throw {err: "Package bundles (*.coq-pkg) not found"};

    // - unzip everything in `coqlib`
    var coqlibDir = path.join(basedir, 'coqlib');
    mkdirp.sync(coqlibDir);
    await cas(path.join(coqlibDir, '_coq-pkgs'), dirstamp(coqpkgsDir), async () => {
        for (let fn of glob.sync('*.coq-pkg', {cwd: coqpkgsDir})) {
            var fp = path.join(coqpkgsDir, fn);
            await unzip(fp, coqlibDir);
        }

        // - link `theories` and `plugins` to be consistent with Coq dist structure
        for (let link of ['theories', 'plugins'])
            ln_sf('Coq', path.join(coqlibDir, link));
    });

    // Locate native Coq
    if (includeNative) {
        var coqlibNative = await findCoq();

        // - link libs in `ml`
        var mlDir = path.join(basedir, 'ml');
        mkdirp.sync(mlDir);
        await cas(path.join(mlDir, '_coqlib-native'), dirstamp(coqlibNative), () => {
            for (let fn of glob.sync('**/*.cmxs', {cwd: coqlibNative}))
                ln_sf(
                    path.join(coqlibNative, fn),
                    path.join(mlDir, path.basename(fn)));
        });
    }
    else mlDir = undefined;

    return {coqlib: coqlibDir, include: mlDir};
}

async function runCoqC(cfg: {coqlib: string, include: string},
                       args: string[]) {
    var {coqlib, include} = cfg,
        args = ['-coqlib', coqlib, '-include', include, ...args];
    try {
        return await chld.spawn('coqc', args, {stdio: 'inherit'});
    }
    catch { throw {err: 'coqc error'}; }
}

/*- specific helpers -*/

function findNM() {
    var nm = findUp.sync('node_modules', {type: 'directory'});
    if (!nm) throw {err: "node_modules directory not found"};
    return nm;
}

async function findCoq() {
    var cfg = await chld.exec("coqc -config"),
        mo = cfg.stdout.match(/^COQCORELIB=(.*)/m);
    if (!mo) throw {err: "Coq config COQCORELIB=_ not found"};
    return mo[1];
}

/*- main entry point -*/

async function main(args: string[]) {
    try {
        var cfg = await setup();
        var ret = await runCoqC(cfg, args);
        return ret.code;
    }
    catch (e) {
        if (e.err) console.log('oops: ' + e.err);
        else console.error(e);
        return 1;
    }
}

function installCommand(commander: commander.CommanderStatic) {
    commander.command('coqc')
        .description("Runs `coqc` with waCoq's standard library.")
        .allowUnknownOption(true)
        .helpOption('-z', '(run `wacoq coqc -help` instead)')
        .action(async opts => { await main(opts.args); });
}


export { main, setup, installCommand }
