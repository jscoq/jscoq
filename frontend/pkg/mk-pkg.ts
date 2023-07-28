#!/usr/bin/env node

import commander from 'commander';
import manifest from '../../package.json';

import { Driver, BuildError, Opts } from './driver';

async function main() {

    var rc = 0;

    var prog = commander
        .name('jscoq')
        .version(manifest.version);
    prog.command('build', {isDefault: true})
        .option('--rootdir <dir>',            'toplevel directory for finding `.v` and `.vo` files')
        .option('--nostdlib',                 'skip loading the standard Coq packages')
        .action(async opts => { rc = await build(opts); });

    await prog.parseAsync(process.argv);
    return rc;
}

async function build(opts: Opts) {

    if (opts.args.length > 0) {
        if (!opts.workspace && opts.args[0].endsWith('.json'))
            opts.workspace = opts.args.shift();
        else if (!opts.rootdir) {
            console.error('--rootdir is mandatory');
            return 1;
        } if (opts.args.length > 0) {
            console.error('extraneous arguments: ', opts.args);
            return 1;
        }
    }

    var cli = new Driver(opts);

    try {
        await cli.prepare();
        await cli.package();

        return cli.errors ? 1 : 0;
    }
    catch (e) {
        if (e instanceof BuildError) return 1;
        else throw e;
    }
}

main().then(rc => process.exit(rc || 0));
