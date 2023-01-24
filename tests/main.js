import * as assert from 'assert';
import * as fs from 'fs';
import * as child_process from 'child_process';
import * as util from 'util';
import pkg from 'glob';
const { glob } = pkg;

const cliJsPath = locateCliJs();

function locateCliJs() {
    var alts = glob.sync('_build/jscoq+*/dist-cli/cli.cjs');
    if (alts.length == 0) throw new Error('cli.cjs not found');
    else if (alts.length > 1) throw new Error('multiple builds found: ' + alts);
    return alts[0];
}

function cliSubprocess(flags) {
    return util.promisify(child_process.execFile)('node', [cliJsPath, ...flags],
        {encoding: 'utf-8'});
}

describe('qa0 - sanity test', function() {
    this.timeout(10000);

    describe('nonzeros', function() {
        var rc;
        it('should run without error', async function() {
            rc = await cliSubprocess(['run', '-l', 'tests/qa0/nonzeros.v']);
            assert.strictEqual(rc.stderr, "");
        });
        it('should produce correct output', function() {
            var expected = fs.readFileSync('tests/qa0/nonzeros.out', 'utf-8');
            assert.strictEqual(rc.stdout, expected);
        });
    });

    describe('timeout', function() {
        it('should report a timeout', async function() {
            try {
                await cliSubprocess(['run', '-l', 'tests/qa0/timeout.v']);
            }
            catch (rc) {
                var expected = fs.readFileSync('tests/qa0/timeout.out', 'utf-8');
                assert.strictEqual(rc.stdout, expected);
                return;
            }
            throw new Error('terminated without error');
        });
    });

    describe('options', function() {
        it('should read default option value', async function() {
            var rc = await cliSubprocess(['run', '-e', "Test Silent."]);
            var expected = fs.readFileSync('tests/qa0/options-0.out', 'utf-8');
            assert.strictEqual(rc.stdout, expected);
        });
    });
});
