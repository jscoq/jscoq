const assert = require('assert'),
      fs = require('fs'),
      glob = require('glob'),
      child_process = require('child_process');

const cliJsPath = locateCliJs();

function locateCliJs() {
    var alts = glob.sync('_build/jscoq+*/cli.js');
    if (alts.length == 0) throw new Error('coq-cli.js not found');
    else if (alts.length > 1) throw new Error('multiple builds found: ' + alts);
    return alts[0];
}

function cliSubprocessSync(flags) {
    return child_process.spawnSync('node', [cliJsPath, ...flags],
        {encoding: 'utf-8'});
}

describe('qa0 - sanity test', function() {
    this.timeout(10000); 

    describe('nonzeros', function() {
        var rc = cliSubprocessSync(['run', '-l', 'tests/qa0/nonzeros.v']);
        it('should run without error', function() {
            assert.strictEqual(rc.status, 0);
            assert.strictEqual(rc.stderr, "");
        });
        it('should produce correct output', function() {
            var expected = fs.readFileSync('tests/qa0/nonzeros.out', 'utf-8');
            assert.strictEqual(rc.stdout, expected);
        });
    });

    describe('timeout', function() {
        var rc = cliSubprocessSync(['run', '-l', 'tests/qa0/timeout.v']);
        it('should report a timeout', function() {
            var expected = fs.readFileSync('tests/qa0/timeout.out', 'utf-8');
            assert.strictEqual(rc.stdout, expected);
        });
    });
});