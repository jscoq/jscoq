// Node app that import the file cache.js exporting a couple of arrays
// cache.md5 and cache.js and outputs a directory bcache/$MD5 containing
// the proper JS

var bc_md5 = require('../bc-md5.json');
var bc_js  = require('../bc-js.json');

var fs = require('fs');

for(var i = 0; i < bc_md5.length; i++) {
  fs.writeFile("coq-pkgs/bcache/" + bc_md5[i], bc_js[i],
               function(err) { });
}

for(var i = 0; i < bc_md5.length; i++) {
  process.stdout.write(bc_md5[i]);
  if (i + 1 < bc_md5.length)
    process.stdout.write("\n");
}
