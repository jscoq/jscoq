// Node app that import the file cache.js exporting a couple of arrays
// cache.md5 and cache.js and outputs a directory bcache/$MD5 containing
// the proper JS

var cache = require('./cache');

// In cache.js
/*

module.exports = {
  md5: [...],
  js : [...]
  }
};
*/

var fs = require('fs');

for(var i = 0; i < cache.md5.length; i++) {
  fs.writeFile("bcache/" + cache.md5[i], cache.js[i],
               function(err) { });
}

for(var i = 0; i < cache.md5.length; i++) {
  process.stdout.write(cache.md5[i] + "\n");
}
