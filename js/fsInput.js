var util = require('util');
var fs   = require('fs');
var bfs = new Buffer(100);

//Requires: caml_raise_end_of_file, caml_string_get, caml_ml_string_length
//Provides: caml_ml_input_char
function caml_ml_input_char(chan) {

  // process.stdin.setEncoding('utf8');
  // console.log(util.inspect(chan, {showHidden: false, depth: null}));

  if (chan.file.data.l <= chan.offset) {
    // console.log("trigger\n");
    chan.file.data.l = fs.readSync(0, bfs, 0, 100, null);
    bfs[chan.file.data.l] = 0;
    chan.file.data.c = bfs.toString();
    chan.offset = 0;
  }

  // console.log(util.inspect(chan, {showHidden: false, depth: null}));
  if (chan.offset >= caml_ml_string_length(chan.file.data))
    caml_raise_end_of_file();
  var c = caml_string_get(chan.file.data, chan.offset);
  chan.offset++;
  return c;
}
