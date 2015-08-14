// String.prototype.hashCode = function() {
//   var hash = 0, i, chr, len;
//   if (this.length == 0) return hash;
//   for (i = 0, len = this.length; i < len; i++) {
//     chr   = this.charCodeAt(i);
//     hash  = ((hash << 5) - hash) + chr;
//     hash |= 0; // Convert to 32bit integer
//   }
//   return hash;
// };

// var codeHash = code.toString().hashCode();
// console.log("Requested reify code: " + codeHash);

//Provides: caml_reify_bytecode
//Requires: caml_failwith
function caml_reify_bytecode (code, _sz) {

  if(joo_global_object.digest && joo_global_object.lastCoqReq) {
    var md5 = joo_global_object.digest(code);
    console.log("Reify bytecode of {" + joo_global_object.lastCoqReq + "} [" + md5 + "/" + _sz + "]");
  } else {
    console.log("Reify bytecode called, no debug info");
  }

  if(joo_global_object.toplevelCompile)
    return joo_global_object.toplevelCompile(code);
  else caml_failwith("Toplevel not initialized (toplevelCompile)")
}

