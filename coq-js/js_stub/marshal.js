/**
 * A few overrides for Marshal and channel primitives which seem to be buggy
 * or inefficient in js_of_ocaml.
 * (we will report them and hopefully they will get fixed upstream.)
 */

//Provides: caml_output_val
//Requires: caml_int64_to_bytes, caml_failwith
//Requires: caml_int64_bits_of_float
//Requires: MlBytes, caml_ml_string_length, caml_string_unsafe_get
/**
 * This is a modified version of caml_output_val that correctly reflects
 * sharing, and as a result, avoids duplication and saves a lot of space.
 */
var caml_output_val = function (){
  function Writer () { this.chunk = []; }
  Writer.prototype = {
    chunk_idx:20, block_len:0, obj_counter:0, size_32:0, size_64:0,
    write:function (size, value) {
      for (var i = size - 8;i >= 0;i -= 8)
        this.chunk[this.chunk_idx++] = (value >> i) & 0xFF;
    },
    write_code:function (size, code, value) {
      this.chunk[this.chunk_idx++] = code;
      for (var i = size - 8;i >= 0;i -= 8)
        this.chunk[this.chunk_idx++] = (value >> i) & 0xFF;
    },
    write_shared:function (offset) {
      if (offset < (1 << 8)) this.write_code(8, 0x04 /*cst.CODE_SHARED8*/, offset);
      else if (offset < (1 << 16)) this.write_code(16, 0x05 /*cst.CODE_SHARED16*/, offset);
      else this.write_code(32, 0x06 /*cst.CODE_SHARED32*/, offset);
    },
    finalize:function () {
      this.block_len = this.chunk_idx - 20;
      this.chunk_idx = 0;
      this.write (32, 0x8495A6BE);
      this.write (32, this.block_len);
      this.write (32, this.obj_counter);
      this.write (32, this.size_32);
      this.write (32, this.size_64);
      return this.chunk;
    }
  }
  return function (v) {
    var writer = new Writer ();
    var stack = [];
    var intern_obj_table = [];
    
    function store(v) { intern_obj_table.push(v); writer.obj_counter = intern_obj_table.length; }
    function recall(v) {
        for (var i = 0; i < intern_obj_table.length; i++) {
            if (intern_obj_table[i] === v) return intern_obj_table.length - i;
        }
    }

    function memo(v) {
        var existing_offset = recall(v);
        if (existing_offset) { writer.write_shared(existing_offset); return existing_offset; }
        else store(v);
    }

    function extern_rec (v) {
      if (v instanceof Array && v[0] === (v[0]|0)) {
        if (v[0] == 255) {
          // Int64
          if (memo(v)) return;
          writer.write (8, 0x12 /*cst.CODE_CUSTOM*/);
          for (var i = 0; i < 3; i++) writer.write (8, "_j\0".charCodeAt(i));
          var b = caml_int64_to_bytes (v);
          for (var i = 0; i < 8; i++) writer.write (8, b[i]);
          writer.size_32 += 4;
          writer.size_64 += 3;
          return;
        }
        if (v[0] == 251) {
          caml_failwith("output_value: abstract value (Abstract)");
        }
        if (v.length > 1 && memo(v)) return;
        if (v[0] < 16 && v.length - 1 < 8)
          writer.write (8, 0x80 /*cst.PREFIX_SMALL_BLOCK*/ + v[0] + ((v.length - 1)<<4));
        else
          writer.write_code(32, 0x08 /*cst.CODE_BLOCK32*/, ((v.length-1) << 10) | v[0]);
        writer.size_32 += v.length;
        writer.size_64 += v.length;
        if (v.length > 1) stack.push (v, 1);
      } else if (v instanceof MlBytes) {
        if (memo(v)) return;
        var len = caml_ml_string_length(v);
        if (len < 0x20)
          writer.write (8, 0x20 /*cst.PREFIX_SMALL_STRING*/ + len);
        else if (len < 0x100)
          writer.write_code (8, 0x09/*cst.CODE_STRING8*/, len);
        else
          writer.write_code (32, 0x0A /*cst.CODE_STRING32*/, len);
        for (var i = 0;i < len;i++)
          writer.write (8, caml_string_unsafe_get(v,i));
        writer.size_32 += 1 + (((len + 4) / 4)|0);
        writer.size_64 += 1 + (((len + 8) / 8)|0);
      } else {
        if (v != (v|0)){
          var type_of_v = typeof v;
//
// If a float happens to be an integer it is serialized as an integer
// (Js_of_ocaml cannot tell whether the type of an integer number is
// float or integer.) This can result in unexpected crashes when
// unmarshalling using the standard runtime. It seems better to
// systematically fail on marshalling.
//
//          if(type_of_v != "number")
          caml_failwith("output_value: abstract value ("+type_of_v+")");
//          var t = caml_int64_to_bytes(caml_int64_bits_of_float(v));
//          writer.write (8, 0x0B /*cst.CODE_DOUBLE_BIG*/);
//          for(var i = 0; i<8; i++){writer.write(8,t[i])}
        }
        else if (v >= 0 && v < 0x40) {
          writer.write (8, 0X40 /*cst.PREFIX_SMALL_INT*/ + v);
        } else {
          if (v >= -(1 << 7) && v < (1 << 7))
            writer.write_code(8, 0x00 /*cst.CODE_INT8*/, v);
          else if (v >= -(1 << 15) && v < (1 << 15))
            writer.write_code(16, 0x01 /*cst.CODE_INT16*/, v);
          else
            writer.write_code(32, 0x02 /*cst.CODE_INT32*/, v);
        }
      }
    }
    extern_rec (v);
    while (stack.length > 0) {
      var i = stack.pop ();
      var v = stack.pop ();
      if (i + 1 < v.length) stack.push (v, i + 1);
      extern_rec (v[i]);
    }
    writer.finalize ();
    return writer.chunk;
  }
} ();


//Provides: caml_ml_pos_out
//Requires: caml_ml_channels, caml_ml_flush
function caml_ml_pos_out(chanid) {
  caml_ml_flush(chanid);    /* [offset] is not reliable in output streams until buffer is flushed */
  return caml_ml_channels[chanid].offset;
}

/*
   The following seem to suffer from the same problem, but we are not using
   them so it is hard to test.

//Provides: caml_ml_pos_out_64
//Requires: caml_int64_of_float, caml_ml_channels, caml_ml_flush
function caml_ml_pos_out_64(chanid) {
  caml_ml_flush(chanid);   
  return caml_int64_of_float (caml_ml_channels[chanid].offset);
}

//Provides: caml_ml_seek_out
//Requires: caml_ml_channels, caml_ml_flush
function caml_ml_seek_out(chanid,pos){
  caml_ml_channels[chanid].offset = pos;
  return 0;
}

//Provides: caml_ml_seek_out_64
//Requires: caml_int64_to_float, caml_ml_channels, caml_ml_flush
function caml_ml_seek_out_64(chanid,pos){
  caml_ml_flush(chanid);   
  caml_ml_channels[chanid].offset = caml_int64_to_float(pos);
  return 0;
}

*/