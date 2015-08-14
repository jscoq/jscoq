//Provides: caml_sys_file_exists
//Requires: caml_root_dir, caml_make_path
function caml_sys_file_exists (name) {
  console.log("Sys.file_exists: " + name);
  var dir = caml_root_dir;
  var path = caml_make_path(name);
  var auto_load;
  var pos;
  for(var i=0;i<path.length;i++){
    if(dir.auto) { auto_load = dir.auto; pos = i}
    if(!(dir.exists && dir.exists(path[i]))) {
      if(auto_load) {
        console.log(auto_load);
        console.log(JSON.stringify(auto_load));

        var res = auto_load(path, pos);
        console.log("Sys.file_exists: returning auto load ");
        console.log(res);
        console.log(JSON.stringify(res));

        return true;
      }
      else
      {
        console.log("Sys.file_exists: returning 0");
        return 0;
      }
    }
    dir=dir.get(path[i]);
  }
  console.log("Sys.file_exists: returning 1");
  return 1;
}
