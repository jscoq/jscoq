function unix_ll(s, args) { 
  if (unix_ll.log) console.warn(s, args); 
  if (unix_ll.trap) throw new Error("unix trap: '"+ s + "' not implemented");
}
unix_ll.log = true;       // whether to log calls
unix_ll.trap = false;     // whether to halt on calls

//Provides: unix_ll
var unix_ll;

//Provides: caml_raise_unix_error
//Requires: caml_named_value, caml_raise_with_arg, caml_new_string
function caml_raise_unix_error(msg) {
  var tag = caml_named_value("Unix.Unix_error");
  // var util = require('util');
  // console.log(util.inspect(chan, {showHidden: false, depth: null}));
  caml_raise_with_arg (tag, caml_new_string (msg));
}

//Provides: unix_access
//Requires: unix_ll
function unix_access() {
  unix_ll("unix_access", arguments);
  return 0;
}

//Provides: unix_alarm
//Requires: unix_ll
function unix_alarm() {
  unix_ll("unix_alarm", arguments);
  return 0;
}

//Provides: unix_bind
//Requires: unix_ll
function unix_bind() {
  unix_ll("unix_bind", arguments);
  return 0;
}

//Provides: unix_close
//Requires: unix_ll
function unix_close() {
  unix_ll("unix_close", arguments);
  return 0;
}

//Provides: unix_connect
//Requires: unix_ll
function unix_connect() {
  unix_ll("unix_connect", arguments);
  return 0;
}

//Provides: unix_dup
//Requires: unix_ll
function unix_dup() {
  unix_ll("unix_dup", arguments);
  return 0;
}

//Provides: unix_dup2
//Requires: unix_ll
function unix_dup2() {
  unix_ll("unix_dup2", arguments);
  return 0;
}

//Provides: unix_environment
//Requires: unix_ll
function unix_environment() {
  unix_ll("unix_environment", arguments);
  return 0;
}

//Provides: unix_error_message
//Requires: unix_ll
function unix_error_message() {
  unix_ll("unix_error_message", arguments);
  return 0;
}

//Provides: unix_execve
//Requires: unix_ll
function unix_execve() {
  unix_ll("unix_execve", arguments);
  return 0;
}

//Provides: unix_execvp
//Requires: unix_ll
function unix_execvp() {
  unix_ll("unix_execvp", arguments);
  return 0;
}

//Provides: unix_execvpe
//Requires: unix_ll
function unix_execvpe() {
  unix_ll("unix_execvpe", arguments);
  return 0;
}

//Provides: unix_getcwd
//Requires: unix_ll
function unix_getcwd() {
  unix_ll("unix_getcwd", arguments);
  return 0;
}

//Provides: unix_fork
//Requires: unix_ll
function unix_fork() {
  unix_ll("unix_fork", arguments);
  return 0;
}

//Provides: unix_getpid
//Requires: unix_ll
function unix_getpid() {
  unix_ll("unix_getpid", arguments);
  return 0;
}

//Provides: unix_getpwnam
//Requires: unix_ll
function unix_getpwnam() {
  unix_ll("unix_getpwnam", arguments);
  return 0;
}

//Provides: unix_getsockname
//Requires: unix_ll
function unix_getsockname() {
  unix_ll("unix_getsockname", arguments);
  return 0;
}

//Provides: unix_isatty
//Requires: unix_ll
function unix_isatty() {
  unix_ll("unix_isatty", arguments);
  return 0;
}

//Provides: unix_kill
//Requires: unix_ll
function unix_kill() {
  unix_ll("unix_kill", arguments);
  return 0;
}

//Provides: unix_listen
//Requires: unix_ll
function unix_listen() {
  unix_ll("unix_listen", arguments);
  return 0;
}

//Provides: unix_mkdir
//Requires: unix_ll
function unix_mkdir() {
  unix_ll("unix_mkdir", arguments);
  return 0;
}
//Provides: unix_pipe
//Requires: unix_ll
function unix_pipe() {
  unix_ll("unix_pipe", arguments);
  return 0;
}

//Provides: unix_read
//Requires: unix_ll
function unix_read() {
  unix_ll("unix_read", arguments);
  return 0;
}

//Provides: unix_opendir
//Requires: unix_ll
function unix_opendir(dir) {
  unix_ll("unix_opendir", arguments);

  // caml_raise_unix_error("opendir", arguments);
  return [];
}

//Provides: unix_readdir
//Requires: unix_ll, caml_raise_constant, caml_global_data
function unix_readdir(dir) {
  unix_ll("unix_readdir", arguments);

  // caml_raise_unix_error("readdir", arguments);
  caml_raise_constant(caml_global_data.End_of_file);
  return [];
}

//Provides: unix_closedir
//Requires: unix_ll
function unix_closedir() {
  unix_ll("unix_closedir", arguments);
  return [];
}

//Provides: unix_select
//Requires: unix_ll
function unix_select() {
  unix_ll("unix_select", arguments);
  return 0;
}

//Provides: unix_set_close_on_exec
//Requires: unix_ll
function unix_set_close_on_exec() {
  unix_ll("unix_set_close_on_exec", arguments);
  return 0;
}

//Provides: unix_set_nonblock
//Requires: unix_ll
function unix_set_nonblock() {
  unix_ll("unix_set_nonblock", arguments);
  return 0;
}

//Provides: unix_sleep
//Requires: unix_ll
function unix_sleep() {
  unix_ll("unix_sleep", arguments);
  return 0;
}

//Provides: unix_socket
//Requires: unix_ll
function unix_socket() {
  unix_ll("unix_socket", arguments);
  return 0;
}

//Provides: unix_string_of_inet_addr
//Requires: unix_ll
function unix_string_of_inet_addr() {
  unix_ll("unix_string_of_inet_addr", arguments);
  return 0;
}

//Provides: unix_times
//Requires: unix_ll
function unix_times() {
  unix_ll("unix_times", arguments);
  return 0;
}

//Provides: unix_wait
//Requires: unix_ll
function unix_wait() {
  unix_ll("unix_wait", arguments);
  return 0;
}

//Provides: unix_waitpid
//Requires: unix_ll
function unix_waitpid() {
  unix_ll("unix_waitpid", arguments);
  return 0;
}

//Provides: unix_stat
//Requires: unix_ll
function unix_stat() {
  unix_ll("unix_stat", arguments);
  return 0;
}