var v_log = true;   // Whether to log
function ll(s) { if (v_log) console.warn(s); }

function caml_raise_unix_error(msg) {
  var tag = caml_named_value("Unix.Unix_error");
  // var util = require('util');
  // console.log(util.inspect(chan, {showHidden: false, depth: null}));
  caml_raise_with_arg (tag, caml_new_string (msg));
}

//Provides: unix_access
function unix_access() {
  // ll("unix_access");
  return 0;
}

//Provides: unix_alarm
function unix_alarm() {
  // ll("unix_alarm");
  return 0;
}

//Provides: unix_bind
function unix_bind() {
  // ll("unix_bind");
  return 0;
}

//Provides: unix_close
function unix_close() {
  // ll("unix_close");
  return 0;
}

//Provides: unix_connect
function unix_connect() {
  // ll("unix_connect");
  return 0;
}

//Provides: unix_dup
function unix_dup() {
  // ll("unix_dup");
  return 0;
}

//Provides: unix_dup2
function unix_dup2() {
  // ll("unix_dup2");
  return 0;
}

//Provides: unix_environment
function unix_environment() {
  // ll("unix_environment");
  return 0;
}

//Provides: unix_error_message
function unix_error_message() {
  // ll("unix_error_message");
  return 0;
}

//Provides: unix_execve
function unix_execve() {
  // ll("unix_execve");
  return 0;
}

//Provides: unix_execvp
function unix_execvp() {
  // ll("unix_execvp");
  return 0;
}

//Provides: unix_execvpe
function unix_execvpe() {
  // ll("unix_execvpe");
  return 0;
}

//Provides: unix_getcwd
function unix_getcwd() {
  // ll("unix_getcwd");
  return 0;
}

//Provides: unix_fork
function unix_fork() {
  // ll("unix_fork");
  return 0;
}

//Provides: unix_getpid
function unix_getpid() {
  // ll("unix_getpid");
  return 0;
}

//Provides: unix_getpwnam
function unix_getpwnam() {
  // ll("unix_getpwnam");
  return 0;
}

//Provides: unix_getsockname
function unix_getsockname() {
  // ll("unix_getsockname");
  return 0;
}

//Provides: unix_isatty
function unix_isatty() {
  // ll("unix_isatty");
  return 0;
}

//Provides: unix_kill
function unix_kill() {
  // ll("unix_kill");
  return 0;
}

//Provides: unix_listen
function unix_listen() {
  // ll("unix_listen");
  return 0;
}

//Provides: unix_mkdir
function unix_mkdir() {
  // ll("unix_mkdir");
  return 0;
}
//Provides: unix_pipe
function unix_pipe() {
  // ll("unix_pipe");
  return 0;
}

//Provides: unix_read
function unix_read() {
  // ll("unix_read");
  return 0;
}

//Provides: unix_opendir
function unix_opendir(dir) {
  // ll("unix_opendir");

  // caml_raise_unix_error("opendir");
  return [];
}

//Provides: unix_readdir
//Requires: caml_raise_constant, caml_global_data
function unix_readdir(dir) {
  // ll("unix_readdir");

  // caml_raise_unix_error("readdir");
  caml_raise_constant(caml_global_data.End_of_file);
  return [];
}

//Provides: unix_closedir
function unix_closedir() {
  // ll("unix_closedir");
  return [];
}

//Provides: unix_select
function unix_select() {
  // ll("unix_select");
  return 0;
}

//Provides: unix_set_close_on_exec
function unix_set_close_on_exec() {
  // ll("unix_set_close_on_exec");
  return 0;
}

//Provides: unix_set_nonblock
function unix_set_nonblock() {
  // ll("unix_set_nonblock");
  return 0;
}

//Provides: unix_sleep
function unix_sleep() {
  // ll("unix_sleep");
  return 0;
}

//Provides: unix_socket
function unix_socket() {
  // ll("unix_socket");
  return 0;
}

//Provides: unix_string_of_inet_addr
function unix_string_of_inet_addr() {
  // ll("unix_string_of_inet_addr");
  return 0;
}

//Provides: unix_times
function unix_times() {
  // ll("unix_times");
  return 0;
}

//Provides: unix_wait
function unix_wait() {
  // ll("unix_wait");
  return 0;
}

//Provides: unix_waitpid
function unix_waitpid() {
  // ll("unix_waitpid");
  return 0;
}

//Provides: unix_stat
var ll;
function unix_stat(arg) {
  ll("unix_stat(" + arg + ")");
  return 0;
}