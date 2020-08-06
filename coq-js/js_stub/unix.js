//Provides: unix_ll
function unix_ll(s, args) { 
  if (unix_ll.log) joo_global_object.console.warn(s, args); 
  if (unix_ll.trap) throw new Error("unix trap: '"+ s + "' not implemented");
}
unix_ll.log = true;       // whether to log calls
unix_ll.trap = false;     // whether to halt on calls

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


// Provides: unix_accept
// Requires: unix_ll
function unix_accept()                 { unix_ll("unix_accept", arguments); }
// Provides: unix_chdir
// Requires: unix_ll
function unix_chdir()                  { unix_ll("unix_chdir", arguments); }
// Provides: unix_chmod
// Requires: unix_ll
function unix_chmod()                  { unix_ll("unix_chmod", arguments); }
// Provides: unix_chown
// Requires: unix_ll
function unix_chown()                  { unix_ll("unix_chown", arguments); }
// Provides: unix_chroot
// Requires: unix_ll
function unix_chroot()                 { unix_ll("unix_chroot", arguments); }
// Provides: unix_clear_close_on_exec
// Requires: unix_ll
function unix_clear_close_on_exec()    { unix_ll("unix_clear_close_on_exec", arguments); }
// Provides: unix_clear_nonblock
// Requires: unix_ll
function unix_clear_nonblock()         { unix_ll("unix_clear_nonblock", arguments); }
// Provides: unix_environment_unsafe
// Requires: unix_ll
function unix_environment_unsafe()     { unix_ll("unix_environment_unsafe", arguments); }
// Provides: unix_execv
// Requires: unix_ll
function unix_execv()                  { unix_ll("unix_execv", arguments); }
// Provides: unix_fchmod
// Requires: unix_ll
function unix_fchmod()                 { unix_ll("unix_fchmod", arguments); }
// Provides: unix_fchown
// Requires: unix_ll
function unix_fchown()                 { unix_ll("unix_fchown", arguments); }
// Provides: unix_fstat
// Requires: unix_ll
function unix_fstat()                 { unix_ll("unix_fstat", arguments); }
// Provides: unix_fstat_64
// Requires: unix_ll
function unix_fstat_64()              { unix_ll("unix_fstat_64", arguments); }
// Provides: unix_ftruncate
// Requires: unix_ll
function unix_ftruncate()             { unix_ll("unix_ftruncate", arguments); }
// Provides: unix_ftruncate_64
// Requires: unix_ll
function unix_ftruncate_64()          { unix_ll("unix_ftruncate_64", arguments); }
// Provides: unix_getaddrinfo
// Requires: unix_ll
function unix_getaddrinfo()           { unix_ll("unix_getaddrinfo", arguments); }
// Provides: unix_getegid
// Requires: unix_ll
function unix_getegid()               { unix_ll("unix_getegid", arguments); }
// Provides: unix_geteuid
// Requires: unix_ll
function unix_geteuid()               { unix_ll("unix_geteuid", arguments); }
// Provides: unix_getgid
// Requires: unix_ll
function unix_getgid()                { unix_ll("unix_getgid", arguments); }
// Provides: unix_getgrgid
// Requires: unix_ll
function unix_getgrgid()              { unix_ll("unix_getgrgid", arguments); }
// Provides: unix_getgrnam
// Requires: unix_ll
function unix_getgrnam()              { unix_ll("unix_getgrnam", arguments); }
// Provides: unix_getgroups
// Requires: unix_ll
function unix_getgroups()             { unix_ll("unix_getgroups", arguments); }
// Provides: unix_gethostbyaddr
// Requires: unix_ll
function unix_gethostbyaddr()         { unix_ll("unix_gethostbyaddr", arguments); }
// Provides: unix_gethostbyname
// Requires: unix_ll
function unix_gethostbyname()         { unix_ll("unix_gethostbyname", arguments); }
// Provides: unix_gethostname
// Requires: unix_ll
function unix_gethostname()           { unix_ll("unix_gethostname", arguments); }
// Provides: unix_getitimer
// Requires: unix_ll
function unix_getitimer()             { unix_ll("unix_getitimer", arguments); }
// Provides: unix_getlogin
// Requires: unix_ll
function unix_getlogin()              { unix_ll("unix_getlogin", arguments); }
// Provides: unix_getnameinfo
// Requires: unix_ll
function unix_getnameinfo()           { unix_ll("unix_getnameinfo", arguments); }
// Provides: unix_getpeername
// Requires: unix_ll
function unix_getpeername()           { unix_ll("unix_getpeername", arguments); }
// Provides: unix_getppid
// Requires: unix_ll
function unix_getppid()               { unix_ll("unix_getppid", arguments); }
// Provides: unix_getprotobyname
// Requires: unix_ll
function unix_getprotobyname()        { unix_ll("unix_getprotobyname", arguments); }
// Provides: unix_getprotobynumber
// Requires: unix_ll
function unix_getprotobynumber()      { unix_ll("unix_getprotobynumber", arguments); }
// Provides: unix_getpwuid
// Requires: unix_ll
function unix_getpwuid()              { unix_ll("unix_getpwuid", arguments); }
// Provides: unix_getservbyname
// Requires: unix_ll
function unix_getservbyname()         { unix_ll("unix_getservbyname", arguments); }
// Provides: unix_getservbyport
// Requires: unix_ll
function unix_getservbyport()         { unix_ll("unix_getservbyport", arguments); }
// Provides: unix_getsockopt
// Requires: unix_ll
function unix_getsockopt()            { unix_ll("unix_getsockopt", arguments); }
// Provides: unix_getuid
// Requires: unix_ll
function unix_getuid()                { unix_ll("unix_getuid", arguments); }
// Provides: unix_has_symlink
// Requires: unix_ll
function unix_has_symlink()           { unix_ll("unix_has_symlink", arguments); }
// Provides: unix_initgroups
// Requires: unix_ll
function unix_initgroups()            { unix_ll("unix_initgroups", arguments); }
// Provides: unix_link
// Requires: unix_ll
function unix_link()                  { unix_ll("unix_link", arguments); }
// Provides: unix_lockf
// Requires: unix_ll
function unix_lockf()                 { unix_ll("unix_lockf", arguments); }
// Provides: unix_lseek
// Requires: unix_ll
function unix_lseek()                 { unix_ll("unix_lseek", arguments); }
// Provides: unix_lseek_64
// Requires: unix_ll
function unix_lseek_64()              { unix_ll("unix_lseek_64", arguments); }
// Provides: unix_lstat
// Requires: unix_ll
function unix_lstat()                 { unix_ll("unix_lstat", arguments); }
// Provides: unix_lstat_64
// Requires: unix_ll
function unix_lstat_64()              { unix_ll("unix_lstat_64", arguments); }
// Provides: unix_mkfifo
// Requires: unix_ll
function unix_mkfifo()                { unix_ll("unix_mkfifo", arguments); }
// Provides: unix_nice
// Requires: unix_ll
function unix_nice()                  { unix_ll("unix_nice", arguments); }
// Provides: unix_open
// Requires: unix_ll
function unix_open()                  { unix_ll("unix_open", arguments); }
// Provides: unix_putenv
// Requires: unix_ll
function unix_putenv()                { unix_ll("unix_putenv", arguments); }
// Provides: unix_readlink
// Requires: unix_ll, caml_raise_unix_error
function unix_readlink()              { unix_ll("unix_readlink", arguments);
                                        caml_raise_unix_error("not implemented: unix_readlink"); }
// Provides: unix_recv
// Requires: unix_ll
function unix_recv()                  { unix_ll("unix_recv", arguments); }
// Provides: unix_recvfrom
// Requires: unix_ll
function unix_recvfrom()              { unix_ll("unix_recvfrom", arguments); }
// Provides: unix_rename
// Requires: unix_ll
function unix_rename()                { unix_ll("unix_rename", arguments); }
// Provides: unix_rewinddir
// Requires: unix_ll
function unix_rewinddir()             { unix_ll("unix_rewinddir", arguments); }
// Provides: unix_rmdir
// Requires: unix_ll
function unix_rmdir()                 { unix_ll("unix_rmdir", arguments); }
// Provides: unix_send
// Requires: unix_ll
function unix_send()                  { unix_ll("unix_send", arguments); }
// Provides: unix_sendto
// Requires: unix_ll
function unix_sendto()                { unix_ll("unix_sendto", arguments); }
// Provides: unix_setgid
// Requires: unix_ll
function unix_setgid()                { unix_ll("unix_setgid", arguments); }
// Provides: unix_setgroups
// Requires: unix_ll
function unix_setgroups()             { unix_ll("unix_setgroups", arguments); }
// Provides: unix_setitimer
// Requires: unix_ll
function unix_setitimer()             { unix_ll("unix_setitimer", arguments); }
// Provides: unix_setsid
// Requires: unix_ll
function unix_setsid()                { unix_ll("unix_setsid", arguments); }
// Provides: unix_setsockopt
// Requires: unix_ll
function unix_setsockopt()            { unix_ll("unix_setsockopt", arguments); }
// Provides: unix_setuid
// Requires: unix_ll
function unix_setuid()                { unix_ll("unix_setuid", arguments); }
// Provides: unix_shutdown
// Requires: unix_ll
function unix_shutdown()              { unix_ll("unix_shutdown", arguments); }
// Provides: unix_sigpending
// Requires: unix_ll
function unix_sigpending()            { unix_ll("unix_sigpending", arguments); }
// Provides: unix_sigprocmask
// Requires: unix_ll
function unix_sigprocmask()           { unix_ll("unix_sigprocmask", arguments); }
// Provides: unix_sigsuspend
// Requires: unix_ll
function unix_sigsuspend()            { unix_ll("unix_sigsuspend", arguments); }
// Provides: unix_single_write
// Requires: unix_ll
function unix_single_write()          { unix_ll("unix_single_write", arguments); }
// Provides: unix_socketpair
// Requires: unix_ll
function unix_socketpair()            { unix_ll("unix_socketpair", arguments); }
// Provides: unix_stat_64
// Requires: unix_ll
function unix_stat_64()               { unix_ll("unix_stat_64", arguments); }
// Provides: unix_symlink
// Requires: unix_ll
function unix_symlink()               { unix_ll("unix_symlink", arguments); }
// Provides: unix_tcdrain
// Requires: unix_ll
function unix_tcdrain()               { unix_ll("unix_tcdrain", arguments); }
// Provides: unix_tcflow
// Requires: unix_ll
function unix_tcflow()                { unix_ll("unix_tcflow", arguments); }
// Provides: unix_tcflush
// Requires: unix_ll
function unix_tcflush()               { unix_ll("unix_tcflush", arguments); }
// Provides: unix_tcgetattr
// Requires: unix_ll
function unix_tcgetattr()             { unix_ll("unix_tcgetattr", arguments); }
// Provides: unix_tcsendbreak
// Requires: unix_ll
function unix_tcsendbreak()           { unix_ll("unix_tcsendbreak", arguments); }
// Provides: unix_tcsetattr
// Requires: unix_ll
function unix_tcsetattr()             { unix_ll("unix_tcsetattr", arguments); }
// Provides: unix_truncate
// Requires: unix_ll
function unix_truncate()              { unix_ll("unix_truncate", arguments); }
// Provides: unix_truncate_64
// Requires: unix_ll
function unix_truncate_64()           { unix_ll("unix_truncate_64", arguments); }
// Provides: unix_umask
// Requires: unix_ll
function unix_umask()                 { unix_ll("unix_umask", arguments); }
// Provides: unix_unlink
// Requires: unix_ll
function unix_unlink()                { unix_ll("unix_unlink", arguments); }
// Provides: unix_utimes
// Requires: unix_ll
function unix_utimes()                { unix_ll("unix_utimes", arguments); }
// Provides: unix_write
// Requires: unix_ll
function unix_write()                 { unix_ll("unix_write", arguments); }
// Provides: caml_channel_descriptor
// Requires: unix_ll
function caml_channel_descriptor()   { unix_ll("caml_channel_descriptor", arguments); }
// Provides: caml_mutex_try_lock
// Requires: unix_ll
function caml_mutex_try_lock()       { unix_ll("caml_mutex_try_lock", arguments); }
// Provides: caml_obj_add_offset
// Requires: unix_ll
function caml_obj_add_offset()       { unix_ll("caml_obj_add_offset", arguments); }
// Provides: caml_sys_unsafe_getenv
// Requires: unix_ll
function caml_sys_unsafe_getenv()    { unix_ll("caml_sys_unsafe_getenv", arguments); }
// Provides: caml_thread_join
// Requires: unix_ll
function caml_thread_join()          { unix_ll("caml_thread_join", arguments); }
// Provides: caml_thread_sigmask
// Requires: unix_ll
function caml_thread_sigmask()       { unix_ll("caml_thread_sigmask", arguments); }
// Provides: caml_unix_map_file_bytecode
// Requires: unix_ll
function caml_unix_map_file_bytecode() { unix_ll("caml_unix_map_file_bytecode", arguments); }
// Provides: caml_wait_signal
// Requires: unix_ll
function caml_wait_signal()          { unix_ll("caml_wait_signal", arguments); }
