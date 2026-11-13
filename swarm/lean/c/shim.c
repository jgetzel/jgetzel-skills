// The C swarm-lean needs: sqlite3 (open, prepare, bind, step, columns), the local time of day, and exec.
#include <lean/lean.h>
#include <sqlite3.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static lean_obj_res io_err(const char *msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static void noop_foreach(void *p, b_lean_obj_arg f) { (void)p; (void)f; }

// A connection; sqlite3_close_v2 waits for its statements, so the order the GC frees them in does not matter.
static void conn_fin(void *p) { if (p) sqlite3_close_v2((sqlite3 *)p); }
static lean_external_class *conn_cls;

// A statement; finalized when freed (finalizing it earlier is not needed: the GC frees it at its last use).
static void stmt_fin(void *p) { if (p) sqlite3_finalize((sqlite3_stmt *)p); }
static lean_external_class *stmt_cls;

static void init_classes(void) {
  if (!conn_cls) conn_cls = lean_register_external_class(conn_fin, noop_foreach);
  if (!stmt_cls) stmt_cls = lean_register_external_class(stmt_fin, noop_foreach);
}

static sqlite3 *conn_of(b_lean_obj_arg c) { return (sqlite3 *)lean_get_external_data(c); }
static sqlite3_stmt *stmt_of(b_lean_obj_arg s) { return (sqlite3_stmt *)lean_get_external_data(s); }

LEAN_EXPORT lean_obj_res swarm_db_open(b_lean_obj_arg path, uint8_t ro, lean_obj_arg w) {
  init_classes();
  sqlite3 *db = NULL;
  int flags = ro ? SQLITE_OPEN_READONLY : (SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE);
  int rc = sqlite3_open_v2(lean_string_cstr(path), &db, flags, NULL);
  if (rc != SQLITE_OK) {
    lean_obj_res e = io_err(db ? sqlite3_errmsg(db) : sqlite3_errstr(rc));
    sqlite3_close_v2(db);
    return e;
  }
  sqlite3_busy_timeout(db, 10000);
  return lean_io_result_mk_ok(lean_alloc_external(conn_cls, db));
}

LEAN_EXPORT lean_obj_res swarm_db_errmsg(b_lean_obj_arg c, lean_obj_arg w) {
  return lean_io_result_mk_ok(lean_mk_string(sqlite3_errmsg(conn_of(c))));
}

LEAN_EXPORT lean_obj_res swarm_db_prepare(b_lean_obj_arg c, b_lean_obj_arg sql, lean_obj_arg w) {
  init_classes();
  sqlite3_stmt *st = NULL;
  if (sqlite3_prepare_v2(conn_of(c), lean_string_cstr(sql), -1, &st, NULL) != SQLITE_OK || !st) {
    if (st) sqlite3_finalize(st);
    return io_err(sqlite3_errmsg(conn_of(c)));
  }
  return lean_io_result_mk_ok(lean_alloc_external(stmt_cls, st));
}

static lean_obj_res bind_rc(b_lean_obj_arg s, int rc) {
  if (rc != SQLITE_OK) return io_err(sqlite3_errmsg(sqlite3_db_handle(stmt_of(s))));
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res swarm_db_bind_null(b_lean_obj_arg s, uint32_t i, lean_obj_arg w) {
  return bind_rc(s, sqlite3_bind_null(stmt_of(s), (int)i));
}

LEAN_EXPORT lean_obj_res swarm_db_bind_int(b_lean_obj_arg s, uint32_t i, int64_t v, lean_obj_arg w) {
  return bind_rc(s, sqlite3_bind_int64(stmt_of(s), (int)i, v));
}

LEAN_EXPORT lean_obj_res swarm_db_bind_real(b_lean_obj_arg s, uint32_t i, double v, lean_obj_arg w) {
  return bind_rc(s, sqlite3_bind_double(stmt_of(s), (int)i, v));
}

LEAN_EXPORT lean_obj_res swarm_db_bind_text(b_lean_obj_arg s, uint32_t i, b_lean_obj_arg v, lean_obj_arg w) {
  return bind_rc(s, sqlite3_bind_text(stmt_of(s), (int)i, lean_string_cstr(v), (int)lean_string_size(v) - 1,
                                      SQLITE_TRANSIENT));
}

// 1 a row, 0 done; an error otherwise.
LEAN_EXPORT lean_obj_res swarm_db_step(b_lean_obj_arg s, lean_obj_arg w) {
  int rc = sqlite3_step(stmt_of(s));
  if (rc == SQLITE_ROW) return lean_io_result_mk_ok(lean_box(1));
  if (rc == SQLITE_DONE) return lean_io_result_mk_ok(lean_box(0));
  return io_err(sqlite3_errmsg(sqlite3_db_handle(stmt_of(s))));
}

LEAN_EXPORT lean_obj_res swarm_db_reset(b_lean_obj_arg s, lean_obj_arg w) {
  sqlite3_reset(stmt_of(s));
  sqlite3_clear_bindings(stmt_of(s));
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res swarm_db_column_count(b_lean_obj_arg s, lean_obj_arg w) {
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)sqlite3_column_count(stmt_of(s))));
}

LEAN_EXPORT lean_obj_res swarm_db_column_name(b_lean_obj_arg s, uint32_t i, lean_obj_arg w) {
  const char *n = sqlite3_column_name(stmt_of(s), (int)i);
  return lean_io_result_mk_ok(lean_mk_string(n ? n : ""));
}

// SQLITE_INTEGER 1, FLOAT 2, TEXT 3, BLOB 4, NULL 5.
LEAN_EXPORT lean_obj_res swarm_db_column_type(b_lean_obj_arg s, uint32_t i, lean_obj_arg w) {
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)sqlite3_column_type(stmt_of(s), (int)i)));
}

LEAN_EXPORT lean_obj_res swarm_db_column_int(b_lean_obj_arg s, uint32_t i, lean_obj_arg w) {
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)sqlite3_column_int64(stmt_of(s), (int)i)));
}

LEAN_EXPORT lean_obj_res swarm_db_column_real(b_lean_obj_arg s, uint32_t i, lean_obj_arg w) {
  return lean_io_result_mk_ok(lean_box_float(sqlite3_column_double(stmt_of(s), (int)i)));
}

LEAN_EXPORT lean_obj_res swarm_db_column_text(b_lean_obj_arg s, uint32_t i, lean_obj_arg w) {
  const unsigned char *t = sqlite3_column_text(stmt_of(s), (int)i);
  int n = sqlite3_column_bytes(stmt_of(s), (int)i);
  return lean_io_result_mk_ok(lean_mk_string_from_bytes(t ? (const char *)t : "", t ? (size_t)n : 0));
}

LEAN_EXPORT lean_obj_res swarm_db_changes(b_lean_obj_arg c, lean_obj_arg w) {
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)sqlite3_changes64(conn_of(c))));
}

// os.date("%H:%M", t): the local time of day of epoch second t.
LEAN_EXPORT lean_obj_res swarm_hhmm(int64_t t, lean_obj_arg w) {
  time_t tt = (time_t)t;
  struct tm tm;
  char buf[16];
  if (!localtime_r(&tt, &tm) || !strftime(buf, sizeof buf, "%H:%M", &tm)) return io_err("localtime failed");
  return lean_io_result_mk_ok(lean_mk_string(buf));
}

// Replaces this process with file (searched on PATH) run as argv; returns only on failure.
LEAN_EXPORT lean_obj_res swarm_execvp(b_lean_obj_arg file, b_lean_obj_arg args, lean_obj_arg w) {
  size_t n = lean_array_size(args);
  char **argv = calloc(n + 1, sizeof(char *));
  if (!argv) return io_err("out of memory");
  for (size_t i = 0; i < n; i++) argv[i] = (char *)lean_string_cstr(lean_array_get_core(args, i));
  execvp(lean_string_cstr(file), argv);
  int e = errno;
  free(argv);
  return io_err(strerror(e));
}

// Epoch seconds (os.time()).
LEAN_EXPORT lean_obj_res swarm_now(lean_obj_arg w) {
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)time(NULL)));
}

// Board #101's Sys (SwarmLean/Sys.lean): the process and file calls Lean's IO lacks.
#include <signal.h>
#include <limits.h>
extern char **environ;

// posix.signal.kill(pid, 0) == 0: the process exists and may be signalled.
LEAN_EXPORT lean_obj_res swarm_alive(int64_t pid, lean_obj_arg w) {
  return lean_io_result_mk_ok(lean_box(pid > 0 && kill((pid_t)pid, 0) == 0));
}

LEAN_EXPORT lean_obj_res swarm_getppid(lean_obj_arg w) {
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)getppid()));
}

// Epoch seconds with the fraction (clock_gettime(CLOCK_REALTIME)).
LEAN_EXPORT lean_obj_res swarm_now_f(lean_obj_arg w) {
  struct timespec ts;
  clock_gettime(CLOCK_REALTIME, &ts);
  return lean_io_result_mk_ok(lean_box_float((double)ts.tv_sec + ts.tv_nsec / 1e9));
}

// os.date(fmt, t) in local time.
LEAN_EXPORT lean_obj_res swarm_strftime(b_lean_obj_arg fmt, int64_t t, lean_obj_arg w) {
  time_t tt = (time_t)t;
  struct tm tm;
  char buf[256];
  if (!localtime_r(&tt, &tm)) return io_err("localtime failed");
  size_t n = strftime(buf, sizeof buf, lean_string_cstr(fmt), &tm);
  buf[n] = 0;
  return lean_io_result_mk_ok(lean_mk_string(buf));
}

// uname().nodename.
LEAN_EXPORT lean_obj_res swarm_hostname(lean_obj_arg w) {
  char buf[256];
  if (gethostname(buf, sizeof buf) != 0) return io_err(strerror(errno));
  buf[sizeof buf - 1] = 0;
  return lean_io_result_mk_ok(lean_mk_string(buf));
}

// Every NAME=VALUE of the environment.
LEAN_EXPORT lean_obj_res swarm_environ(lean_obj_arg w) {
  lean_object *a = lean_mk_empty_array();
  for (char **e = environ; *e; e++) a = lean_array_push(a, lean_mk_string(*e));
  return lean_io_result_mk_ok(a);
}

LEAN_EXPORT lean_obj_res swarm_setenv(b_lean_obj_arg k, b_lean_obj_arg v, lean_obj_arg w) {
  if (setenv(lean_string_cstr(k), lean_string_cstr(v), 1) != 0) return io_err(strerror(errno));
  return lean_io_result_mk_ok(lean_box(0));
}

// readlink(2); an error when p is not a symlink.
LEAN_EXPORT lean_obj_res swarm_readlink(b_lean_obj_arg p, lean_obj_arg w) {
  char buf[PATH_MAX + 1];
  ssize_t n = readlink(lean_string_cstr(p), buf, PATH_MAX);
  if (n < 0) return io_err(strerror(errno));
  buf[n] = 0;
  return lean_io_result_mk_ok(lean_mk_string(buf));
}

// link(2): a hard link to a at b.
LEAN_EXPORT lean_obj_res swarm_link(b_lean_obj_arg a, b_lean_obj_arg b, lean_obj_arg w) {
  if (link(lean_string_cstr(a), lean_string_cstr(b)) != 0) return io_err(strerror(errno));
  return lean_io_result_mk_ok(lean_box(0));
}

/* Lean's main calls lean_initialize() once any Lean.* module is imported (here only Lean.Data.Json), which links and
   initializes the whole compiler library (~90 MB). Only the runtime is needed: each module initializes its imports. */
void lean_initialize_runtime_module(void);
void lean_initialize(void) { lean_initialize_runtime_module(); }
