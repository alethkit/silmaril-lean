/* Compile in the pinned amalgamation's translation unit to inspect nBusy. */
#ifndef SQLITE_DEBUG
#error Build this probe with SQLITE_DEBUG so its checks are active.
#endif
#include "sqlite3.c"

enum { probe_opcode = 1001, initial_busy_count = 7 };

static sqlite3 *connection;
static sqlite3_file *expected_file;
static int observed_calls;
static int callback_result;

static int retry(void *context, int count) {
  assert(context == connection);
  assert(count == initial_busy_count);
  return 1;
}

static int file_control(sqlite3_file *file, int opcode, void *arg) {
  assert(file == expected_file && opcode == probe_opcode && arg == NULL);
  assert(sqlite3_mutex_held(connection->mutex));
  assert(sqlite3InvokeBusyHandler(&connection->busyHandler) == 1);
  assert(connection->busyHandler.nBusy == initial_busy_count + 1);
  ++observed_calls;
  return callback_result;
}

int main(int argc, char **argv) {
  assert(argc == 2 && sqlite3_threadsafe() == 1);
  assert(sqlite3_open_v2(argv[1], &connection,
    SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE | SQLITE_OPEN_FULLMUTEX |
    SQLITE_OPEN_PRIVATECACHE, NULL) == SQLITE_OK);
  assert(sqlite3_exec(connection, "CREATE TABLE probe(x)", NULL, NULL, NULL) ==
    SQLITE_OK);
  assert(connection->mutex != NULL);
  assert(sqlite3_busy_handler(connection, retry, connection) == SQLITE_OK);
  assert(sqlite3_file_control(connection, NULL, SQLITE_FCNTL_FILE_POINTER,
    &expected_file) == SQLITE_OK);
  assert(expected_file != NULL && expected_file->pMethods != NULL);

  const sqlite3_io_methods *original = expected_file->pMethods;
  sqlite3_io_methods methods = *original;
  methods.xFileControl = file_control;
  expected_file->pMethods = &methods;
  connection->busyHandler.nBusy = initial_busy_count;

  const int statuses[] = {SQLITE_OK, SQLITE_BUSY, SQLITE_IOERR_READ};
  for (size_t i = 0; i < sizeof statuses / sizeof statuses[0]; ++i) {
    callback_result = statuses[i];
    assert(sqlite3_file_control(connection, NULL, probe_opcode, NULL) ==
      statuses[i]);
    assert(observed_calls == (int)i + 1);
    assert(connection->busyHandler.nBusy == initial_busy_count);
    assert(sqlite3_mutex_notheld(connection->mutex));
    printf("xFileControl status=%d restored_busy_count=%d\n",
      statuses[i], connection->busyHandler.nBusy);
  }

  expected_file->pMethods = original;
  assert(sqlite3_close(connection) == SQLITE_OK);
  return 0;
}
