#include "sqlite3.h"

#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CHECK(condition) do { \
  if (!(condition)) { \
    fprintf(stderr, "native.c:%d: %s\n", __LINE__, #condition); \
    exit(EXIT_FAILURE); \
  } \
} while (0)
#define COUNT(array) (sizeof(array) / sizeof((array)[0]))

typedef struct {
  int64_t rowid, value;
} Row;

static const Row rows[] = {
  { INT64_MIN, 0 }, { -5, -8 }, { 0, 7 }, { 2, 7 }, { 9, 9 }, { INT64_MAX, 3 }
};

typedef struct {
  Row rows[COUNT(rows)];
  size_t length;
} Result;

typedef struct {
  Result scan;
  unsigned connects, disconnects, opens, closes, plans, filters, advances, end_checks;
} Probe;

typedef struct {
  sqlite3_vtab base;
  Probe *probe;
} Table;

typedef struct {
  sqlite3_vtab_cursor base;
  int index, step;
  int64_t lower;
} Cursor;

static Probe *probe_of(sqlite3_vtab_cursor *cursor) {
  return ((Table *)cursor->pVtab)->probe;
}

static int connect_table(sqlite3 *db, void *aux, int argc, const char *const *argv,
                         sqlite3_vtab **out, char **error) {
  (void)argc;
  (void)argv;
  (void)error;
  int rc = sqlite3_declare_vtab(db, "CREATE TABLE x(value INTEGER)");
  if (rc != SQLITE_OK) return rc;
  Table *table = sqlite3_malloc(sizeof(*table));
  if (table == NULL) return SQLITE_NOMEM;
  *table = (Table){.probe = aux};
  table->probe->connects++;
  *out = &table->base;
  return SQLITE_OK;
}

static int disconnect_table(sqlite3_vtab *base) {
  ((Table *)base)->probe->disconnects++;
  sqlite3_free(base);
  return SQLITE_OK;
}

static int best_index(sqlite3_vtab *base, sqlite3_index_info *info) {
  if (info->nOrderBy != 1 || info->aOrderBy[0].iColumn != -1)
    return SQLITE_CONSTRAINT;
  int lower = -1, ceiling = -1;
  for (int i = 0; i < info->nConstraint; ++i) {
    const struct sqlite3_index_constraint *term = &info->aConstraint[i];
    if (!term->usable) continue;
    if (term->iColumn == -1 && term->op == SQLITE_INDEX_CONSTRAINT_GE) lower = i;
    if (term->iColumn == 0 && term->op == SQLITE_INDEX_CONSTRAINT_LT) ceiling = i;
  }
  if (lower < 0 || ceiling < 0) return SQLITE_CONSTRAINT;
  info->aConstraintUsage[ceiling].argvIndex = 1;
  info->aConstraintUsage[lower].argvIndex = 2;
  info->aConstraintUsage[lower].omit = 1;
  info->orderByConsumed = 1;
  info->idxNum = info->aOrderBy[0].desc ? 2 : 1;
  info->idxStr = "bounded";
  info->estimatedCost = (double)COUNT(rows);
  info->estimatedRows = COUNT(rows);
  ((Table *)base)->probe->plans++;
  return SQLITE_OK;
}

static int open_cursor(sqlite3_vtab *base, sqlite3_vtab_cursor **out) {
  Cursor *cursor = sqlite3_malloc(sizeof(*cursor));
  if (cursor == NULL) return SQLITE_NOMEM;
  *cursor = (Cursor){.index = -1};
  ((Table *)base)->probe->opens++;
  *out = &cursor->base;
  return SQLITE_OK;
}

static int close_cursor(sqlite3_vtab_cursor *base) {
  probe_of(base)->closes++;
  sqlite3_free(base);
  return SQLITE_OK;
}

static bool in_range(const Cursor *cursor) {
  return cursor->index >= 0 && (size_t)cursor->index < COUNT(rows);
}

static void skip_below_lower(Cursor *cursor) {
  while (in_range(cursor) && rows[cursor->index].rowid < cursor->lower)
    cursor->index += cursor->step;
}

static int filter_cursor(sqlite3_vtab_cursor *base, int index, const char *name,
                         int argc, sqlite3_value **argv) {
  probe_of(base)->filters++;
  if (argc != 2 || name == NULL || strcmp(name, "bounded") != 0 ||
      (index != 1 && index != 2)) return SQLITE_ERROR;
  if (sqlite3_value_type(argv[0]) != SQLITE_INTEGER ||
      sqlite3_value_type(argv[1]) != SQLITE_INTEGER) return SQLITE_MISMATCH;
  Cursor *cursor = (Cursor *)base;
  cursor->step = index == 1 ? 1 : -1;
  cursor->index = index == 1 ? 0 : (int)COUNT(rows) - 1;
  cursor->lower = sqlite3_value_int64(argv[1]);
  skip_below_lower(cursor);
  return SQLITE_OK;
}

static int next_row(sqlite3_vtab_cursor *base) {
  Cursor *cursor = (Cursor *)base;
  CHECK(in_range(cursor));
  probe_of(base)->advances++;
  cursor->index += cursor->step;
  skip_below_lower(cursor);
  return SQLITE_OK;
}

static int end_of_scan(sqlite3_vtab_cursor *base) {
  Probe *probe = probe_of(base);
  Cursor *cursor = (Cursor *)base;
  if (!in_range(cursor)) {
    probe->end_checks++;
    return 1;
  }
  CHECK(probe->scan.length < COUNT(rows));
  probe->scan.rows[probe->scan.length++] = rows[cursor->index];
  return 0;
}

static int read_column(sqlite3_vtab_cursor *base, sqlite3_context *ctx, int column) {
  Cursor *cursor = (Cursor *)base;
  CHECK(column == 0 && in_range(cursor));
  sqlite3_result_int64(ctx, rows[cursor->index].value);
  return SQLITE_OK;
}

static int read_rowid(sqlite3_vtab_cursor *base, sqlite3_int64 *out) {
  Cursor *cursor = (Cursor *)base;
  CHECK(in_range(cursor));
  *out = rows[cursor->index].rowid;
  return SQLITE_OK;
}

static const sqlite3_module module = {
  .iVersion = 1,
  .xConnect = connect_table,
  .xDisconnect = disconnect_table,
  .xBestIndex = best_index,
  .xOpen = open_cursor,
  .xClose = close_cursor,
  .xFilter = filter_cursor,
  .xNext = next_row,
  .xEof = end_of_scan,
  .xColumn = read_column,
  .xRowid = read_rowid,
};

static sqlite3_stmt *prepare(sqlite3 *db, const char *sql) {
  sqlite3_stmt *stmt;
  int rc = sqlite3_prepare_v2(db, sql, -1, &stmt, NULL);
  if (rc != SQLITE_OK) fprintf(stderr, "%s: %s\n", sql, sqlite3_errmsg(db));
  CHECK(rc == SQLITE_OK);
  return stmt;
}

static Result execute_query(sqlite3 *db, bool virtual_table, int dir, int64_t lo, int64_t hi) {
  char sql[160];
  sqlite3_snprintf(sizeof(sql), sql,
    "SELECT rowid,value FROM %s WHERE rowid>=?1 AND value<?2 ORDER BY rowid %s",
    virtual_table ? "backed" : "ordinary", dir == 1 ? "ASC" : "DESC");
  sqlite3_stmt *stmt = prepare(db, sql);
  CHECK(sqlite3_bind_int64(stmt, 1, lo) == SQLITE_OK);
  CHECK(sqlite3_bind_int64(stmt, 2, hi) == SQLITE_OK);
  Result result = {0};
  int rc;
  while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
    CHECK(result.length < COUNT(rows));
    CHECK(sqlite3_column_type(stmt, 0) == SQLITE_INTEGER);
    CHECK(sqlite3_column_type(stmt, 1) == SQLITE_INTEGER);
    result.rows[result.length++] = (Row){sqlite3_column_int64(stmt, 0),
                                         sqlite3_column_int64(stmt, 1)};
  }
  if (rc != SQLITE_DONE) fprintf(stderr, "%s: %s\n", sql, sqlite3_errmsg(db));
  CHECK(rc == SQLITE_DONE);
  if (virtual_table) CHECK(sqlite3_stmt_status(stmt, SQLITE_STMTSTATUS_SORT, 0) == 0);
  CHECK(sqlite3_finalize(stmt) == SQLITE_OK);
  return result;
}

static void compare_and_print(sqlite3 *db, Probe *probe, int dir, int64_t lo, int64_t hi) {
  probe->scan.length = 0;
  unsigned plans = probe->plans, filters = probe->filters, advances = probe->advances;
  unsigned end_checks = probe->end_checks;
  Result actual = execute_query(db, true, dir, lo, hi);
  Result expected = execute_query(db, false, dir, lo, hi);
  CHECK(probe->plans > plans && probe->filters == filters + 1);
  CHECK(probe->end_checks == end_checks + 1);
  CHECK(probe->advances == advances + probe->scan.length);
  CHECK(actual.length == expected.length);
  for (size_t i = 0; i < actual.length; ++i) {
    CHECK(actual.rows[i].rowid == expected.rows[i].rowid);
    CHECK(actual.rows[i].value == expected.rows[i].value);
  }
  printf("case %d %" PRId64 " %" PRId64 "\n", dir, lo, hi);
  for (size_t i = 0; i < probe->scan.length; ++i)
    printf("scan %" PRId64 " %" PRId64 "\n", probe->scan.rows[i].rowid, probe->scan.rows[i].value);
  for (size_t i = 0; i < actual.length; ++i)
    printf("row %" PRId64 " %" PRId64 "\n", actual.rows[i].rowid, actual.rows[i].value);
}

int main(void) {
  CHECK(sqlite3_libversion_number() == 3054001);
  CHECK(strcmp(sqlite3_sourceid(), SQLITE_SOURCE_ID) == 0);
  sqlite3 *db;
  Probe probe = {0};
  CHECK(sqlite3_open(":memory:", &db) == SQLITE_OK);
  CHECK(sqlite3_create_module(db, "backed", &module, &probe) == SQLITE_OK);
  CHECK(sqlite3_exec(db, "CREATE TABLE ordinary(value INTEGER)", NULL, NULL, NULL) == SQLITE_OK);
  sqlite3_stmt *insert = prepare(db, "INSERT INTO ordinary(rowid,value) VALUES (?1,?2)");
  for (size_t i = 0; i < COUNT(rows); ++i) {
    CHECK(sqlite3_bind_int64(insert, 1, rows[i].rowid) == SQLITE_OK);
    CHECK(sqlite3_bind_int64(insert, 2, rows[i].value) == SQLITE_OK);
    CHECK(sqlite3_step(insert) == SQLITE_DONE);
    CHECK(sqlite3_reset(insert) == SQLITE_OK);
  }
  CHECK(sqlite3_finalize(insert) == SQLITE_OK);

  static const int64_t lowers[] = {INT64_MIN, -5, -4, 0, 3, INT64_MAX};
  static const int64_t ceilings[] = {-8, -7, 0, 7, 8, INT64_MAX};
  for (int dir = 1; dir <= 2; ++dir)
    for (size_t i = 0; i < COUNT(lowers); ++i)
      for (size_t j = 0; j < COUNT(ceilings); ++j)
        compare_and_print(db, &probe, dir, lowers[i], ceilings[j]);

  unsigned end_checks = probe.end_checks;
  sqlite3_stmt *invalid = prepare(db,
    "SELECT rowid,value FROM backed WHERE rowid>=0 AND value<NULL ORDER BY rowid");
  CHECK(sqlite3_step(invalid) == SQLITE_MISMATCH);
  CHECK(sqlite3_finalize(invalid) == SQLITE_MISMATCH);
  CHECK(probe.end_checks == end_checks && probe.opens == probe.filters && probe.closes == probe.opens);
  CHECK(sqlite3_close(db) == SQLITE_OK);
  CHECK(probe.connects == 1 && probe.disconnects == 1);
  return EXIT_SUCCESS;
}
