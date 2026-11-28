-- recursive WITH tables: the recursive SELECT prepared once for all its queue rows (uncorrelated subqueries, FROM
-- subqueries, other WITH tables and transient indexes made once), UNION's rows seen kept in an ordered set
CREATE TABLE edge(src INTEGER, dst INTEGER, w TEXT);
WITH RECURSIVE s(i) AS (SELECT 1 UNION ALL SELECT i+1 FROM s WHERE i < 300) INSERT INTO edge SELECT i, i+1, 'w' || (i % 7) FROM s;
INSERT INTO edge VALUES (5, 100, 'jump'), (5, 6, 'dup'), (NULL, 1, 'null');
-- a join to an unindexed table: a transient index built once
WITH RECURSIVE r(n, d) AS (SELECT 1, 0 UNION ALL SELECT e.dst, r.d + 1 FROM r JOIN edge e ON e.src = r.n WHERE r.d < 120)
SELECT count(*), sum(n), max(d) FROM r;
WITH RECURSIVE r(n, d) AS (SELECT 1, 0 UNION SELECT e.dst, r.d + 1 FROM r JOIN edge e ON e.src = r.n WHERE r.d < 120)
SELECT count(*), sum(n), max(d) FROM r;
-- the queue row after the table
WITH RECURSIVE r(n, d) AS (SELECT 1, 0 UNION ALL SELECT e.dst, r.d + 1 FROM edge e JOIN r ON e.src = r.n WHERE r.d < 50)
SELECT count(*), sum(n), max(d) FROM r;
-- LEFT JOIN from the queue row: a row with no edge still goes on
WITH RECURSIVE r(n, w, d) AS (SELECT 298, 'start', 0 UNION ALL SELECT coalesce(e.dst, -1), coalesce(e.w, 'none'), r.d + 1 FROM r LEFT JOIN edge e ON e.src = r.n WHERE r.d < 5 AND r.n > 0)
SELECT * FROM r;
-- an uncorrelated subquery and a FROM subquery in the recursive SELECT
WITH RECURSIVE r(n) AS (SELECT 1 UNION ALL SELECT n + s.step FROM r, (SELECT count(*) / 100 AS step FROM edge) s WHERE n < (SELECT max(src) FROM edge))
SELECT count(*), sum(n), max(n) FROM r;
-- another WITH table joined in the recursive SELECT
WITH RECURSIVE c(k, v) AS (VALUES (1, 'odd'), (0, 'even')), r(n, v) AS (SELECT 1, 'start' UNION ALL SELECT n + 1, c.v FROM r JOIN c ON c.k = r.n % 2 WHERE n < 8)
SELECT * FROM r;
-- inside a correlated subquery: prepared again for each outer row
SELECT src, (WITH RECURSIVE r(n) AS (SELECT edge.src UNION ALL SELECT n + 1 FROM r WHERE n < edge.src + 3) SELECT group_concat(n) FROM r) FROM edge WHERE src < 4;
-- UNION: duplicates of earlier rows (and among the initial rows) are not queued again
WITH RECURSIVE r(n) AS (VALUES (1), (2), (1), (NULL), (NULL) UNION SELECT (n * 3) % 17 FROM r WHERE n IS NOT NULL)
SELECT * FROM r;
WITH RECURSIVE r(x, y) AS (SELECT 1, 'a' UNION SELECT (x + 1) % 4, CASE WHEN x % 2 = 0 THEN 'a' ELSE 'b' END FROM r)
SELECT * FROM r;
WITH RECURSIVE r(n) AS (SELECT 1 UNION SELECT n + 1 FROM r WHERE n < 5000) SELECT count(*), sum(n) FROM r;
WITH RECURSIVE r(n) AS (SELECT 1 UNION SELECT n + 1 FROM r LIMIT 7) SELECT * FROM r;
-- INSERT ... SELECT appending ascending rowids, then into the middle and before the first
CREATE TABLE t(a INTEGER PRIMARY KEY, b TEXT);
WITH RECURSIVE s(i) AS (SELECT 1 UNION ALL SELECT i+1 FROM s WHERE i < 3000) INSERT INTO t SELECT i * 2, 'row ' || i || ' ' || (i % 13) || substr('xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx', 1, i % 40) FROM s;
INSERT INTO t SELECT a + 1, 'odd ' || a FROM t WHERE a % 100 = 0;
INSERT INTO t VALUES (-5, 'first'), (0, 'zero'), (100000, 'last'), (100001, 'after');
INSERT INTO t(b) VALUES ('new rowid');
INSERT INTO t VALUES (100001, 'conflict');
INSERT OR REPLACE INTO t VALUES (100001, 'replaced');
INSERT INTO t VALUES (100002, substr(hex(zeroblob(3000)), 1, 5000));
SELECT count(*), sum(a), sum(length(b)), min(a), max(a) FROM t;
SELECT a, b FROM t WHERE a < 3 OR a > 5990 OR a % 1000 = 1 ORDER BY a;
