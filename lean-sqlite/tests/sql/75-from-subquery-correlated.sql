-- A FROM subquery inside a correlated subquery reads the enclosing rows' columns.
CREATE TABLE m(a INTEGER PRIMARY KEY, b INTEGER);
INSERT INTO m VALUES(1, -9223372036854775808),(2,5),(3,6);
CREATE TABLE t(k INTEGER PRIMARY KEY, v TEXT);
INSERT INTO t VALUES(1,'x'),(2,'y'),(3,'z');
SELECT k, (SELECT y FROM (SELECT b + k y FROM m WHERE a > 1) LIMIT 1) FROM t;
-- two levels
SELECT k, (SELECT (SELECT y FROM (SELECT b + k y FROM m WHERE a > 1) LIMIT 1) + 1) FROM t;
SELECT k, (SELECT (SELECT y FROM (SELECT b + k y FROM m WHERE a > 1) LIMIT 1) + a) FROM t, m WHERE a = 2;
-- the middle query's own column and the outer one
SELECT k, (SELECT max(z) FROM (SELECT a * 10 + k z FROM m) WHERE z > (SELECT k * 10)) FROM t;
SELECT k, (SELECT (SELECT max(z) FROM (SELECT a * 10 + k + q z FROM m)) FROM (SELECT k * 100 q)) FROM t;
SELECT k FROM t WHERE EXISTS (SELECT 1 FROM (SELECT a FROM m WHERE a = k + 1));
SELECT k FROM t WHERE k IN (SELECT x - 1 FROM (SELECT a + k - k x FROM m));
SELECT k, (SELECT count(*) FROM (SELECT a FROM m WHERE a <= k) JOIN (SELECT k j) ON 1) FROM t;
SELECT k, (SELECT group_concat(w) FROM (SELECT a + k w FROM m ORDER BY a DESC)) FROM t;
