-- hoistCore: a core with no uncorrelated subquery runs as compiled; one with them in every position it hoists (lookups, ON, WHERE, GROUP BY, HAVING, result columns, ORDER BY, VALUES, LIKE ESCAPE)
CREATE TABLE t(a INTEGER PRIMARY KEY, b INTEGER, c TEXT); INSERT INTO t VALUES(1,10,'x'),(2,20,'y'),(3,30,'z'),(4,40,'x');
CREATE TABLE u(k INTEGER PRIMARY KEY, v INTEGER); INSERT INTO u VALUES(1,2),(2,3),(3,1);
SELECT 1;
SELECT a, b FROM t WHERE a = 2;
SELECT a FROM t WHERE a = (SELECT max(k) FROM u);
SELECT a FROM t WHERE a IN (SELECT v FROM u) ORDER BY a;
SELECT a FROM t WHERE a IN ((SELECT min(k) FROM u), (SELECT max(k) FROM u)) ORDER BY a;
SELECT t.a, u.v FROM t JOIN u ON u.k = t.a AND u.v > (SELECT min(v) FROM u) ORDER BY 1;
SELECT c, count(*) FROM t GROUP BY c HAVING count(*) >= (SELECT min(v) FROM u) - 0 ORDER BY c;
SELECT c || (SELECT count(*) FROM u), b + (SELECT max(v) FROM u) FROM t ORDER BY b * (SELECT -1);
SELECT a FROM t WHERE c LIKE (SELECT 'x%') ESCAPE (SELECT '!') ORDER BY a;
SELECT a FROM t WHERE NOT EXISTS (SELECT 1 FROM u WHERE k > 5) AND a > (SELECT 2);
SELECT abs((SELECT -5)), cast((SELECT '7') AS INTEGER), (SELECT NULL) IS NULL;
VALUES((SELECT count(*) FROM t), (SELECT max(b) FROM t));
-- a correlated subquery holding an uncorrelated one, and one with its own WITH table read by an inner subquery
SELECT a, (SELECT v FROM u WHERE k = t.a AND v < (SELECT max(v) FROM u)) FROM t ORDER BY a;
SELECT a, (WITH w(x) AS (SELECT t.b) SELECT (SELECT x + 1 FROM w)) FROM t ORDER BY a;
SELECT a, (SELECT count(*) FROM u WHERE v < t.a AND k IN (SELECT k FROM u WHERE v > 1)) FROM t ORDER BY a;
-- no outer row: the subquery's inner one is never run
SELECT (SELECT v FROM u WHERE k = t.a AND v > (SELECT abs(-9223372036854775808))) FROM t WHERE a > 100;
SELECT count(*) FROM t WHERE b = (SELECT b FROM t AS q WHERE q.a = t.a);
-- UPDATE and DELETE whose subqueries read the table they change
UPDATE t SET b = (SELECT max(b) FROM t) + a WHERE a = (SELECT min(a) FROM t);
SELECT * FROM t ORDER BY a;
UPDATE t SET b = (SELECT count(*) FROM t AS q WHERE q.b < t.b);
SELECT * FROM t ORDER BY a;
DELETE FROM t WHERE b = (SELECT min(b) FROM t);
SELECT * FROM t ORDER BY a;
DELETE FROM t WHERE a = 2;
SELECT * FROM t ORDER BY a;
