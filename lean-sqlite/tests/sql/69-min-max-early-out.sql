-- min()/max() as the only aggregate: bare columns follow sqlite's early-out (the loop stops after one row when the access
-- path or a WHERE term gives the argument's order)
CREATE TABLE v(c, n); INSERT INTO v VALUES('a',NULL),('b',NULL),('c',NULL),('d',5),('e',3),('f',3),('g',9),('h',9);
CREATE TABLE z(c, n NOT NULL); INSERT INTO z SELECT c, n FROM v WHERE n IS NOT NULL; CREATE INDEX zi ON z(n);
CREATE TABLE y(c, n); INSERT INTO y SELECT * FROM v; CREATE INDEX yi ON y(n);
CREATE TABLE w(c, n INTEGER PRIMARY KEY); INSERT INTO w SELECT c, rowid * 2 FROM v;
CREATE TABLE u(c, n COLLATE nocase); INSERT INTO u VALUES('a','a'),('b','A'),('c','a');
-- a pinned argument
SELECT c, min(n) FROM v WHERE n IS NULL;
SELECT c, max(n) FROM v WHERE n IS NULL;
SELECT c, max(n) FROM v WHERE n ISNULL AND c > 'a';
SELECT c, min(n) FROM v WHERE n IS NULL AND c IN ('b', 'c');
SELECT c, max(n) FROM v WHERE n IS (SELECT NULL);
SELECT c, min(n) FROM v WHERE n = 3 AND c > 'e';
SELECT c, max(n) FROM v WHERE 3 = n;
SELECT c, max(n) FROM y WHERE n IS NULL;
SELECT c, min(n) FROM w WHERE n = 6;
SELECT c, max(n) FROM u WHERE n = 'A';
SELECT c, max(n) FROM u WHERE n = 'A' COLLATE binary;
SELECT c, max(n) FROM u WHERE n = 'A' COLLATE nocase;
SELECT c, min(DISTINCT n) FROM v WHERE n = 3;
-- not pinned: a full scan, the last bare column at each new best
SELECT c, min(n) FROM v;
SELECT c, max(n) FROM v;
SELECT c, min(n) FROM v WHERE n IS NOT NULL;
SELECT c, max(n) FROM v WHERE n = c;
-- the access path gives the order: the rowid, an index (max reads it backwards, equal keys in reverse rowid order)
SELECT c, min(n) FROM w;
SELECT c, max(n) FROM w;
SELECT c, max(rowid) FROM z WHERE c > 'e';
SELECT c, min(n) FROM w WHERE n > 4;
SELECT c, max(n) FROM w WHERE n < 8;
SELECT c, min(n) FROM z;
SELECT c, max(n) FROM z;
SELECT c, min(DISTINCT n) FROM z;
SELECT c, max(n) FROM z WHERE c > 'e';
SELECT c, max(n) FROM z ORDER BY 1;
SELECT c, max(n) FROM y;
SELECT c, min(n) FROM y;
SELECT c, max(n) FROM y WHERE n < 9;
SELECT c, min(n) FROM y WHERE n > 3;
SELECT c, max(n) FROM z WHERE n = 3;
SELECT c, max(n) FROM z WHERE n = 3 AND c = 'f';
-- not the only aggregate, HAVING, FILTER, an expression, GROUP BY: no early-out
SELECT c, max(n), count(*) FROM z;
SELECT c, max(n), min(n) FROM z;
SELECT c, max(n) FROM z ORDER BY min(n);
SELECT c, max(n) FROM z HAVING max(n) > 1;
SELECT c, max(n) FILTER (WHERE c > 'g') FROM z;
SELECT c, max(n + 0) FROM z;
SELECT c, max(n) FROM z GROUP BY n;
SELECT c, max(n) FROM v WHERE n IS NULL GROUP BY n;
-- a subquery and a compound arm
SELECT (SELECT c || max(n) FROM z), (SELECT c FROM v WHERE n IS NULL);
SELECT c, max(n) FROM z UNION ALL SELECT c, min(n) FROM z;
SELECT c, max(n) FROM y UNION SELECT 1, 2;
SELECT c, max(n) FROM v WHERE n IS NULL UNION ALL SELECT 'x', 0;
-- sqlite may drive the loop from another index: the one on n is not taken then
CREATE TABLE t(a, c, n); CREATE INDEX tc ON t(c); CREATE INDEX tn ON t(n);
INSERT INTO t VALUES('p','k',9),('q','k',9),('r',NULL,9),('s',NULL,9);
SELECT a, max(n) FROM t WHERE c IS NULL;
SELECT a, max(n) FROM t WHERE c IS 'k';
SELECT a, max(n) FROM t WHERE c IN ('k', 'zz');
SELECT a, max(n) FROM t WHERE c = 'k' OR c = 'zz';
SELECT a, max(n) FROM t WHERE c GLOB 'k*';
SELECT a, max(n) FROM t WHERE c = 'k';
SELECT a, max(n) FROM t WHERE c BETWEEN 'a' AND 'z';
SELECT a, max(n) FROM t WHERE a > 'p';

-- a join whose only aggregate is min()/max() of a column its WHERE pins stops after its first row (bare columns are that row's)
create table jv(c,n); insert into jv values('a',null),('b',null),('c',null),('d',null);
SELECT a.c, b.c, min(a.n) FROM jv a, jv b WHERE a.n IS NULL;
SELECT a.c, b.c, min(a.n) FROM jv a LEFT JOIN jv b ON 1 WHERE a.n IS NULL;
SELECT a.c, b.c, max(b.n) FROM jv a, jv b WHERE b.n IS NULL;
SELECT a.c, b.c, min(a.n) FROM jv a JOIN jv b ON a.c = b.c WHERE a.n IS NULL;
SELECT a.c, b.c, min(b.n) FROM jv a LEFT JOIN jv b ON a.c = 'zz' WHERE b.n IS NULL;
SELECT a.c, min(a.n) FROM jv a, jv b, jv z WHERE a.n IS NULL;
SELECT count(*), min(a.n) FROM jv a, jv b WHERE a.n IS NULL;
