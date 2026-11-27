-- Joins with no usable index on the inner table (sqlite builds an automatic index there).
CREATE TABLE a(id INTEGER PRIMARY KEY, x INTEGER, y TEXT, z);
CREATE TABLE b(id INTEGER PRIMARY KEY, x INTEGER, t TEXT COLLATE NOCASE, r REAL, n);
CREATE TABLE c(id INTEGER PRIMARY KEY, bx INTEGER, w TEXT);
WITH RECURSIVE s(n) AS (SELECT 1 UNION ALL SELECT n+1 FROM s WHERE n < 60)
INSERT INTO a SELECT n, n % 7, CASE n % 4 WHEN 0 THEN 'Ab' WHEN 1 THEN 'ab' WHEN 2 THEN 'AB' ELSE NULL END, CASE n % 3 WHEN 0 THEN n % 5 WHEN 1 THEN (n % 5) || '' ELSE (n % 5) + 0.0 END FROM s;
WITH RECURSIVE s(n) AS (SELECT 1 UNION ALL SELECT n+1 FROM s WHERE n < 80)
INSERT INTO b SELECT n, CASE WHEN n % 11 = 0 THEN NULL ELSE n % 9 END, CASE n % 3 WHEN 0 THEN 'ab' WHEN 1 THEN 'aB' ELSE 'zz' END, (n % 6) / 2, CASE n % 4 WHEN 0 THEN n % 5 WHEN 1 THEN (n % 5) || '' WHEN 2 THEN (n % 5) + 0.0 ELSE NULL END FROM s;
WITH RECURSIVE s(n) AS (SELECT 1 UNION ALL SELECT n+1 FROM s WHERE n < 30)
INSERT INTO c SELECT n, n % 9, 'w' || n FROM s;
CREATE TABLE e(id INTEGER PRIMARY KEY, x INTEGER);
SELECT a.id, b.id FROM a JOIN b ON b.x = a.x;
SELECT a.id, b.id, b.x FROM a, b WHERE a.x = b.x AND b.id > 10 ORDER BY a.id, b.id;
SELECT a.id, b.id FROM a JOIN b ON b.t = a.y;
SELECT a.id, b.id FROM a JOIN b ON a.y = b.t;
SELECT a.id, b.id FROM a JOIN b ON b.n = a.z;
SELECT a.id, b.id FROM a JOIN b ON b.x = a.z;
SELECT a.id, b.id FROM a JOIN b ON b.r = a.x;
SELECT a.id, b.id FROM a JOIN b ON b.t = a.x;
SELECT a.id, b.id FROM a JOIN b ON b.x = a.x * 2 - 1;
SELECT a.id, b.id FROM a LEFT JOIN b ON b.x = a.x + 5;
SELECT a.id, count(b.id) FROM a LEFT JOIN b ON b.x = a.x AND b.r > 1 GROUP BY a.id;
SELECT a.id, e.id FROM a JOIN e ON e.x = a.x;
SELECT a.id, e.id FROM a LEFT JOIN e ON e.x = a.x;
SELECT a.id, b.id, c.id FROM a JOIN b ON b.x = a.x JOIN c ON c.bx = b.x WHERE a.id < 20;
SELECT a.id, b.id FROM a JOIN b ON b.x = a.x AND b.n = a.z;
SELECT a.id, s.id FROM a JOIN (SELECT id, x FROM b WHERE id % 2 = 0 LIMIT 1000) s ON s.x = a.x;
WITH s AS MATERIALIZED (SELECT id, x FROM b WHERE id % 2 = 0) SELECT a.id, s.id FROM a JOIN s ON s.x = a.x;
SELECT a.id, b.id FROM a JOIN b ON b.x = a.x ORDER BY b.id, a.id LIMIT 30;
SELECT a.id, (SELECT count(*) FROM c JOIN b ON b.x = c.bx WHERE c.id = a.id) FROM a WHERE a.id < 15;
SELECT a.id, b.id FROM a JOIN b ON b.x = a.x LIMIT 7;
SELECT a.id, b.id, c.id FROM a LEFT JOIN b ON b.x = a.x + 4 JOIN c ON c.bx = b.x;
SELECT a.id, b.id, c.id FROM a LEFT JOIN b ON b.x = a.x + 4 LEFT JOIN c ON c.bx = b.x WHERE a.id < 25;
SELECT a.id, (SELECT group_concat(b.id) FROM c JOIN b ON b.x = c.bx WHERE c.id > a.x * 3) FROM a WHERE a.id < 12;
SELECT b.id, a.id FROM b JOIN a ON a.y = b.t COLLATE BINARY WHERE b.id < 10;
SELECT count(*), sum(a.id * b.id) FROM a JOIN b ON b.n = a.z AND b.t = a.y;
SELECT a.id, b.id FROM a JOIN b ON a.x = b.x;
SELECT a.id, b.id FROM a LEFT JOIN b ON a.x + 5 = b.x;
SELECT a.id, b.id, c.id FROM a JOIN b ON a.x = b.x JOIN c ON b.x = c.bx WHERE a.id < 20;
SELECT count(*), sum(c.id) FROM c JOIN b USING (id);
SELECT a.id, c.w FROM a JOIN c ON a.x = c.id;
CREATE TABLE bx AS SELECT id, x FROM b;
SELECT a.id, bx.id FROM a NATURAL JOIN bx WHERE a.id < 30;
CREATE INDEX bxi ON bx(x);
SELECT a.id, bx.id FROM a JOIN bx ON a.x = bx.x WHERE a.id < 30;
CREATE TABLE edge(src INTEGER, dst INTEGER);
WITH RECURSIVE s(n) AS (SELECT 1 UNION ALL SELECT n+1 FROM s WHERE n < 200) INSERT INTO edge SELECT n, (n * 7) % 200 + 1 FROM s;
WITH RECURSIVE r(n, d) AS (SELECT 1, 0 UNION SELECT e.dst, r.d + 1 FROM r JOIN edge e ON e.src = r.n WHERE r.d < 40) SELECT count(*), sum(n), max(d) FROM r;
WITH RECURSIVE r(n, d) AS (SELECT 1, 0 UNION SELECT e.dst, r.d + 1 FROM edge e JOIN r ON r.n = e.src WHERE r.d < 40) SELECT count(*), sum(n), max(d) FROM r;
