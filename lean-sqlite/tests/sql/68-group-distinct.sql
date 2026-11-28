-- GROUP BY groups, aggregates with no GROUP BY, SELECT DISTINCT and agg(DISTINCT x), streamed as the join makes rows
CREATE TABLE g(a INTEGER, k, c TEXT, n, t TEXT COLLATE NOCASE, r TEXT COLLATE RTRIM);
INSERT INTO g VALUES(5, 1, 'z', NULL, 'A', 'x'), (3, 1.0, 'y', NULL, 'a', 'x '), (9, 2, 'a', 3, 'b', 'y'),
  (1, 1, 'x', NULL, 'B', 'x  '), (7, 2.0, 'b', 3, 'a', 'y '), (2, 1, 'w', 1, 'c', 'Y'), (4, -0.0, 'q', 1, 'C', 'z'),
  (6, 0.0, 'r', NULL, 'A', 'z'), (8, 0, 's', 2, 'c', ' z'), (10, NULL, 'p', 0, NULL, NULL), (11, NULL, 'o', 5, 'b', 'x');
-- group_concat keeps the scan order within a group; 1 and 1.0, 2 and 2.0, -0.0, 0.0 and 0 group together; NULLs group
SELECT k, count(*), group_concat(a), group_concat(c, '') FROM g GROUP BY k;
SELECT typeof(k), k, group_concat(a) FROM g GROUP BY k;
-- NOCASE and RTRIM keys group under their collation; the group shows its first row's value
SELECT t, count(*), group_concat(a) FROM g GROUP BY t;
SELECT r, count(*), group_concat(a) FROM g GROUP BY r;
SELECT t, r, count(*) FROM g GROUP BY t, r;
SELECT c COLLATE NOCASE AS cc, count(*) FROM g GROUP BY cc;
-- groups come out in key order; ORDER BY and HAVING over them
SELECT k, sum(a) FROM g GROUP BY k ORDER BY 2 DESC;
SELECT t, count(*) FROM g GROUP BY t HAVING count(*) > 1;
SELECT k % 2, max(c), min(c), avg(a), total(n), sum(n) FROM g GROUP BY k % 2;
-- SELECT DISTINCT: each row at its first occurrence, under the result columns' collations
SELECT DISTINCT k FROM g;
SELECT DISTINCT t FROM g;
SELECT DISTINCT r FROM g;
SELECT DISTINCT t, k FROM g;
SELECT DISTINCT c COLLATE NOCASE FROM (SELECT c FROM g UNION ALL SELECT upper(c) FROM g);
SELECT DISTINCT k FROM g ORDER BY k DESC;
SELECT DISTINCT k FROM g LIMIT 3;
SELECT DISTINCT k FROM g LIMIT 2 OFFSET 2;
SELECT DISTINCT count(*) FROM g GROUP BY t;
-- a DISTINCT with a LIMIT stops the scan: the row that would overflow abs() is never computed
CREATE TABLE h(x INTEGER);
INSERT INTO h VALUES(1), (2), (1), (3), (-9223372036854775808);
SELECT DISTINCT abs(x) FROM h LIMIT 3;
-- agg(DISTINCT x): the first occurrence of each value, under x's collation; NULL is one value (json_group_array keeps it)
SELECT count(DISTINCT t), count(DISTINCT r), count(DISTINCT c COLLATE NOCASE), count(DISTINCT k) FROM g;
SELECT group_concat(DISTINCT t), group_concat(DISTINCT r), group_concat(DISTINCT k) FROM g;
SELECT k, count(DISTINCT t), group_concat(DISTINCT t) FROM g GROUP BY k;
SELECT json_group_array(DISTINCT n), json_group_array(n) FROM g;
SELECT sum(DISTINCT n), avg(DISTINCT n), total(DISTINCT k) FROM g;
SELECT count(DISTINCT a) FILTER (WHERE a > 4), group_concat(DISTINCT t) FILTER (WHERE a % 2 = 0) FROM g;
-- bare columns: the first row of the group (with no GROUP BY too)
SELECT a, c, count(*) FROM g;
SELECT a, count(*), sum(a) FROM g WHERE a > 4;
SELECT k, a, c, count(*) FROM g GROUP BY k;
-- with min() or max(): the row where the last of them took a new best value (or a NULL while it had none)
SELECT c, min(n) FROM g;
SELECT c, max(n) FROM g;
SELECT c, min(n), count(*) FROM g GROUP BY k;
SELECT c, min(a), max(a) FROM g;
SELECT c, max(a), min(a) FROM g;
SELECT c, min(a), max(a) FROM g GROUP BY k;
SELECT c, max(c), count(*) FROM g GROUP BY t;
SELECT c, min(DISTINCT n) FROM g;
SELECT c, max(DISTINCT n) FROM g;
SELECT c, min(n) FILTER (WHERE a > 6) FROM g;
SELECT c, min(n) FILTER (WHERE a > 4), max(a) FILTER (WHERE a < 3) FROM g;
SELECT c, max(a) FILTER (WHERE a < 3), min(n) FILTER (WHERE a > 4) FROM g;
SELECT c, min(a) FILTER (WHERE a > 4), count(*) FROM g GROUP BY k;
SELECT c, min(n) FILTER (WHERE a = 100) FROM g;
SELECT c, min(n) FROM g WHERE k = 1;
-- no rows: one group with no GROUP BY (HAVING applies to it), none with GROUP BY
SELECT a, count(*), max(c) FROM g WHERE a > 100;
SELECT count(*) FROM g WHERE a > 100 HAVING count(*) = 0;
SELECT count(*) FROM g WHERE a > 100 HAVING count(*) > 0;
SELECT k, count(*) FROM g WHERE a > 100 GROUP BY k;
SELECT count(*), sum(a) FROM g WHERE 0;
