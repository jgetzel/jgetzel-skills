-- a grouped SELECT ordered by its GROUP BY keys needs no sort: its result columns are computed only for the rows output
CREATE TABLE m(a INTEGER PRIMARY KEY, b INTEGER); INSERT INTO m VALUES(1, -9223372036854775808),(2,5),(3,6); CREATE TABLE t(k INTEGER PRIMARY KEY, v TEXT); INSERT INTO t VALUES(1,'x'),(2,'y'),(3,'z');
SELECT abs(b), sum(a) FROM m GROUP BY a ORDER BY a LIMIT 1 OFFSET 1;
SELECT a, sum(b) FROM m GROUP BY a ORDER BY a;
SELECT a, sum(b) FROM m GROUP BY a ORDER BY a DESC;
SELECT b, count(*) FROM m GROUP BY b, a ORDER BY b;
SELECT b, a, count(*) FROM m GROUP BY b, a ORDER BY b, a LIMIT 2;
SELECT a, count(*) FROM m GROUP BY a ORDER BY a, count(*);
SELECT m.a x, count(*) FROM m GROUP BY m.a ORDER BY m.a LIMIT 1 OFFSET 2;
SELECT a, count(*) FROM m GROUP BY a ORDER BY a NULLS LAST;
SELECT a, count(*) FROM m GROUP BY a HAVING a > 1 ORDER BY a;
create table c(x text collate nocase, y); insert into c values('a',1),('B',2),('A',3),('b',4),(null,5);
select x, sum(y) from c group by x order by x;
select x, sum(y) from c group by x order by x limit 1 offset 1;
select x, count(*) from c group by x order by x desc;
select y, count(*) from c group by y order by y limit 2;
