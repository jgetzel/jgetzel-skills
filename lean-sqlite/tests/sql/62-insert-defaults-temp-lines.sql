CREATE TABLE t(a, b DEFAULT (abs(-9223372036854775808)));
INSERT INTO t VALUES(1,2);
SELECT * FROM t;
INSERT INTO t(a) VALUES(3);
SELECT count(*) FROM t;
INSERT INTO t VALUES(4,5);
SELECT * FROM t;
CREATE TABLE m(a, b);
CREATE INDEX mi ON m(a);
CREATE TEMP TABLE m(a, b);
INSERT INTO main.m VALUES(1,2);
INSERT INTO main.m VALUES(7,8);
SELECT * FROM main.m WHERE a = 7;
SELECT * FROM main.m;
SELECT * FROM temp.m;
UPDATE main.m SET a = 9 WHERE a = 1;
SELECT * FROM main.m WHERE a = 9;
DELETE FROM main.m WHERE a = 7;
SELECT * FROM main.m;
PRAGMA integrity_check;
select 1 /* c */ ; -- x
select 'multi
line;'; select 2
;
select 7.0, .5, 1e5, 0x1f, x'ab', 'a;b', [e;f], 1end;
