CREATE TABLE T1(Id INTEGER PRIMARY KEY, Name TEXT);
INSERT INTO t1 VALUES(1, 'a');
Insert Into T1(NAME, ID) Values('b', 2);
SELECT ID, name FROM t1 ORDER BY id;
SELECT T1.Id, t1.NAME from T1;
select "Id", "name", [id], `name` from t1 order by 1;
select 'Id', "Id" from t1 limit 1;
select * from "T1" where "ID" = 1;
select  1  ,
   2
   ;
select /* inline comment */ 3 -- trailing
;
-- a whole line comment
select 4; -- another
/* block
comment */ select 5;
select 6 /* x */ + /* y */ 7;
select t1.id as "my id", id as "select" from t1 order by 1;
create table "order"("group" integer, "select" text, "from" text);
insert into "order" values(1, 's', 'f');
select "group", "select", "from" from "order";
create table [x y](a);
select count(*) from [x y];
SELECT
  id,
  name
FROM
  t1
WHERE
  id > 1
;
select 1;;
;
select 2 ;
select ( 1 ) , ( 2 );
select * from t1 as x where x.id = 1;
select x.* from t1 x;
select t1.* from t1 order by t1.id desc;
select 'a''b', "a""b" from (select 1 as "a""b");
select 1 from t1 where name = 'zzz';
select main.t1.id from t1 limit 1;
create table main.m1(a);
insert into main.m1 values(1);
select * from main.m1;
select sqlite_version() like '3.%';
