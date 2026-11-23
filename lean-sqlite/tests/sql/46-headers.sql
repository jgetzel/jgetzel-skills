.headers on
create table t(id integer primary key, name text, v real);
insert into t values(1,'a',1.5),(2,'b',null),(3,null,3.0);
select * from t;
select id, name as n, v * 2, 'lit', null from t where id < 3;
select count(*), sum(v) from t;
select t.id, t.name from t;
select id from t where 0;
select 1 as "A B", 2 as 'c';
select a.id, b.id from t a join t b on a.id = b.id - 1;
.headers off
select * from t;
.headers on
select typeof(id), typeof(name) from t limit 1;
select x'4142' as blobby, 5 as five;
