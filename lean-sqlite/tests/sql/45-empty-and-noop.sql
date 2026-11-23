select 1 where 0;
create table e(a, b);
select * from e;
select count(*), sum(a), total(a), avg(a), min(a), max(a), group_concat(a) from e;
select a, count(*) from e group by a;
select * from e order by a limit 5;
select distinct a from e;
select * from e e1, e e2;
select * from e left join e e2 on 1;
select (select a from e), exists(select 1 from e), 1 in (select a from e), 1 not in (select a from e);
delete from e;
update e set a = 1;
select changes();
insert into e select * from e;
select count(*) from e;
drop table e;
create table e(x);
select count(*) from e union select 5 order by 1;
.headers on
select * from e;
select count(*) as n from e;
select 1 where 0;
select a.x as foo, 5 from e a;
.headers off
select * from e;
