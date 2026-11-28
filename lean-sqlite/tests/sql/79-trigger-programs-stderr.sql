-- a trigger program is compiled once per statement and run on each row: what it reads is read again on each row
create table t(a integer primary key, b); create table lg(x, y);
create trigger t1 after insert on t when (select count(*) from lg) < 3 begin insert into lg select new.a, count(*) from t; end;
insert into t values(1, 1), (2, 2), (3, 3), (4, 4), (5, 5); select * from lg; select changes();
drop trigger t1; delete from lg;
create trigger t2 before insert on t begin select raise(ignore) where new.b < 0; insert into lg values(new.a, last_insert_rowid()); end;
insert into t values(6, 1), (7, -1), (8, 2); select * from t order by a; select * from lg; select changes();
drop trigger t2; delete from lg;
-- nested and mutually recursive triggers (a trigger running does not fire again)
create table u(k integer primary key, n); create table v(k integer primary key, n);
create trigger tu after insert on u begin insert into v values(new.k, new.n * 10); insert into lg values('u', new.k); end;
create trigger tv after insert on v begin insert or ignore into u values(new.k + 100, new.n); update lg set y = y + 1000 where x = 'u'; end;
insert into u values(1, 1), (2, 2); select * from u order by k; select * from v order by k; select * from lg order by x, y;
drop trigger tu; drop trigger tv; delete from lg;
-- a DEFAULT in a body's column-list INSERT, and OR REPLACE writing a NOT NULL column's DEFAULT
create table d(a, b not null default (2 * 21), c default 'c');
create trigger td after insert on t begin insert into d(a) values(new.a); insert or replace into d values(new.a, null, new.b); end;
insert into t values(20, 1), (21, 2); select * from d order by rowid;
create table dw(a primary key, b not null default (7 + 1)) without rowid;
insert or replace into dw values(1, null), (2, 5), (1, null); select * from dw;
update or replace dw set b = null where a = 2; select * from dw;
drop trigger td;
-- changes() and a RETURNING statement whose rows fire triggers
create trigger tc after update on t begin insert into lg values(new.a, changes()); end;
update t set b = b + 1 where a > 5 returning a, b; select * from lg order by x;
drop trigger tc; delete from lg;
-- a body statement that does not compile raises its error when a row fires it
create trigger te after insert on t when new.a > 1000 begin insert into lg values(nosuch); end;
insert into t values(1001, 1); select count(*) from t where a = 1001;
insert into t values(31, 1), (1002, 1); select count(*) from t where a in (31, 1002);
select count(*) from t where a in (31, 1001, 1002);
drop trigger te;
-- UPDATE and DELETE bodies, and a view's INSTEAD OF trigger, over many rows
create table q(k integer primary key, n); insert into q values(1, 0), (2, 0), (3, 0);
create view vq as select k, n from q;
create trigger tq instead of insert on vq begin update q set n = n + new.n where k = new.k; delete from q where n > 5; end;
insert into vq values(1, 1), (2, 2), (1, 3), (2, 4), (3, 1); select * from q order by k;
create trigger tw after delete on q begin insert into lg values('del', old.k); end;
delete from q; select * from lg;
