create table t(id integer primary key autoincrement, name text, score real, data blob, note);
insert into t values(1, 'ann', 3.5, x'00ff', null), (2, 'bob "b"', 10.0, null, 'multi
line'), (3, 'çé', -1e100, x'41', 'a,b');
.headers on
select * from t;
.mode csv
select * from t;
.mode column
select id, name, score from t;
.mode box
select id, name, score from t;
.mode table
select id, name from t;
.mode markdown
select id, name from t;
.mode json
select * from t;
.mode line
select id, name from t where id < 3;
.mode quote
select * from t;
.mode insert out
select * from t;
.mode tabs
select id, name from t;
.mode html
select id, name from t where id = 1;
.mode list
.headers off
.nullvalue <null>
select note from t;
.separator ; |
select id, name from t;
.separator |
.width 5 10
.mode column
select id, name from t;
.mode list
.print hello world
.tables
.indexes
create index tn on t(name);
create view v as select name from t;
create trigger tr after insert on t begin select 1; end;
create table "odd name"(x);
insert into "odd name" values('q');
.dump
