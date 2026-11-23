create table a(x);
create table bb(x);
create table ccc(x);
create table dddd(x);
create table e(x);
create table ffffffffffff(x);
create table g(x);
create table hh(x);
create table iii(x);
create table jjjjjjjjjjjjjjjjjjjjj(x);
create table k(x);
create table llllll(x);
create table m(x);
create table nnnnnnnnn(x);
create table o(x);
create table pp(x);
create table qqqqqqqqqqqqqqqqqqqqqq(x);
create table r(x);
create table s(x);
.tables
.tables %e%
create index ix on a(x);
create index iy on bb(x);
create temp table tt(x);
create index temp.tix on tt(x);
.indexes
.indexes i
.tables b%
create table t(a); create index ti on t(a); create table t2(b); create index t2i on t2(b); create view tv as select 1;
insert into t values(1); insert into t2 values(2);
.dump t%
.dump --data-only t2
.dump t2 tv
.separator ", "
select 1, 2;
.nullvalue "a b"
select null;
.print "a  b" c 'd  e' "x\ty"
.separator "\t"
select 1, 2;
.separator '|'
.nullvalue ''
.echo on
select 3;
.echo off
select 4;
