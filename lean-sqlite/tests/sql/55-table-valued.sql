create table t(a integer primary key, b text not null default 'x', c real, d);
create index tb on t(b, c desc);
create unique index tc on t(c);
select * from pragma_table_info('t');
select name, type from pragma_table_info('t') where pk = 0 order by name;
select * from pragma_index_list('t') order by name;
select * from pragma_index_info('tb');
select t.name, i.name from sqlite_schema t join pragma_index_list(t.name) i order by 1, 2;
