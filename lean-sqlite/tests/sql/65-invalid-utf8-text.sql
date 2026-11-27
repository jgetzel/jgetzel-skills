-- TEXT whose bytes are not valid UTF-8 keeps its bytes (sqlite is bytewise)
create table t(a, b);
insert into t(a) values (cast(x'ff61' as text)), (cast(x'80' as text)), ('a'), (cast(x'c3a9' as text)), (cast(x'e282' as text)),
  (cast(x'61ff' as text)), (cast(x'f09f9880' as text)), (cast(x'c0af' as text)), (cast(x'eda080' as text)), (cast(x'41' as text));
select hex(a), typeof(a), length(a), hex(cast(a as blob)), typeof(cast(a as blob)) from t order by rowid;
select hex(a) from t order by a;
select hex(a) from t order by a desc;
select hex(a), a = 'a', a < 'b', a > 'b', a = cast(a as blob), a < cast(a as blob) from t order by rowid;
select hex(a), a = x'ff61', cast(a as blob) = x'ff61', a = cast(x'ff61' as text), a > 'z', a < 'z' from t order by rowid;
select hex(quote(a)), quote(a) from t where rowid < 4 order by rowid;
select hex(a || 'z'), hex('z' || a), hex(a || a), length(a || a) from t order by rowid;
select hex(upper(a)), hex(lower(a)), hex(trim(a)), hex(ltrim(a, 'a')), hex(rtrim(a, 'a')) from t order by rowid;
select hex(replace(a, 'a', 'b')), hex(substr(a, 1, 1)), hex(substr(a, 2)), instr(a, 'a') from t order by rowid;
select hex(group_concat(a)), hex(group_concat(a, '|')), count(distinct a), hex(min(a)), hex(max(a)) from t;
select hex(printf('%s', a)), hex(printf('%5s|', a)) from t where rowid < 4 order by rowid;
select hex(coalesce(a, 'x')), hex(ifnull(a, 'x')), hex(nullif(a, 'a')), hex(iif(a = 'a', 'y', a)) from t order by rowid;
select a like '%a', a glob '*a*', a like a, a glob a from t order by rowid;
select typeof(cast(x'ff' as text)), length(cast(x'ff' as text)), length(cast(x'ffff' as text)), length(cast(x'80808080' as text)), length(cast(x'6180' as text));
select length(cast(x'c3a980' as text)), length(cast(x'e282ac80' as text)), length(cast(x'f09f98' as text)), length(cast(x'6100ff' as text));
select hex(cast(x'ff61' as text)), hex(cast(cast(x'ff61' as text) as blob)), hex(cast(cast(x'ff61' as text) as text));
select cast(x'ff61' as text) = cast(x'ff61' as text), cast(x'ff61' as text) = cast(x'ff62' as text), cast(x'ff61' as text) < cast(x'ff62' as text);
select cast(x'ff61' as text) < cast(x'c3a9' as text), cast(x'80' as text) < cast(x'c3a9' as text), cast(x'f4' as text) < 'z', cast(x'80' as text) > 'a';
-- chars of the private-use plane that stand for raw bytes here, built from code points and from bytes
select hex(char(1114111)), hex(char(1113984)), length(char(1114111)), hex(char(1114111) || 'a');
create table pp(a); insert into pp values (char(1114111)), (cast(x'f48fbfbf' as text)), ('x');
select hex(a), length(a), a = cast(x'f48fbfbf' as text) from pp;
select hex(upper(char(1114111)));
select cast(x'e2' as text) || cast(x'82ac' as text) = cast(x'e282ac' as text), length(cast(x'e2' as text) || cast(x'82ac' as text)), length(cast(x'e282ac' as text));
create table cc(a); insert into cc values (cast(x'e2' as text) || cast(x'82ac' as text)), (cast(x'e282ac' as text)), (cast(x'e282ac' as text));
select count(distinct a), hex(max(a)) from cc;
select hex(a), count(*) from cc group by a;
select hex(a) from (select a from cc union select cast(x'e282ac' as text));
select hex(group_concat(a)) from cc;
select cast(x'8080' as text) like '_', cast(x'8080' as text) like '__', cast(x'8080' as text) glob '?', cast(x'8080' as text) glob '??', cast(x'e282' as text) like '_', cast(x'e282' as text) like '__', cast(x'e282' as text) glob '?', cast(x'e282' as text) glob '??';
select cast(x'61e282' as text) like 'a_', cast(x'61e282' as text) like 'a__', cast(x'ff80' as text) like '_', cast(x'ff80' as text) like '__', cast(x'c3a980' as text) like '_', cast(x'c3a980' as text) like '__', cast(x'80c3a9' as text) like '__';
-- joined pieces that complete a scalar
select count(distinct x), hex(min(x)) from (select cast(x'e2' as text) || cast(x'82ac' as text) as x union all select cast(x'e282ac' as text));
select hex(x), count(*) from (select cast(x'e2' as text) || cast(x'82ac' as text) as x union all select cast(x'e282ac' as text) union all select 'a') group by x order by x;
select cast(x'e2' as text) || cast(x'82' as text) = cast(x'e282' as text), concat(cast(x'c3' as text), cast(x'a9' as text)) = 'e', concat(cast(x'c3' as text), cast(x'a9' as text)) = cast(x'c3a9' as text), length(concat(cast(x'c3' as text), cast(x'a9' as text)));
select hex(replace(cast(x'c3ffa9' as text), cast(x'ff' as text), '')), replace(cast(x'c3ffa9' as text), cast(x'ff' as text), '') = cast(x'c3a9' as text), length(replace(cast(x'c3ffa9' as text), cast(x'ff' as text), ''));
select hex(concat_ws(cast(x'ff' as text), 'a', 'b')), concat_ws('', cast(x'e2' as text), cast(x'82ac' as text)) = cast(x'e282ac' as text);
select hex(group_concat(x, '')), group_concat(x, '') = cast(x'e282ac' as text) from (select cast(x'e2' as text) as x union all select cast(x'82ac' as text));
select substr(cast(x'e282ac' as text), 1, 1) = cast(x'e282ac' as text), hex(substr(cast(x'61e282ac' as text), 2));
-- stored, read back, rewritten, and indexed
update t set b = rowid;
select hex(a), b from t order by rowid;
create index ta on t(a);
select b from t where a = cast(x'ff61' as text);
select b from t where a > cast(x'80' as text) order by a;
select b from t where a >= cast(x'e282' as text) order by a;
select b from t where a < cast(x'c3a9' as text) order by a desc;
select hex(a) from t indexed by ta order by a;
select hex(a), count(*) from t group by a order by a;
select hex(a) from t where a in (cast(x'ff61' as text), cast(x'80' as text)) order by rowid;
select hex(a) from (select a from t union select cast(x'ff61' as text)) order by 1;
create table u(k text primary key, v);
insert into u values (cast(x'ff' as text), 1), (cast(x'fe' as text), 2), ('x', 3);
select hex(k), v from u order by k;
select v from u where k = cast(x'ff' as text);
insert or replace into u values (cast(x'ff' as text), 4);
select hex(k), v from u order by k;
insert into u values (cast(x'ff' as text), 5);
-- printed
select cast(x'ff61' as text), cast(x'80' as text), cast(x'c3a9' as text);
select cast(x'ff61' as text) as c, 1;
.mode quote
select cast(x'ff61' as text), cast(x'c3a9' as text);
.mode csv
select cast(x'ff61' as text), cast(x'c3a9' as text);
.mode json
select cast(x'ff61' as text), cast(x'c3a9' as text);
.mode insert
select cast(x'ff61' as text), cast(x'c3a9' as text);
.mode line
select cast(x'ff61' as text), cast(x'c3a9' as text);
