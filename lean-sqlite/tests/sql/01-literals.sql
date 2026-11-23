select 1, -1, +5, 0, 007, 1234567890123, 9223372036854775807, -9223372036854775808;
select 9223372036854775808, -9223372036854775809, 0x10, 0xFF, 0x7fffffffffffffff;
select 1.5, .5, 5., 1e3, 1E-3, 1.5e+10, 3.0, -0.0, 100.0;
select 'abc', 'it''s', '', 'multi
line', 'tab	x';
select x'414243', x'', typeof(x'00'), length(x'0102');
select null, typeof(null), true, false, typeof(true);
select 1 as a, 'x' as b, 2.5 as "quoted alias";
select typeof(1), typeof(1.0), typeof('a'), typeof(x'01'), typeof(null);
.headers on
select 1 as one, 'two' as two, null as three, 4.5;
select 1+1, 'a'||'b', -(-3);
.headers off
select 'unicode: ' || 'é日本語', length('é日本語'), hex('é');
