-- statements from tests/sql/40-blobs.sql that lean-sqlite does not support (text holding bytes that are not UTF-8)
select instr(x'0102030405', x'0304'), hex(replace(x'010203', x'02', x'aabb')), hex(trim(x'0001', x'00')), upper(x'41');
select hex(x'abcdef' || x'12'), hex(char(0, 1, 2)), unicode(char(0)), length(char(0, 0)), hex(coalesce(null, x'0a'));
