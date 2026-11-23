-- statements from tests/sql/29-long-text-blobs.sql that lean-sqlite does not support (text holding bytes that are not UTF-8)
update t set b = x'ff' || b where id = 2;
select hex(substr(b, 1, 2)), length(b) from t where id = 2;
