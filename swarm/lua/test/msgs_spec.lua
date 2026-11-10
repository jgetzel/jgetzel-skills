-- msgs: two deliveries racing for one inbox (the waiter's and a hook's) show each message once (swarm/model: s4_racy, inboxExact).
local db, msgs = require "swarm.db", require "swarm.msgs"
local stdlib = require "posix.stdlib"
local dir = stdlib.mkdtemp((os.getenv("TMPDIR") or "/tmp") .. "/swarm-spec-XXXXXX")
stdlib.setenv("SWARM_DB", dir .. "/swarm.db")
local c = db.connect()
c:exec("insert into cursor(agent,last_msg_id) values('n',0)")
msgs.post(c, "p", "n", "one")
msgs.post(c, "p", "n", "two")

-- a connection whose first cursor write is preceded by another delivery to n, as when the hook runs in between
local other, raced = nil, false
local racing = setmetatable({ exec = function(_, sql, ...)
  if not raced and sql:find("cursor") then raced = true; other = msgs.deliver(c, "n") end
  return c:exec(sql, ...)
end }, { __index = function(_, k) local f = c[k]; return type(f) == "function" and function(_, ...) return f(c, ...) end or f end })
local mine = msgs.deliver(racing, "n")
assert(raced and other:find("one") and other:find("two"), other)
assert(not mine:find("one") and not mine:find("two"), "shown twice: " .. mine)
assert(c:one("select last_msg_id from cursor where agent='n'").last_msg_id == 2)

msgs.post(c, "p", "n", "three")  -- an uncontested delivery still shows and marks it
assert(msgs.deliver(c, "n"):find("three") and #msgs.unread(c, "n") == 0)
