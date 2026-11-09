-- sw-lua probe: each library the Lua port would use, checked against what swarm/swarm relies on.
-- Run: nix build --impure -o luaenv --expr '(builtins.getFlake "/etc/nixos").inputs.nixpkgs.legacyPackages.x86_64-linux.luajit.withPackages
--        (p: with p; [ lsqlite3 lua-cjson dkjson luaposix lrexlib-pcre2 luafilesystem argparse luautf8 busted ])'
--      luaenv/bin/luajit sw-lua-probe.lua
-- Prints one line per check; exits 1 on the first failed assert.
local ok_n = 0
local function ok(name, cond, extra)
  assert(cond, name .. (extra and (": " .. tostring(extra)) or ""))
  ok_n = ok_n + 1
  print("ok  " .. name .. (extra and ("  [" .. tostring(extra) .. "]") or ""))
end
local function note(s) print("--  " .. s) end

note(jit.version .. ", " .. _VERSION .. ", 5.2 compat: " .. tostring(pcall(load, "goto x ::x::") and load("goto x ::x::") ~= nil))

-- sqlite3 -> lsqlite3
local sqlite3 = require "lsqlite3"

local dir = require("posix.stdlib").mkdtemp("/tmp/sw-lua-XXXXXX")
local dbf = dir .. "/swarm.db"
local db = assert(sqlite3.open(dbf))
db:busy_timeout(10000)
for r in db:nrows("pragma journal_mode=wal") do ok("sqlite wal", r.journal_mode == "wal") end
assert(db:exec("create table t(id integer primary key autoincrement, n int, s text)") == sqlite3.OK)
ok("sqlite begin immediate", db:exec("begin immediate") == sqlite3.OK)
local st = db:prepare("insert into t(n,s) values(?,?)")
st:bind_values(2 ^ 53, nil) st:step() st:reset()
st:bind_values(1793988107, "x") st:step() st:finalize()
ok("sqlite get_autocommit inside tx", db.get_autocommit == nil or db:get_autocommit() == false,
   db.get_autocommit and "has get_autocommit" or "no get_autocommit: track depth in Lua")
assert(db:exec("commit") == sqlite3.OK)
local rows = {}
for r in db:nrows("select * from t order by id") do rows[#rows + 1] = r end
ok("sqlite NULL column is nil in nrows", rows[1].s == nil)
ok("sqlite int64 2^53 round-trips as a double", rows[1].n == 2 ^ 53, string.format("%.0f", rows[1].n))
ok("sqlite int type is number (no integer subtype in 5.1)", type(rows[2].n) == "number" and math.type == nil)
ok("sqlite last_insert_rowid", db:last_insert_rowid() == 2)
-- a second connection holding begin immediate makes ours wait, then fail with BUSY (Python: OperationalError)
local peer = sqlite3.open(dbf); peer:exec("begin immediate")
db:busy_timeout(300)
local rc = db:exec("begin immediate")
ok("sqlite busy -> SQLITE_BUSY after busy_timeout", rc == sqlite3.BUSY, rc)
peer:exec("rollback"); peer:close()
local ro = sqlite3.open("file:" .. dbf .. "?mode=ro", sqlite3.OPEN_READONLY + sqlite3.OPEN_URI)
ok("sqlite read-only URI open (cmd_state)", ro and select(2, pcall(function() for r in ro:nrows("select count(*) c from t") do return r.c end end)) == 2)
ro:close()

-- json -> lua-cjson (and dkjson for comparison)
local cjson = require "cjson"
ok("cjson null decodes to a truthy lightuserdata (Python None is falsy)", cjson.decode('{"a":null}').a == cjson.null and cjson.null)
ok("cjson empty table encodes as {} (no [] without a marker)", cjson.encode({}) == "{}")
ok("cjson.empty_array exists", cjson.empty_array ~= nil and cjson.encode({ x = cjson.empty_array }) == '{"x":[]}')
ok("cjson array_mt exists", cjson.array_mt ~= nil and cjson.encode(setmetatable({}, cjson.array_mt)) == "[]")
ok("cjson default precision loses 15+ digit ints", cjson.encode(123456789012345678) ~= "123456789012345678", cjson.encode(2 ^ 53))
cjson.encode_number_precision(16)
ok("cjson precision 16: 2^53 exact", cjson.encode(2 ^ 53) == "9007199254740992")
ok("cjson precision 16: 4.85 stays 4.85", cjson.encode(4.85) == "4.85")
ok("cjson escapes / (harmless)", cjson.encode("a/b") == '"a\\/b"')
ok("cjson emits raw UTF-8 (Python ensure_ascii emits \\u)", cjson.encode("é") == '"é"')
ok("cjson invalid json -> error (Python ValueError)", not pcall(cjson.decode, "{nope"))
local dk = require "dkjson"
ok("dkjson null -> nil with nullval=nil", dk.decode('{"a":null,"b":1}', 1, nil).a == nil)

-- subprocess -> luaposix fork/exec/pipe (stdout, stderr, exit code, stdin, cwd, env)
local unistd, wait, poll, fcntl = require "posix.unistd", require "posix.sys.wait", require "posix.poll", require "posix.fcntl"
local function run(argv, o)
  o = o or {}
  local ir, iw = unistd.pipe(); local or_, ow = unistd.pipe(); local er, ew = unistd.pipe()
  local pid = unistd.fork()
  if pid == 0 then
    unistd.dup2(ir, 0); unistd.dup2(ow, 1); unistd.dup2(o.merge and ow or ew, 2)
    for _, f in ipairs { ir, iw, or_, ow, er, ew } do unistd.close(f) end
    if o.cwd and not unistd.chdir(o.cwd) then unistd._exit(127) end
    for k, v in pairs(o.env or {}) do require("posix.stdlib").setenv(k, v) end
    unistd.execp(argv[1], { select(2, unpack(argv)) })
    unistd._exit(127)
  end
  unistd.close(ir); unistd.close(ow); unistd.close(ew)
  if o.input then unistd.write(iw, o.input) end
  unistd.close(iw)
  local out, err, fds = {}, {}, { [or_] = { events = { IN = true } }, [er] = { events = { IN = true } } }
  local deadline = o.timeout and (os.time() + o.timeout)
  while next(fds) do
    local n = poll.poll(fds, o.timeout and 100 or -1)
    if deadline and os.time() > deadline then require("posix.signal").kill(pid, 9) end
    for fd, f in pairs(fds) do
      if f.revents and (f.revents.IN or f.revents.HUP) then
        local s = unistd.read(fd, 65536)
        if not s or #s == 0 then unistd.close(fd); fds[fd] = nil
        else table.insert(fd == or_ and out or err, s) end
      end
    end
  end
  local _, how, code = wait.wait(pid)
  return table.concat(out), table.concat(err), how == "exited" and code or -code
end
local o, e, c = run({ "sh", "-c", 'cat; echo err >&2; pwd; echo "$FOO"; exit 3' }, { input = "in\n", cwd = "/tmp", env = { FOO = "bar" } })
ok("posix run: stdout+stdin+cwd+env", o == "in\n/tmp\nbar\n", o)
ok("posix run: stderr separate", e == "err\n")
ok("posix run: exit code", c == 3)
local big = run({ "sh", "-c", "head -c 300000 /dev/zero; head -c 300000 /dev/zero >&2" })
ok("posix run: 300k on both pipes, no deadlock", #big == 300000)
local _, _, kc = run({ "sleep", "5" }, { timeout = 1 })
ok("posix run: timeout kills", kc == -9)
local _, _, nc = run({ "no-such-binary-xyz" })
ok("posix run: missing binary -> 127 (Python raises OSError)", nc == 127)

-- re -> lrexlib-pcre2
local rex = require "rex_pcre2"
local F = rex.flags()
ok("pcre2 flags: UTF, UCP, DOTALL, MULTILINE", F.UTF and F.UCP and F.DOTALL and F.MULTILINE)
local HEAVY = rex.new([[\b(cabal|stack|ghc|make|cmake|ninja|gradle|mvn|pytest|tox|tsc|spago|purs|playwright|nix\s+(build|flake\s+check)|docker\s+build|(cargo|go|npm|pnpm|yarn|bun)\s+(run\s+)?(build|test|check|clippy|bench|install))\b]])
ok("pcre2 HEAVY_RE alternation + \\b", HEAVY:find("cd x && cargo run test") and not HEAVY:find("cargo fmt"))
local HUNK = rex.new([[^<<<<<<< .*?\n(.*?)^\|\|\|\|\|\|\| .*?\n(.*?)^=======\n(.*?)^>>>>>>> ]], F.DOTALL + F.MULTILINE)
local a, b, cc = HUNK:match("x\n<<<<<<< o\nA\n||||||| b\nB\n=======\nC\n>>>>>>> t\n")
ok("pcre2 HUNK re.S|re.M lazy groups", a == "A\n" and b == "B\n" and cc == "C\n")
local toks = {}
for t in rex.gmatch("héllo, wörld\n", [[\w+|[^\w\s]|\n]], F.UTF + F.UCP) do toks[#toks + 1] = t end
ok("pcre2 TOK with UTF|UCP matches Python's unicode \\w", table.concat(toks, "|") == "héllo|,|wörld|\n", table.concat(toks, "|"))
toks = {}
for t in rex.gmatch("héllo", [[\w+|[^\w\s]|\n]]) do toks[#toks + 1] = t end
ok("pcre2 TOK without UCP splits é into bytes (the trap)", #toks > 1, #toks)
ok("pcre2 lookbehind", rex.find("a-b", [[(?<=-)b]]) == 3)
ok("pcre2 bad user regex -> error (Python re.error)", not pcall(rex.new, "(unclosed"))
local function fullmatch(s, pat) return rex.find(s, "^(?:" .. pat .. ")\\z") ~= nil end
ok("fullmatch via ^(?:..)\\z, not $ (which allows a trailing \\n)", fullmatch("12m", [[(\d+)([smh]?)]]) and not fullmatch("12m\n", [[(\d+)([smh]?)]]))

-- argparse
local argparse = require "argparse"
local ap = argparse("swarm"):command_target("cmd")
local run_ = ap:command("run"); run_:option("--on"); run_:argument("cmd"):args("*")
local post = ap:command("post"); post:argument("to"); post:flag("--urgent"); post:argument("text"):args("+")
local task = ap:command("task"):command_target("act")
local claim = task:command("claim"); claim:argument("id"):convert(tonumber); claim:option("--lease", nil, "2h")
local r = ap:parse { "task", "claim", "69" }
ok("argparse nested subcommands + convert + default", r.cmd == "task" and r.act == "claim" and r.id == 69 and r.lease == "2h")
r = ap:parse { "post", "@all", "--urgent", "hi", "there" }
ok("argparse flag between positionals", r.urgent and r.to == "@all" and #r.text == 2)
r = ap:parse { "run", "--on", "laptop", "--", "make", "-j4" }
ok("argparse -- passes the rest through (REMAINDER via --)", r.on == "laptop" and r.cmd[1] == "make" and r.cmd[2] == "-j4")
local okp, perr = ap:pparse { "run", "make", "-j4" }
ok("argparse: 'run make -j4' without -- is an error (Python REMAINDER accepts it)", not okp, perr)
okp, perr = ap:pparse { "task", "claim" }
ok("argparse missing arg -> pparse false + message", not okp, perr)

-- paths, glob, fnmatch, tempfile, time -> luaposix + luafilesystem
local lfs = require "lfs"
local stdlib, glob, fnm = require "posix.stdlib", require "posix.glob", require "posix.fnmatch"
unistd.link(dir .. "/swarm.db", dir .. "/ln", true)
ok("realpath through a symlink", stdlib.realpath(dir .. "/ln") == stdlib.realpath(dir) .. "/swarm.db")
ok("readlink", unistd.readlink(dir .. "/ln") == dir .. "/swarm.db")
ok("glob", #glob.glob(dir .. "/*.db", 0) == 1)
ok("fnmatch * crosses / like Python", fnm.fnmatch("migrations/*", "migrations/a/b.sql") == 0)
ok("lfs mkdir + attributes", lfs.mkdir(dir .. "/d") and lfs.attributes(dir .. "/d", "mode") == "directory")
ok("lfs.touch keeps an mtime (shutil.copy2)", lfs.touch(dir .. "/swarm.db", 1000, 1000) and lfs.attributes(dir .. "/swarm.db", "modification") == 1000)
ok("sysconf CLK_TCK / PAGESIZE", unistd.sysconf(unistd._SC_CLK_TCK) == 100 and unistd.sysconf(unistd._SC_PAGESIZE) == 4096)
ok("getppid / kill 0", unistd.getppid() > 1 and require("posix.signal").kill(unistd.getpid(), 0) == 0)
local ptime = require "posix.time"
local s0 = require("posix.sys.time").gettimeofday()
ptime.nanosleep { tv_sec = 0, tv_nsec = 200000000 }
local s1 = require("posix.sys.time").gettimeofday()
ok("sub-second sleep (wait --poll 0.2)", (s1.tv_sec - s0.tv_sec) * 1e6 + (s1.tv_usec - s0.tv_usec) >= 190000)
ok("os.time() is an integral double", os.time() == math.floor(os.time()))
ok("os.date %H:%M == time.strftime(localtime)", os.date("%H:%M", 0):match("^%d%d:%d%d$"))
-- datetime.fromisoformat("...Z").timestamp(): os.time{} is local time, so UTC needs the offset back out
local function utc(iso)
  local Y, M, D, h, m, s = iso:match("^(%d+)-(%d+)-(%d+)T(%d+):(%d+):(%d+)")
  local t = os.time { year = Y, month = M, day = D, hour = h, min = m, sec = s, isdst = false }
  local u = os.date("!*t", t); u.isdst = false
  return t + (t - os.time(u))
end
ok("ISO-8601 Z -> epoch", utc("2026-11-08T10:05:00Z") == 1794132300, utc("2026-11-08T10:05:00Z"))

-- strings: byte vs character semantics
ok("('é'):sub(1,1) cuts a UTF-8 char in half ([:80] truncation)", ("é"):sub(1, 1) ~= "é")
local utf8 = require "lua-utf8"
ok("luautf8.sub slices characters", utf8.sub("héllo", 1, 2) == "hé")
ok("string.format %-12s pads bytes not chars", #string.format("%-5s", "é") == 5)
ok("tostring of big doubles goes exponent", tostring(1e15) == "1e+15" and string.format("%d", 1e15) == "1000000000000000")
local s = {}
for i = 1, 50 do s[i] = { k = i % 2, i = i } end
table.sort(s, function(x, y) return x.k < y.k end)
local stable = true
for i = 2, 25 do if s[i].i < s[i - 1].i then stable = false end end
note("table.sort stable on ties: " .. tostring(stable) .. " (Python sorted is always stable)")

-- tests: busted
ok("busted loads", pcall(require, "busted"))

os.execute("rm -rf " .. dir)
print(("%d checks passed"):format(ok_n))
