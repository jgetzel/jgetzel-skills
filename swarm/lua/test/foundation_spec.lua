-- util, re, json, proc against the Python behaviour they stand in for.
local util, re, json, proc = require "swarm.util", require "swarm.re", require "swarm.json", require "swarm.proc"

-- util
assert(util.dur("90s") == 90 and util.dur("30m") == 1800 and util.dur("2h") == 7200 and util.dur("5") == 5)
local ok, e = pcall(util.dur, "2d")
assert(not ok and e.exit == 1)
assert(util.ago(util.now() - 3725) == "1h02m" and util.ago(util.now() - 125) == "2m" and util.ago(nil) ~= nil)
assert(util.d(1e15) == "1000000000000000")
assert(util.cut("héllo", 2) == "hé")
assert(util.shquote("a b") == "'a b'" and util.shquote("it's") == "'it'\"'\"'s'" and util.shquote("") == "''")
assert(util.shjoin({ "make", "-j4", "x y" }) == "make -j4 'x y'")
assert(table.concat(util.split("  a  b "), "|") == "a|b" and table.concat(util.split("a,,b", ","), "|") == "a||b")
assert(#util.splitlines("a\nb\n") == 2 and #util.splitlines("") == 0)
assert(util.basename("/x/wt") == "wt" and util.basename("/x/") == "" and util.dirname("/x/y") == "/x" and util.join("/a", "b", "c") == "/a/b/c")

-- re
local m = re.search("(a)(x)?b", "zzab")
assert(m[0] == "ab" and m[1] == "a" and m[2] == nil and m.s == 3)
assert(re.match("b", "ab") == nil and re.match("a", "ab")[0] == "a")
assert(re.fullmatch("(\\d+)([smh]?)", "12m") and not re.fullmatch("(\\d+)([smh]?)", "12m\n"))
assert(table.concat(re.findall("\\w+|[^\\w\\s]|\\n", "héllo, wörld\n"), "|") == "héllo|,|wörld|\n")
assert(table.concat(re.findall("^worktree (.*)$", "worktree /a\nx\nworktree /b\n", re.M), "|") == "/a|/b")
local g = re.findall("(a)(b)?", "a ab")
assert(g[1][1] == "a" and g[1][2] == "" and g[2][2] == "b")
local hunk = "^<<<<<<< .*?\\n(.*?)^\\|\\|\\|\\|\\|\\|\\| .*?\\n(.*?)^=======\\n(.*?)^>>>>>>> "
local hs = {}
for h in re.finditer(hunk, "x\n<<<<<<< o\nA\n||||||| b\nB\n=======\nC\n>>>>>>> t\n", re.S + re.M) do hs[#hs + 1] = h end
assert(#hs == 1 and hs[1][1] == "A\n" and hs[1][2] == "B\n" and hs[1][3] == "C\n")
assert(#re.findall("x*", "é") == 2)  -- empty matches step over a whole character
assert(re.sub("[^\\w.-]", "_", "my repo/é") == "my_repo_é")
assert(re.escape("main red: run (1)") == "main\\ red\\:\\ run\\ \\(1\\)" and re.match(re.escape("a.b"), "axb") == nil)
assert(not pcall(re.compile, "(unclosed"))

-- json
local j = json.decode('{"a":null,"b":[],"c":[1,null],"d":"x/y"}')
assert(j.a == nil and #j.b == 0 and j.c[1] == 1)
assert(json.encode(j.b) == "[]" and json.encode(json.array()) == "[]" and json.encode({}) == "{}")
assert(json.encode(2 ^ 53) == "9007199254740992" and json.encode(4.85) == "4.85" and json.encode("x/y") == '"x/y"')
local bad, err = json.decode("{nope")
assert(bad == nil and err)

-- proc
local o, er, code = proc.exec({ "sh", "-c", 'cat; echo err >&2; pwd; echo "$FOO"; exit 3' },
  { input = "in\n", cwd = "/", env = { FOO = "bar" } })
assert(o == "in\n/\nbar\n" and er == "err\n" and code == 3, o)
local big = ("x"):rep(300000)
o = proc.exec({ "sh", "-c", "cat; head -c 300000 /dev/zero >&2" }, { input = big })
assert(o == big)  -- 300 KB in, out and on stderr at once: no deadlock
assert(select(3, proc.exec({ "no-such-binary-xyz" })) == 127)
assert(select(3, proc.exec({ "true" }, { input = big })) == 0)  -- a child that never reads its stdin
assert(proc.run({ "false" }) == nil and proc.run({ "echo", "hi" }) == "hi\n")
assert(proc.git({ "--version" }):match("^git version"))
o = proc.exec({ "sh", "-c", "echo out; echo err >&2" }, { merge = true })
assert(o == "out\nerr\n")
