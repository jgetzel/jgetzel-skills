import LuaLean.Run

/-! Random Lua chunks with the Lean interpreter's results, for `test/luasem.lua` to run under LuaJIT and compare (the
"Decoding Lua" check: the semantics is tested against the implementation). A chunk is a random program over the
subset's numbers, strings, patterns, string.format, tables and table.sort, and its control flow (closures, varargs,
metatables, goto, pcall). `writeCases` writes them as a Lua chunk, `return {{src = .., out = ..}, ..}`, `out` the
dual-number target's results and `single = ..` the single-number target's where they differ; a chunk whose Lean run
needs an effect or more fuel is left out. A user of the library adds chunks of its own (calls of its modules'
functions: swarm/model/SwarmModel/LuaCases.lean). -/

namespace Lua.Gen

abbrev G := StateM StdGen

def rnd (n : Nat) : G Nat := modifyGet fun g => randNat g 0 n
def pick {α} [Inhabited α] (l : List α) : G α := return l.getD (← rnd (l.length - 1)) default
def chance (k : Nat) : G Bool := return (← rnd (k - 1)) == 0
def str (cs : String) (n : Nat) : G String := do
  let mut r := ""
  for _ in [0:← rnd n] do r := r.push (← pick cs.toList)
  return r
def commas (l : List String) : String := ", ".intercalate l

/-- a Lua string literal: printable ASCII as itself, the rest \ddd -/
def q (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' || c == '\\' then "\\" ++ c.toString
    else if c.toNat < 32 || c.toNat > 126 then "\\" ++ String.ofList (Num.padLeft '0' 3 (Num.digits c.toNat))
    else c.toString) ++ "\""

-- ---------- numbers and strings ----------

def numLit : G String := pick
  ["0", "1", "2", "3", "7", "10", "-1", "-4", "100", "255", "0.5", "2.25", "-1.5", "1e3", "1e15", "1e16", "2^53",
   "123456789012", "0x1f", "3.0", "1e-5", "0.1", "1/3", "1e300", "-0.0", "65", "97"]

def strLit : G String := do return q (← str "ab c1.%-()[]^$xA" 7)

mutual
partial def numE (d : Nat) : G String := do
  if d == 0 then return ← numLit
  match ← rnd 9 with
  | 0 | 1 | 2 => return s!"({← numE (d - 1)} {← pick ["+", "-", "*", "/", "%", "^", "+", "*"]} {← numE (d - 1)})"
  | 3 => return s!"-({← numE (d - 1)})"
  | 4 => return s!"math.{← pick ["floor", "abs", "ceil"]}({← numE (d - 1)})"
  | 5 => return s!"math.{← pick ["max", "min"]}({← numE (d - 1)}, {← numE (d - 1)})"
  | 6 => return s!"#{← strE (d - 1)}"
  | 7 => return s!"(tonumber({← strE (d - 1)}) or {← numLit})"
  | _ => numLit

partial def strE (d : Nat) : G String := do
  if d == 0 then return ← if ← chance 4 then pure s!"tostring({← numLit})" else strLit
  match ← rnd 11 with
  | 0 | 1 => return s!"({← strE (d - 1)} .. {← if ← chance 3 then numE (d - 1) else strE (d - 1)})"
  | 2 => return s!"({← strE (d - 1)}):sub({← pick ["1", "2", "-1", "-3", "0", "4", "10", "-10"]}{← pick ["", ", 2", ", -2", ", 0", ", 3", ", 100"]})"
  | 3 => return s!"({← strE (d - 1)}):rep({← pick ["0", "1", "2", "3"]}{← pick ["", ", \"-\""]})"
  | 4 => return s!"({← strE (d - 1)}):{← pick ["upper", "lower", "reverse"]}()"
  | 5 => return s!"tostring({← numE (d - 1)})"
  | 6 => return s!"(({← strE (d - 1)}):gsub({← patLit}, {← pick ["\"<%0>\"", "\"\"", "\"%%\"", "\"-\""]}))"
  | 7 => return s!"(({← strE (d - 1)}):match({← patLit}) or \"\")"
  | 8 => return s!"string.char({← pick ["72", "105", "0", "255", "10", "34"]}, {← pick ["65", "92", "127"]})"
  | _ => strLit

/-- a Lua pattern, mostly well formed -/
partial def pat : G String := do
  let piece : G String := do
    let single ← pick [".", "a", "b", "x", "%a", "%d", "%s", "%w", "%p", "%l", "%u", "%x", "%A", "%S", "%W", "%%",
      "%.", "%(", "[ab]", "[^a]", "[a-c]", "[%a_]", "[%d.]", "[]a]", "[^%s]", " ", "1", "(", ")"]
    match ← rnd 9 with
    | 0 => return single ++ (← pick ["*", "+", "-", "?"])
    | 1 => return s!"({single}{← pick ["", "*", "+", "-"]})"
    | 2 => return "()"
    | 3 => return ← pick ["%b()", "%f[%w]", "%f[%s]", "%1", "%b[]"]
    | _ => return single
  let mut r := if ← chance 5 then "^" else ""
  for _ in [0:(← rnd 4) + 1] do r := r ++ (← piece)
  if ← chance 6 then r := r ++ "$"
  if ← chance 12 then r := r ++ (← pick ["[", "%", "(", ")", "[a"])
  return r

partial def patLit : G String := do return q (← pat)
end

def subject : G String := do return q (← str "ab  x1.()[]%A-^$" 10)

-- ---------- chunks ----------

def helper : String :=
  "local function P(...) local r = {pcall(...)} if r[1] then return r end return \"err\" end\n"

def arith : G String := do
  let es ← (List.range 4).mapM fun _ => do pure s!"P(function() return {← numE 3} end)"
  return helper ++ s!"return {commas es}"

def strings : G String := do
  let es ← (List.range 4).mapM fun _ => do pure s!"P(function() return {← strE 3} end)"
  return helper ++ s!"return {commas es}"

def patterns : G String := do
  let s ← subject
  let p ← patLit
  let repl ← pick ["\"<%0>\"", "\"%1-%%\"", "\"x\"", "{a = \"A\", [\"(\"] = 1, b = false}",
    "function(x) return x .. \"!\" end", "function() return false end", "function(a, b) return b end", "\"%2\""]
  let init ← pick ["1", "2", "-2", "0", "5", "20", "-20"]
  let mx ← pick ["", ", 1", ", 2", ", 0"]
  return helper ++ s!"local s, p = {s}, {p}
local g = \{}
local ok = pcall(function() for a, b in s:gmatch(p) do g[#g + 1] = \{a, b}; if #g > 20 then break end end end)
return P(string.find, s, p), P(string.find, s, p, {init}), P(string.match, s, p, {init}), P(string.gsub, s, p, {repl}{mx}), ok and g or \"err\", P(string.find, s, p, 1, true)"

def fmtSpec : G (String × String) := do
  let flags ← pick ["", "", "-", "0", "+", " ", "#", "-0", "+0"]
  let w ← pick ["", "", "1", "5", "12"]
  let pr ← pick ["", "", ".0", ".1", ".3", ".14", ".17"]
  let conv ← pick ['d', 'i', 'x', 'X', 'c', 'e', 'E', 'f', 'g', 'G', 's', 'q', 'd', 'f', 'g', 's']
  let arg ← match conv with
    | 'c' => pick ["65", "97", "48", "126"]
    | 's' | 'q' => if ← chance 4 then numE 1 else strE 1
    | 'd' | 'i' | 'x' | 'X' => pick ["0", "7", "-3", "255", "1e15", "3.7", "-2.5", "42", "123456789", "2^31",
      "-2^31 - 1", "2^32 + 65", "-2^63", "2^53"]
    | _ => numE 1
  let pr := if conv == 'c' then "" else pr
  return (s!"%{flags}{w}{pr}{conv}", arg)

def formats : G String := do
  let mut es := []
  for _ in [0:4] do
    let mut f := ""
    let mut as := []
    for _ in [0:(← rnd 2) + 1] do
      let (sp, a) ← fmtSpec
      f := f ++ (← str "ab :%" 2 |>.map fun s => s.replace "%" "%%") ++ sp
      as := as ++ [a]
    es := es ++ [s!"P(string.format, {q f}, {commas as})"]
  return helper ++ s!"return {commas es}"

def tables : G String := do
  let n ← rnd 9
  let strs ← chance 2
  let elems ← (List.range n).mapM fun _ => if strs then strLit else pick ["1", "2", "3", "5", "8", "13", "-1", "0.5", "21", "3"]
  let cmp ← pick ["a > b", "a < b", (if strs then "#a < #b" else "(a % 3) < (b % 3)"), "a <= b"]
  let recs ← (List.range (← rnd 8)).mapM fun i => do pure s!"\{k = {← pick ["1", "2", "3"]}, n = {i}}"
  let pos ← pick ["1", "math.min(2, #t + 1)", "math.max(#t, 1)", "#t + 1"]
  return helper ++ s!"local t = \{{commas elems}}
local u = \{}
for i, v in ipairs(t) do u[i] = v end
table.sort(t)
local okc = P(table.sort, u, function(a, b) return {cmp} end)
local w = \{{commas recs}}
table.sort(w, function(a, b) return a.k < b.k end)
local names = \{}
for i, r in ipairs(w) do names[i] = r.n end
table.insert(t, {pos}, {if strs then "\"z\"" else "99"})
local r1 = table.remove(t, {pos})
local r2 = table.remove(t)
return t, okc, u, names, r1, r2, table.concat(t, \",\"), #t, select('#', unpack(t)), table.maxn(t), \{select({← pick ["1", "2", "-1"]}, unpack(t))}"

def ctrl : G String := do
  let a ← pick ["1", "10", "0", "-2", "1.5"]
  let b ← pick ["10", "1", "5", "-2", "3.5"]
  let st ← pick ["1", "-1", "2", "-3", "0.5", "-0.25"]
  let x ← pick ["0", "3", "-7", "\"5\""]
  let nn ← pick ["0", "5", "12"]
  let k ← pick ["1", "2", "3", "-1", "-2"]
  let args ← pick ["1, nil, 3", "", "nil", "\"a\", \"b\", \"c\", \"d\""]
  return s!"local acc = \{}
for i = {a}, {b}, {st} do acc[#acc + 1] = i; if #acc > 50 then break end end
local function va(...) local n = select('#', ...); local ok, v = pcall(select, {k}, ...); return n, ok, v, \{...} end
local mk = function() local c = {x}; return function(d) c = c + d; return c end end
local f1, f2 = mk(), mk()
f1(1); f1(2); f2(10)
local Base = \{}; Base.__index = Base
function Base.new(x) return setmetatable(\{x = x}, Base) end
function Base:get() return self.x end
local Sub = setmetatable(\{}, \{__index = Base}); Sub.__index = Sub
function Sub:get2() return self:get() * 2 end
local o = setmetatable(\{x = {x}}, Sub)
local k, s = 0, 0
while k < {nn} do k = k + 1; if k % 3 == 0 then goto cont end; s = s + k; ::cont:: end
local r = 0
repeat local q = r * 2; r = r + 1 until q > {nn}
local ok, e = pcall(function() error(\{tag = {x}}) end)
local ok2 = pcall(function() local t = nil; return t.x end)
local ok3, e3 = pcall(error, \"msg\", 0)
local t = \{n = 1, [2] = \"two\", \"one\", {x}}
local keys = 0
for _ in pairs(t) do keys = keys + 1 end
local idx = setmetatable(\{}, \{__index = function(_, key) return key .. \"?\" end})
return acc, va({args}), f1(0), f2(0), o:get2(), Base.new(5):get(), s, r, ok, e.tag, ok2, ok3, e3, t, keys, idx.foo, rawget(idx, \"foo\"), type(o), type(nil), type(type), #t, next(\{}), (\"x\"):len()"

def numbers : G String := do
  let ns ← (List.range 4).mapM fun _ => do
    return q (← pick ["  12  ", "0x1F", "1e5", "1e", ".5", "5.", "-0", "inf", "-inf", "1e500", "0x", "", " ", "abc", "12a",
      "+3", "- 3", "0x1p4", "1E+2", "007", "\t8\n", "0.1e-3", "123456789012345678", "9007199254740993",
      "1e1048575", "1e1048576", "0x1p-1048576"])
  let bs ← (List.range 3).mapM fun _ => do
    pure s!"tonumber({q (← str "0129azAZ" 4)}, {← pick ["2", "16", "36", "10"]})"
  let vs ← (List.range 4).mapM fun _ => numE 2
  return helper ++ s!"return {commas (ns.map fun s => s!"tonumber({s})")}, {commas bs}, {commas (vs.map fun v => s!"P(function() local x = {v}; return tostring(x), x .. \"\", x == math.floor(x), x < 1, -x end)")}"

/-- where the targets and the CPUs may differ (DESIGN.md "Targets"), through locals: the parser folds constants -/
def diffs : G String := do
  let n : G String := pick ["0", "-0.0", "-4", "3", "-1", "0.5", "-2.5", "2147483647", "-2147483648", "2147483648",
    "65536", "-65536", "46341", "0/0", "1/0", "1e300", "123456789012", "0.1", "7"]
  let vs ← (List.range 3).mapM fun _ => n
  let op ← pick ["*", "*", "+", "-", "%", "/"]
  let s ← pick ["-0", "0", "2147483648", "2147483647", "-2147483648", "0x7fffffff", "1e9", "-0.0", "4294967296"]
  return helper ++ s!"local a, b, c = {commas vs}
local x = tonumber({q s})
return P(function() return a {op} b, (a {op} b) * c, a * b * c, -a, a % b, b % a end),
  P(function() return math.max(a, b), math.min(a, b), math.max(a, b, c), math.min(c, b, a) end),
  P(function() return a + 1, a - 1, a * 2, a * a, math.abs(a), math.floor(a / 2), math.ceil(a / 2) end),
  P(function() return 1 / math.ceil(a / 2), 1 / math.floor(a), math.floor(a), math.ceil(a) end),
  P(function() return x, x * -1, x * 0, -x, x + 0, x == a end),
  P(function() return tostring(a * b), (a * b) .. \"\", (\"%.14s\"):format(a * b), (\"%g\"):format(a * b) end)"

/-- metamethods read when the operation runs: `__index` and `__newindex` as functions, tables, chains and wrong
values, set before or after `setmetatable` and removed after; `__call` (a function, a builtin, a callable table,
which LuaJIT does not follow); raw access past them -/
def metas : G String := do
  let k ← pick ["\"a\"", "\"b\"", "\"zz\"", "1", "2", "nil", "0/0", "1.5", "true"]
  let v ← pick ["1", "\"v\"", "nil", "false", "{}"]
  let idx ← pick ["function(_, key) return tostring(key) .. \"?\" end", "{a = \"A\", [1] = \"one\", zz = 0}", "proto",
    "setmetatable({}, {__index = proto})", "\"str\"", "nil", "5", "function() error(\"no\") end"]
  let nidx ← pick ["function(_, key, val) log[#log + 1] = tostring(key) .. \"=\" .. type(val) end", "store", "nil",
    "function(o, key, val) rawset(o, key, val); log[#log + 1] = \"raw\" end", "setmetatable({}, {__newindex = store})",
    "\"str\"", "5"]
  let cl ← pick ["function(self, ...) return select('#', ...), self == t, ... end", "rawequal", "{}", "nil",
    "setmetatable({}, {__call = function() return 1 end})", "function(_, a) if a == nil then return nil end return a end"]
  let set := s!"mt.__index = {idx}; mt.__newindex = {nidx}; mt.__call = {cl}"
  let late ← chance 2
  return helper ++ s!"local log, store = \{}, \{}
local proto = \{a = \"pa\", b = false, zz = \"pz\"}
local mt, t = \{}
{if late then "" else set}
t = setmetatable(\{a = 1}, mt)
{if late then set else ""}
local r1 = P(function() return t[{k}], t.a, t.zz, rawget(t, {k}) end)
local r2 = P(function() t[{k}] = {v}; t.a = 2; t.new = 3; return rawget(t, {k}), rawget(t, \"new\"), t.a, t.new end)
local r3 = P(function() return t({k}, {v}) end)
local r4 = P(function() local n = 0; for x in t do n = n + 1; if n > 3 then break end end; return n end)
local r5 = P(function() rawset(t, \"q\", 7); return t.q, rawget(t, \"zz\") end)
mt.__index = nil
mt.__newindex = nil
local r6 = P(function() t.later = 4; return t.zz, t.b, rawget(t, \"later\") end)
return r1, r2, r3, r4, r5, r6, log, store, proto, t"

-- the metamethods whose task has not landed stop the run where LuaJIT would call them, and only there; `__len` on
-- a table is never called (LuaJIT 2.1 without its 5.2 compatibility)
#guard [("local mt = {} local t = setmetatable({}, mt) mt.__add = 1 return pcall(function() return t + 1 end)",
      "effect metamethod __add"),
    ("local t = setmetatable({}, {__tostring = 1, __eq = 1, __lt = 1, __le = 1, __concat = 1, __unm = 1, __add = 1}) return t == t, pcall(function() return t < 1 end)",
      "ok:true,false,\"c:1: attempt to compare table with number\""),
    ("return #setmetatable({}, {__len = function() return 5 end})", "ok:0"),
    ("local t = setmetatable({}, {__eq = 1}) return t == {}", "effect metamethod __eq"),
    ("local t = setmetatable({}, {}) getmetatable(t).__lt = 1 return t < t", "effect metamethod __lt"),
    ("return -setmetatable({}, {__unm = 1})", "effect metamethod __unm"),
    ("return setmetatable({}, {__concat = 1}) .. \"x\"", "effect metamethod __concat"),
    ("return tostring(setmetatable({}, {__tostring = 1}))", "effect metamethod __tostring"),
    ("return (\"%s\"):format(setmetatable({}, {__tostring = 1}))", "effect metamethod __tostring"),
    ("return getmetatable(setmetatable({}, {__metatable = 1}))", "effect metamethod __metatable"),
    ("local t = setmetatable({}, {__metatable = 1}) return pcall(setmetatable, t, {})", "effect metamethod __metatable"),
    ("return setmetatable({}, {__mode = \"k\"})", "effect metamethod __mode"),
    ("return setmetatable(_G, {})", "effect setmetatable(_G)")].all fun (src, out) =>
  runCase (fun _ => none) .dual [] src.toList == out

/-- doubles outside the integer ranges, and calls that want an integer: LuaJIT leaves the C cast to the CPU, so the
semantics stops the run (`argIntN`), which the `#guard` checks; no chunk of `chunk` is one, it would be left out -/
def rangeXs : List String :=
  ["2^31", "-2^31 - 1", "2^32 + 65", "2^63", "2^64", "-2^63", "1e300", "1/0", "-1/0", "0/0", "2^53"]
def rangeCalls : List String :=
  ["(\"%d\"):format(x)", "(\"%x\"):format(x)", "(\"%c\"):format(x)", "(\"abcdef\"):sub(x)", "(\"abcdef\"):sub(2, x)",
   "select(x, \"a\", \"b\")", "(\"x\"):rep(x)", "string.char(x)", "(\"abc\"):byte(x)", "math.ldexp(1, x)",
   "tonumber(\"1\", x)", "table.move({}, 1, x, 1)"]
def rangeChunk (x call : String) : String := s!"local x = {x}\nreturn pcall(function() return {call} end)"

-- in range only: `%d` and `%x` (int64) of a value up to 2^63 in magnitude
#guard rangeCalls.all fun c => rangeXs.all fun x =>
  (runCase (fun _ => none) .dual [] (rangeChunk x c).toList).startsWith "effect" ==
    !((c.startsWith "(\"%d" || c.startsWith "(\"%x") && ["2^31", "-2^31 - 1", "2^32 + 65", "-2^63", "2^53"].contains x)

/-- the rest of the libraries: math's libm functions through `%.12g` (libms differ in the last bits, and the
committed cases run on three), its exact ones as they are; table.move, foreach, foreachi, getn, new and clear;
tonumber with a base, select and tostring at their corners -/
def libs : G String := do
  let n : G String := pick ["0", "-0.0", "1", "-1", "0.5", "-2.5", "3", "7", "1e300", "5e-324", "2^53", "0/0", "1/0",
    "-1/0", "\"4\"", "100", "-7.25", "1e-310", "2^-1074 * 3", "6"]
  let x ← n
  let y ← n
  let f1 ← pick ["exp", "log", "log10", "sin", "cos", "tan", "asin", "acos", "atan", "sinh", "cosh", "tanh", "sqrt"]
  let f2 ← pick ["pow", "atan2", "log"]
  let e ← pick ["0", "1", "-1", "1.5", "-1.5", "52", "-1074", "1023", "1024", "-2000", "\"3\""]
  let tn ← (List.range 3).mapM fun _ => do
    pure s!"P(tonumber, {q (← str "-+ 0xX19afzAZ" 5)}, {← pick ["2", "8", "10", "16", "36", "10.5", "\"16\"", "1", "37", "nil"]})"
  let tn2 ← pick ["\"ffffffffffffffffffff\", 16", "\"-0\", 16", "\"-80000000\", 16", "\"7fffffff\", 16",
    "\"80000000\", 16", "\"1e5\", 10", "\" 0x1F \", 16", "\"-0x10\", 16", "\"+12\", 8", "15, 16", "\"0x\", 16",
    "\"zz\", 36", "\"- 1\", 10", "\"1\\t\", 2"]
  let elems ← (List.range ((← rnd 5) + 1)).mapM fun _ => pick ["1", "2", "\"a\"", "false", "3.5"]
  let el := commas elems
  let ix : G String := pick ["1", "2", "3", "0", "-1", "1.5", "\"2\"", "5", "-1.5", "2.5", "\" 3.5 \"", "4"]
  let mv ← (List.range 2).mapM fun _ => do pure s!"{← ix}, {← ix}, {← ix}"
  let sel ← pick ["\"#x\"", "\"#\"", "-1", "-3", "2.5", "\"2\"", "4", "-4", "0"]
  let un ← pick ["1, 7997", "1, 7998", "1, 7996, nil", "-3996, 4000", "5, 1"]
  return helper ++ s!"local x, y = {x}, {y}
local function g(v) return (\"%.12g\"):format(v) end
local t = \{{el}}
local acc = \{}
local r1 = P(table.foreachi, t, function(i, v) acc[#acc + 1] = i; if v == false then return \"stop\", 2 end end)
local r2 = P(table.foreach, \{{el}}, function(k, v) acc[#acc + 1] = v; if v == 2 then return k end end)
local n0 = table.getn(t)
local m1 = P(table.move, t, {mv.getD 0 ""})
local m2 = P(table.move, \{{el}}, {mv.getD 1 ""}, \{9})
local rm = \{{el}}
local r3 = P(table.remove, rm, {← ix})
local new, clear = require(\"table.new\"), require(\"table.clear\")
local z = new(4, 2); z[1] = x; z.k = y
local w = setmetatable(\{1, 2, k = 3}, \{}); clear(w)
return P(function() return g(math.{f1}(x)), g(math.{f2}(x, y)), g(math.{f1}(y)), g(math.log(x)) end),
  P(function() return math.fmod(x, y), math.modf(x), math.frexp(y) end), P(math.ldexp, x, {e}), P(math.deg, x),
  P(math.rad, y), math.pi, P(math.fmod, y, x), P(math.modf, y), {commas tn}, P(tonumber, {tn2}), r1, r2, acc, n0, m1, m2, r3, rm,
  table.new == new, table.clear == clear, z, w, getmetatable(w) ~= nil, P(tostring), P(tonumber), P(tostring, nil),
  P(tonumber, nil), P(select, {sel}, \"a\", \"b\", \"c\"), P(function() return select(\"#\", unpack(\{}, {un})) end)"


-- ---------- error values: where LuaJIT reports them, and how it names the operands ----------

/-- tokens joined by a space or, at random, a newline; never one before `(`, which LuaJIT reads as a new statement -/
def layout (toks : List String) : G String := do
  let mut r := ""
  for t in toks do
    let nl ← chance 3
    if r != "" then r := r ++ (if t == "(" then " " else if nl then "\n" else " ")
    r := r ++ t
  return r

/-- something to index or call: a local, an upvalue, a global, a field, a call's value, a constant, a parenthesis -/
def prefixOp : G (List String) := pick [["t"], ["up"], ["gx"], ["g", ".", "a", ".", "b"], ["f", "(", ")"],
  ["(", "nil", ")"], ["(", "\"a\"", ")"], ["(", "{", "}", ")"], ["g", "[", "1", "]"], ["(", "t", ")"], ["s"],
  ["g", ".", "n"], ["g", "[", "k", "]"]]
def valueOp : G (List String) := do
  if ← chance 3 then pick [["nil"], ["\"a\""], ["{", "}"], ["1"], ["true"]] else prefixOp

/-- a statement that raises a runtime error, or not -/
def errStat : G (List String) := do
  let p ← prefixOp
  let v ← valueOp
  let w ← valueOp
  match ← rnd 16 with
  | 0 => return ["return"] ++ p ++ [".", "x"]
  | 1 => return ["local", "r", "="] ++ p ++ ["[", "k", "]", ",", "1"]
  | 2 => return ["local", "r", "="] ++ p ++ [":", "m", "(", ")"]
  | 3 => return ["local", "r", "="] ++ p ++ ["(", "1", ")"]
  | 4 => return ["return"] ++ p ++ ["(", "1", ")"]
  | 5 => return ["return"] ++ v ++ [← pick ["+", "*", "-", "%", "..", "<", "<=", ">", "/", "^"]] ++ w
  | 6 => return ["local", "r", "=", ← pick ["-", "#"]] ++ v
  | 7 => return p ++ [".", "x", "=", "1"]
  | 8 => return ["g", ".", "x", ",", "t", ".", "y", ",", "up", "[", "1", "]", "=", "1", ",", "2", ",", "3"]
  | 9 => pick [["local", "r", "=", "string", ".", "rep", "(", ")"], ["local", "r", "=", "s", ":", "rep", "(", "{", "}", ")"],
      ["local", "r", "=", "s", ":", "rep", "(", "1", ",", "{", "}", ")"], ["return", "string", ".", "sub", "(", ")"],
      ["local", "r", "=", "math", ".", "floor", "(", "\"z\"", ")"], ["local", "r", "=", "tostring", "(", ")"],
      ["local", "r", "=", "select", "(", "0", ")"], ["local", "r", "=", "(", "\"%d\"", ")", ":", "format", "(", "\"q\"", ")"],
      ["local", "r", "=", "setmetatable", "(", "{", "}", ",", "1", ")"], ["local", "r", "=", "string", ".", "char", "(", "300", ")"],
      ["local", "r", "=", "table", ".", "concat", "(", "{", "{", "}", "}", ")"], ["local", "q", "=", "string", ".", "rep", "local", "r", "=", "q", "(", ")"],
      ["local", "r", "=", "(", "\"%y\"", ")", ":", "format", "(", "1", ")"], ["local", "r", "=", "s", ":", "find", "(", "\"(\"", ")"],
      ["local", "r", "=", "next", "(", "{", "}", ",", "1", ")"], ["local", "r", "=", "ipairs", "(", ")"],
      ["local", "r", "=", "table", ".", "sort", "(", "{", "1", ",", "2", "}", ",", "3", ")"]]
  | 10 => pick [["error", "(", "\"m\"", ")"], ["error", "(", "\"m\"", ",", "2", ")"], ["error", "(", "\"m\"", ",", "0", ")"],
      ["error", "(", "{", "}", ")"], ["error", "(", "5", ")"], ["return", "error", "(", "\"m\"", ")"], ["error", "(", ")"]]
  | 11 => pick [["assert", "(", "false", ")"], ["assert", "(", "nil", ",", "\"m\"", ")"], ["assert", "(", "false", ",", "7", ")"],
      ["assert", "(", "1", "==", "2", ",", "{", "}", ")"]]
  | 12 => pick [["for", "i", "=", "1", ",", "t", "do", "end"], ["for", "i", "=", "s", ",", "2", "do", "end"],
      ["for", "k", "in", "1", "do", "end"], ["for", "k", "in", "next", ",", "5", "do", "end"], ["for", "k", "in", "pairs", "(", "t", ")", "do", "end"]]
  | 13 => pick [["local", "function", "h", "(", ")", "error", "(", "\"m\"", ",", "2", ")", "end", "local", "r", "=", "h", "(", ")"],
      ["local", "function", "h", "(", ")", "error", "(", "\"m\"", ",", "2", ")", "end", "return", "h", "(", ")"],
      ["local", "function", "h", "(", ")", "return", "string", ".", "rep", "(", ")", "end", "local", "r", "=", "h", "(", ")"],
      ["local", "function", "h", "(", ")", "return", "t", ".", "x", "end", "local", "r", "=", "h", "(", ")"],
      ["local", "function", "h", "(", "o", ")", "return", "o", ".", "x", "end", "local", "r", "=", "pcall", "(", "h", ")"]]
  | 14 => return ["function", "t", ".", "a", "(", ")", "end"]
  | _ => return ["local", "r", "=", "{"] ++ v ++ [",", "x", "="] ++ w ++ ["}"]

/-- statements raising errors, each under pcall, and the values they raised; now and then one not caught -/
def errors : G String := do
  let mut src := "local up\nlocal g = {a = {}, n = 5}\nlocal E = {}\nlocal function c(f) local ok, e = pcall(f) E[#E + 1] = ok and \"ok\" or e end\n"
  for _ in [0:(← rnd 5) + 2] do
    src := src ++ s!"c(function()\nlocal t, k, f, s = nil, \"x\", function() end, \"x\"\n{← layout (← errStat)}\nend)\n"
  if ← chance 4 then return src ++ "local t, s = nil, \"x\"\ndo\n" ++ (← layout (← errStat)) ++ "\nend\nreturn E"
  return src ++ "return E"

/-- pairs, next and table.foreach where the result does not hang on the order, which in LuaJIT is its layout and
strings' hashes, seeded per process (`Tbl.rank`): what a traversal visits, keys cleared before it, values cleared and
changed during it, nested traversals, next by hand; #t of tables without holes (one border), trimmed, with other keys -/
def traverse : G String := do
  let key : G String := pick ["1", "2", "3", "4", "7", "100", "-1", "0", "1.5", "2^31", "-0.0", "\"a\"", "\"b\"",
    "\"cc\"", "\"1\"", "true", "false"]
  let ks ← (List.range (← rnd 10)).mapM fun _ => key
  let dels ← (List.range (← rnd 4)).mapM fun _ => key
  let n ← rnd 8
  let trim ← rnd 3
  let other ← pick ["", "s.x = 1", "s[0] = 0", "s[-1] = 1", "s[1.5] = 1", "s[2^31] = 1"]
  return helper ++ s!"local t = \{}
for i, k in ipairs(\{{commas ks}}) do t[k] = i end
for _, k in ipairs(\{{commas dels}}) do t[k] = nil end
local n, sum, keys = 0, 0, \{}
for k, v in pairs(t) do n = n + 1; sum = sum + v; keys[#keys + 1] = type(k) .. \":\" .. tostring(k) end
table.sort(keys)
local m, k = 0, next(t)
while k ~= nil do m = m + 1; k = next(t, k) end
local nn = 0
for _ in pairs(t) do for _ in pairs(t) do nn = nn + 1 end end
for k, v in pairs(t) do if v % 2 == 0 then t[k] = nil else t[k] = v * 10 end end
local after = \{}
for k, v in pairs(t) do after[#after + 1] = type(k) .. \":\" .. tostring(k) .. \"=\" .. v end
table.sort(after)
local f = 0
table.foreach(t, function(_, v) f = f + v end)
for k in pairs(t) do t[k] = nil end
local s = \{}
for i = 1, {n} do s[i] = i end
for _ = 1, {trim} do s[#s] = nil end
{other}
return n, sum, keys, m, nn, after, f, next(t), t, #s, #\{1, 2, nil}, #\{nil}, s"

-- #t of a table with more than one border stops the run (LuaJIT's answer is its array part's size: 2 for the second,
-- the least border 0), and so does `next` from a key the table does not hold where LuaJIT's array part (an
-- integer) or a dead node (a key it had) may; a key cleared during a traversal is held until a key is added
#guard [("return #{1, nil, 3}", "effect #t of a table with holes"),
    ("local t = {1, 2} t[1] = nil return #t", "effect #t of a table with holes"),
    ("local t = {1, nil, 3} return pcall(table.insert, t, 4)", "effect #t of a table with holes"),
    ("return unpack({1, nil, 3}, 1, 3)", "ok:1,nil,3"),
    ("return table.concat({1, nil, 3}, \",\", 1, 1)", "ok:\"1\""),
    ("return #{1, 2, nil}, #{n = 1}, #{nil}", "ok:2,0,0"),
    ("return pcall(next, {}, \"a\")", "ok:false,\"invalid key to 'next'\""),
    ("return pcall(next, {}, 1)", "effect next of a key not in the table"),
    ("return pcall(next, {nil, nil}, 1)", "effect next of a key not in the table"),
    ("local t = {a = 1} t.a = nil return next(t, \"a\")", "ok:nil"),
    ("local t = {a = 1} t.a = nil t.b = 2 return next(t, \"a\")", "effect next of a key not in the table")].all
  fun (src, out) => runCase (fun _ => none) .dual [] src.toList == out

-- the order is opaque: run, it is the insertion order; no proof can compute it
example : True := by
  fail_if_success (have : Tbl.rank 0 0 .nil = 0 := rfl)
  fail_if_success (have : Tbl.rank 0 0 .nil = 0 := by decide)
  trivial

/-- load and loadstring: a source and its chunk name, errors raised in the chunk, a reader's pieces, the mode -/
def loads : G String := do
  let body ← pick ["return 1 + 2", "return ...", "local t = nil\nreturn t.x", "error('m')", "error('m', 2)",
    "ld_g = (ld_g or 0) + 1 return ld_g", "return select('#', ...)", "local a, b = ...\nreturn b, a", "return",
    "\n\nreturn nil .. 1", "return function(y) return y * 2 end", "return loadstring('return 5, ...')(...)",
    "return (loadstring('error(\"in\")', '=inner'))()", "local x = 1\n\n\nerror({x})", "return 1 + #(...)",
    "local t = {}; (t).x, (t)['y'] = ...; return t.x, t.y"]
  let long := "long name of a chunk, longer than forty-five bytes at least"
  let name ← pick ["", ", nil", ", \"=n\"", ", \"@f.lua\"", s!", {q long}", s!", \"={long}{long}\"",
    s!", \"@d/{long}/{long}.lua\"", ", \"a\\nb\"", ", \"\"", ", 12", ", \"=\""]
  let mode ← pick ["", "", "", ", \"t\"", ", \"b\"", ", \"bt\"", ", \"\""]
  let name := if mode != "" && name == "" then ", nil" else name
  let cut ← rnd body.length
  let pieces := [(body.take cut).toString, (body.drop cut).toString] ++ (if ← chance 4 then ["", "error()"] else [])
  let src ← match ← rnd 4 with
    | 0 => pure s!"load({q body}{name}{mode})"
    | 1 => pure s!"load(rd({commas (pieces.map q)}){name})"
    | 2 => pure s!"load(rd({commas (pieces.map q)}){name}, nil, \{})"
    | _ => pure s!"loadstring({q body}{name}{mode})"
  let args ← pick ["", ", 1, 2", ", nil, 'ab'", ", 'xyz'"]
  return s!"local function rd(...) local p, i = \{...}, 0 return function() i = i + 1 return p[i] end end
ld_g = nil
local f, e = {src}
if not f then return e end
return pcall(f{args})"

/-- the modules under test/mods, by both their names -/
def modNames : List String := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"]

/-- require and dofile of the modules in test/mods, through a package.path that finds them, LuaJIT run from
lua-lean/: each chunk forgets what an earlier one loaded -/
def files : G String := do
  let (path, pfx) ← pick [("test/?.lua", "mods."), ("test/nope/?.lua;test/?.lua", "mods."), (";;test/?.lua;", "mods."),
    ("test/mods/?.lua", ""), ("test/x?y/?.lua;test/mods/?.lua", "")]
  let mut src := s!"package.path = {q path}\nfor _, m in ipairs(\{{commas (modNames.flatMap fun m => [q m, q ("mods." ++ m)])}}) do package.loaded[m] = nil end\nlocal R = \{}\n"
  for _ in [0:(← rnd 4) + 1] do
    let m := pfx ++ (← pick modNames)
    let st ← match ← rnd 6 with
      | 0 => pure s!"R[#R + 1] = \{pcall(require, {q m})}"
      | 1 => pure s!"R[#R + 1] = \{pcall(function() return require({q m}) end)}"
      | 2 => pure s!"R[#R + 1] = \{pcall(dofile, \"test/mods/{← pick modNames}.lua\")}"
      -- not one whose load fails: LuaJIT leaves a light userdata there (DESIGN.md, known gaps)
      | 3 => do let m := pfx ++ (← pick ["a", "b", "c", "d", "g", "i", "j"]); pure s!"R[#R + 1] = \{require({q m}), package.loaded[{q m}]}"
      | 4 => pure s!"R[#R + 1] = \{pcall(function() return require({q (pfx ++ "j")}).f(21), require({q (pfx ++ "j")}) == require({q (pfx ++ "j")}) end)}"
      | _ => pure s!"R[#R + 1] = \{require == _G.require, require(\"string\") == string, require(\"_G\") == _G, require(\"package\") == package}"
    src := src ++ st ++ "\n"
  return src ++ "return R"

/-- one of the chunks above -/
def chunk : G String := do
  if ← chance 8 then return ← errors
  match ← rnd 13 with
  | 0 => arith
  | 1 => strings
  | 2 | 3 => patterns
  | 4 => formats
  | 5 => tables
  | 6 => ctrl
  | 7 | 8 => diffs
  | 9 => metas
  | 10 => libs
  | 11 => traverse
  | 12 => loads
  | _ => numbers

/-- `n` chunks from `gen` (each with the modules to load first, from `srcs` through package.path `path`) and their
results, to `file` -/
def writeCases (gen : G (String × List String)) (srcs : String → Option Block) (n seed : Nat)
    (file : System.FilePath) (path : String := "./?.lua") : IO Unit := do
  let mut g := mkStdGen seed
  let mut cases : Array String := #[]
  let mut skipped : List String := []
  for _ in [0:n] do
    let ((src, mods), g') := gen.run g
    g := g'
    let out := runCase srcs .dual mods src.toList path
    let out1 := runCase srcs .single mods src.toList path
    if out.startsWith "ok:" || out.startsWith "error:" then
      let single := if out1 == out then "" else s!", single = {String.ofList (serStr out1.toList)}"
      cases := cases.push s!"\{src = {String.ofList (serStr src.toList)}, out = {String.ofList (serStr out.toList)}{single}},"
    else skipped := out :: skipped
  IO.FS.writeFile file ("return {\n" ++ "\n".intercalate cases.toList ++ "\n}\n")
  IO.eprintln s!"{cases.size} cases, {skipped.length} left out{if skipped.isEmpty then "" else s!" (first: {skipped.getLast!})"}"

end Lua.Gen
