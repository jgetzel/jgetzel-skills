import LuaLean.Run

/-! Random Lua chunks with the Lean interpreter's results, for `test/luasem.lua` to run under LuaJIT and compare (the
"Decoding Lua" check: the semantics is tested against the implementation). A chunk is a random program over the
subset's numbers, strings, patterns, string.format, tables and table.sort, and its control flow (closures, varargs,
metatables, goto, pcall, coroutines). `writeCases` writes them as a Lua chunk, `return {{src = .., out = ..}, ..}`, `out` the
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

/-- the operators' metamethods (`__add`…`__pow`, `__unm`, `__concat`) on either operand or both, x's before y's: a
function of what it is given, one returning nothing or two values, one raising an error, a builtin, a callable table,
values that cannot be called; set before or after `setmetatable`; a yield inside one; `__len`, which LuaJIT 2.1 does
not call on a table -/
def opMetas : G String := do
  let mm (tag : String) : G String := pick [s!"function(a, b) return \"{tag}\" .. type(a) .. type(b) end",
    "function() end", s!"function(a, b) return \"{tag}\", 2 end", "rawequal", "function(a, b) error(\"mm\") end",
    "string.rep", "math.floor",
    s!"setmetatable(\{}, \{__call = function(_, a, b) return \"{tag}\" .. type(b) end})", "5", "{}", "nil",
    "function(a, b) if type(b) == \"number\" then return b * 2 end return a == b end"]
  let evs := ["__add", "__sub", "__mul", "__div", "__mod", "__pow", "__unm", "__concat", "__len"]
  let sets ← (List.range 8).mapM fun i => do
    pure s!"mt{(← rnd 1) + 1}.{← pick evs} = {← mm s!"m{i}"}"
  let late ← chance 2
  let opnd : G String := pick ["t", "t", "t", "u", "u", "u", "s", "x", "n", "b", "z"]
  let ex : G String := do
    match ← rnd 5 with
    | 0 => return s!"-{← opnd}"
    | 1 => return s!"#{← opnd}"
    | 2 => return s!"{← opnd} .. {← opnd} .. {← opnd}"
    | _ => return s!"{← opnd} {← pick ["+", "-", "*", "/", "%", "^", ".."]} {← opnd}"
  let es ← (List.range 8).mapM fun _ => ex
  let co := if ← chance 3 then "\nlocal w = coroutine.wrap(function() return setmetatable({}, {__add = function(a, b) return coroutine.yield(b) end}) + 5 end)\nlocal y1 = w()\nlocal y2 = w(7)\nr[#r + 1] = {y1, y2}" else ""
  return s!"local mt1, mt2 = \{}, \{}
{if late then "" else "\n".intercalate sets}
local t, u = setmetatable(\{1, 2}, mt1), setmetatable(\{}, {← pick ["mt2", "mt1"]})
{if late then "\n".intercalate sets else ""}
local s, x, n, b, z = \"10\", \"x\", 3, true, nil
local r = \{}
{"\n".intercalate (es.map fun e => s!"r[#r + 1] = \{pcall(function() return {e} end)}")}{co}
return r"

-- an operator's metamethod that is not a function is called through `__call`, or fails with no place; `__unm` gets
-- its operand twice; `..` goes right to left (as LuaJIT's BC_CAT); a metamethod's first value, nil if none
#guard [("local mt = {} local t = setmetatable({}, mt) mt.__add = 1 return pcall(function() return t + 1 end)",
      "ok:false,\"attempt to call a number value\""),
    ("return pcall(function() return -setmetatable({}, {__unm = 1}) end)", "ok:false,\"attempt to call a number value\""),
    ("return pcall(function() return setmetatable({}, {__sub = {}}) - 1 end)", "ok:false,\"attempt to call a table value\""),
    ("return 2 ^ setmetatable({}, {__pow = setmetatable({}, {__call = function(_, a, b) return type(a), type(b) end})})",
      "ok:\"number\""),
    ("local t = setmetatable({}, {__unm = function(a, b) return rawequal(a, b), select('#', a, b) end}) return -t", "ok:true"),
    ("local t = setmetatable({}, {__concat = function(a, b) return type(a) .. type(b) end}) return 1 .. t .. 'x' .. 2, t .. t, 'a' .. 'b' .. t",
      "ok:\"1tablestring\",\"tabletable\",\"astringtable\""),
    ("local t = setmetatable({}, {__add = function() end}) return t + 1, '3' + t", "ok:nil,nil")].all fun (src, out) =>
  runCase (fun _ => none) .dual [] src.toList == out
/-- comparison and conversion metamethods: `__eq` of one metatable or two (the same function, another, none), a table
against itself; `__lt` and `__le`, without `__le` (`not (b < a)`), each with any result, a wrong value (a number, a
callable table, NaN) or an error, and through table.sort; `__tostring` through tostring, print and `%s`/`%q`,
returning a string, a number, several values, a boolean, or failing; a yield in each; `__metatable` in getmetatable
and setmetatable -/
def compares : G String := do
  let eqs := ["function(x, y) log[#log + 1] = \"eq\" .. x.n .. y.n; return x.n == y.n end", "function() return nil end",
    "function() return 0 end", "5", "callable", "rawequal", "function() error(\"bad eq\") end",
    "function() return false, true end", "nil", "0/0"]
  let lts := ["function(x, y) log[#log + 1] = \"lt\" .. x.n .. y.n; return x.n < y.n end", "function() return \"yes\" end",
    "function() return nil end", "callable", "true", "nil", "function(x) error({code = x.n}) end",
    "function() error(\"lt\", 2) end", "string.rep"]
  let eq ← pick eqs
  let lt ← pick lts
  let le ← pick ["nil", "nil", "function(x, y) log[#log + 1] = \"le\" .. x.n .. y.n; return x.n <= y.n end", "callable",
    "function() return 1 end"]
  let ts ← pick ["function(o) return \"T\" .. o.n end", "function(o) return o.n end", "function(o) return o.n * 1.5, \"x\" end",
    "function(o) io.write(\"<\" .. o.n .. \">\"); return \"w\" end", "function() return nil end", "function() return true end",
    "function() error(\"ts\") end", "function() error(\"ts2\", 2) end", "callable", "5", "type", "string.rep"]
  let m2 ← pick ["m1", "{__eq = f_eq, __lt = f_lt, __le = f_le, __tostring = f_ts}",
    s!"\{__eq = {← pick eqs}, __lt = {← pick lts}}", "{}", "nil"]
  let prot ← pick ["nil", "false", "\"locked\"", "0", "{}"]
  let late ← chance 3
  let yop ← pick ["x < x", "x <= x", "x == setmetatable({}, getmetatable(x))", "tostring(x)", "(\"%s\"):format(x)",
    "print(x)", "table.sort({x, x, x})"]
  return s!"local function Q(...) return \{pcall(...)} end
local log = \{}
local callable = setmetatable(\{}, \{__call = function(self, x, y) log[#log + 1] = \"call\"; return y == nil end})
local f_eq, f_lt, f_le, f_ts = {eq}, {lt}, {le}, {ts}
local m1 = {if late then "{}" else "{__eq = f_eq, __lt = f_lt, __le = f_le, __tostring = f_ts}"}
local m2 = {m2}
local a, b, c = setmetatable(\{n = 1}, m1), setmetatable(\{n = 2}, m2), setmetatable(\{n = 1}, m1)
{if late then "m1.__eq, m1.__lt, m1.__le = f_eq, f_lt, f_le; rawset(m1, \"__tostring\", f_ts)" else ""}
local r1 = Q(function() return a == b, a ~= b, b == a, a == c, a == a, a == \{}, rawequal(a, c), a == 1 end)
local r2 = Q(function() return a < b end)
local r3 = Q(function() return a <= b, b >= a end)
local r4 = Q(function() return a > c, c >= a, b > a end)
local r5 = Q(function() return a < 1, a <= \"x\" end)
local r6 = Q(function() local t = \{b, a, c}; table.sort(t); return t[1].n, t[2].n, t[3].n end)
local r7 = Q(function() return tostring(a), select(\"#\", tostring(a)) end)
local r8 = Q(function() return (\"%s|%6s|%.2s|%q|%d\"):format(a, c, a, c, 3) end)
local r9 = Q(print, \"p\", a, 2.5, c)
local co = coroutine.wrap(function()
  local x = setmetatable(\{n = 3}, \{__lt = function() coroutine.yield(\"lt\"); return true end,
    __eq = function() coroutine.yield(\"eq\"); return 1 end, __tostring = function() coroutine.yield(\"ts\"); return \"s\" end})
  return {yop}
end)
local r10 = Q(function() return co(), co(), co(), co() end)
m1.__metatable = {prot}
local r11 = Q(function() local g = getmetatable(a); return g == m1, g, getmetatable(b) == m2 end)
local r12 = Q(setmetatable, a, m2)
local r13 = Q(function() setmetatable(b, m1); return rawequal(getmetatable(b), m1), getmetatable(b) end)
m1.__metatable = nil
local r14 = Q(function() return getmetatable(a) == m1, getmetatable(setmetatable(a, nil)) end)
return log, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14"

-- `<=` without `__le` is `not (y < x)`; `__eq` and `__lt` want both metamethods the same (one metatable, or two with
-- the same function); tostring is a tail call of `__tostring`, all its values; `%s` and `%q` take its first;
-- `__metatable` hides the metatable and protects it
#guard [("local m = {__lt = function(a, b) return a.n < b.n end} local x, y = setmetatable({n = 1}, m), setmetatable({n = 2}, m) return x <= y, y <= x, x >= y, pcall(function() return x < setmetatable({n = 0}, {__lt = m.__lt}) end)",
      "ok:true,false,false,true,false"),
    ("local f = function() return 1 end local m = {__eq = f} return setmetatable({}, m) == setmetatable({}, {__eq = f}), setmetatable({}, m) == setmetatable({}, {__eq = function() return 1 end}), setmetatable({}, m) == setmetatable({}, {}), setmetatable({}, {}) == setmetatable({}, m)",
      "ok:true,false,false,false"),
    ("local t = setmetatable({}, {__tostring = function() return 1, 2 end}) return select('#', tostring(t)), (\"%s|%q\"):format(t, t), pcall(tostring, setmetatable({}, {__tostring = 5}))",
      "ok:2,\"1|\\0341\\034\",false,\"attempt to call a number value\""),
    ("return getmetatable(setmetatable({}, {__metatable = \"locked\"})), pcall(setmetatable, setmetatable({}, {__metatable = false}), {}), pcall(getmetatable)",
      "ok:\"locked\",false,false,\"bad argument #1 to '?' (value expected)\"")].all fun (src, out) =>
  runCase (fun _ => none) .dual [] src.toList == out

-- a table's `__len` is never called (LuaJIT 2.1 without its 5.2 compatibility); a metatable on _G stops the run
#guard [("local t = setmetatable({}, {__tostring = 1, __eq = 1, __lt = 1, __le = 1, __concat = 1, __unm = 1, __add = 1}) return t == t, pcall(function() return t < 1 end)",
      "ok:true,false,\"c:1: attempt to compare table with number\""),
    ("return #setmetatable({}, {__len = function() return 5 end})", "ok:0"),
    ("return setmetatable(_G, {})", "effect setmetatable(_G)")].all fun (src, out) =>
  runCase (fun _ => none) .dual [] src.toList == out

/-- weak tables (`__mode`), its objects held by locals, so LuaJIT's collector frees none of them: a mode of `k`, `v`,
both, none, cut by a NUL or not a string, set before `setmetatable` or after; reads by key, raw and through
`__index`, writes through `__newindex`, `#t`, `ipairs`, `pairs` (counted, by the order no proof knows) and the table
library. A read that could see an entry the collector freed stops the run (the `#guard` below), so a chunk that
makes one is left out -/
def weaks : G String := do
  let key : G String := pick ["o1", "o2", "f", "\"s\"", "1", "2", "3", "true", "2.5"]
  let val : G String := pick ["o1", "o2", "f", "\"x\"", "7", "false", "nil", "\"y\"", "8"]
  let mode ← pick ["\"k\"", "\"k\"", "\"v\"", "\"kv\"", "\"vk\"", "\"\"", "\"x\"", q "k\x00v", q "v\x00k", "1", "\"K\""]
  let late ← chance 3
  let step : G String := do
    match ← rnd 12 with
    | 0 | 1 | 2 => return s!"t[{← key}] = {← val}"
    | 3 | 4 => return s!"R[#R + 1] = P(function() return V(t[{← key}]) end)"
    | 5 => return s!"R[#R + 1] = P(function() return V(rawget(t, {← key})) end)"
    | 6 => return "R[#R + 1] = P(function() return #t end)"
    | 7 => return "R[#R + 1] = P(function() local n, ty = 0, {} for k, v in pairs(t) do n = n + 1; ty[#ty + 1] = type(k) .. type(v) end table.sort(ty) return n, table.concat(ty, \" \") end)"
    | 8 => return "R[#R + 1] = P(function() local n = 0 for i, v in ipairs(t) do n = n + i end return n end)"
    | 9 => return s!"m.{← pick ["__index", "__newindex"]} = {← pick ["function(_, k) R[#R + 1] = \"mm\" end", "nil", "{}"]}"
    | 10 => return s!"R[#R + 1] = P(function() return {← pick ["table.concat(t, \",\", 1, 2)", "V(unpack(t, 1, 2))", "V(table.remove(t))", "table.insert(t, 1, \"z\")"]} end)"
    | _ => return "R[#R + 1] = P(function() return rawequal(setmetatable(t, m), t), getmetatable(t) == m end)"
  let pre ← (List.range ((← rnd 4) + 1)).mapM fun _ => step
  let post ← (List.range ((← rnd 5) + 1)).mapM fun _ => step
  return helper ++ s!"local o1, o2, f = \{}, \{n = 1}, function() return 1 end
local function V(x) if x == o1 then return \"o1\" elseif x == o2 then return \"o2\" elseif x == f then return \"f\" end return x end
local R = \{}
local m = {if late then "{}" else s!"\{__mode = {mode}}"}
local t = setmetatable(\{}, m)
{"\n".intercalate pre}
{if late then s!"m.__mode = {mode}" else ""}
{"\n".intercalate post}
return R, o1, o2, f()"

-- weak tables: a key held by the reader keeps its entry, and a weak string or number is never freed; a read that
-- could see an object the collector freed stops the run (a weak value read, `next` to a weak entry, `#t` over weak
-- values), and so does a change that would hide one (a mode changed or cleared, a weak table's metatable changed,
-- a metatable on package.loaded)
#guard [("local o = {} local t = setmetatable({}, {__mode = \"k\"}) t[o] = o; t.s = \"x\"; t[1] = o return t[o] == o, t.s, rawget(t, o) == o, t[1] == o, #t, select(\"#\", ipairs(t))",
      "ok:true,\"x\",true,true,1,3"),
    ("local t = setmetatable({\"a\", \"b\", s = 2}, {__mode = \"kv\"}) local n = 0 for k, v in pairs(t) do n = n + 1 end return n, #t, t[1], table.concat(t)",
      "ok:3,2,\"a\",\"ab\""),
    ("local o = {} local t = setmetatable({o}, {__mode = \"k\\0v\"}) return t[1] == o, #t", "ok:true,1"),
    ("local o = {} local t = setmetatable({o}, {__mode = 1}) return t[1] == o, #t", "ok:true,1"),
    ("local o = {} local t = setmetatable({o}, {__mode = \"v\"}) return t[1]", "effect weak table: a value the collector may free"),
    ("local o = {} local m = {} local t = setmetatable({o}, m) m.__mode = \"v\" return rawget(t, 1)", "effect weak table: a value the collector may free"),
    ("local o = {} local t = setmetatable({}, {__mode = \"k\"}) t[o] = 1 return next(t)", "effect next in a weak table"),
    ("local o = {} local t = setmetatable({o}, {__mode = \"v\"}) return pcall(next, t, 1)", "effect next in a weak table"),
    ("local t = setmetatable({{}}, {__mode = \"v\"}) return #t", "effect #t of a weak table"),
    ("local m = setmetatable({__index = function() return 1 end}, {__mode = \"v\"}) return setmetatable({}, m).x", "effect weak table: a value the collector may free"),
    ("local o = {} local t = setmetatable({x = o}, {__mode = \"v\", __newindex = rawset}) t.x = 1 return t.x", "effect weak table: a value the collector may free"),
    ("local m = {__mode = \"k\"} m.__mode = \"v\"", "effect __mode changed"),
    ("local m = {__mode = \"k\"} m.__mode = \"k\" return getmetatable(setmetatable({}, m)) == m", "ok:true"),
    ("local m = {__mode = \"k\"} require(\"table.clear\")(m)", "effect __mode changed"),
    ("local t = setmetatable({}, {__mode = \"k\"}) return setmetatable(t, nil)", "effect setmetatable of a weak table"),
    ("return pcall(setmetatable, package.loaded, {})", "effect setmetatable(package.loaded)")].all fun (src, out) =>
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
  P(tonumber, nil), P(select, {sel}, \"a\", \"b\", \"c\"), P(function() return select(\"#\", unpack(\{}, {un})) end),
  _VERSION"

-- LuaJIT's globals and library fields the semantics does not model are handles (`unmodelled`): calling one stops
-- the run
#guard [("return collectgarbage(\"count\")", "effect collectgarbage"),
    ("return pcall(module, \"m\")", "effect module"),
    ("return package.searchpath(\"x\", \"?\")", "effect package.searchpath"),
    ("return require(\"jit\").off()", "effect jit.off"), ("return jit.status()", "effect jit.status"),
    -- a goto but the continue idiom stops the run too, pcall or not
    ("return pcall(function() local i = 0 ::top:: i = i + 1 if i < 3 then goto top end return i end)",
      "effect goto: a label that does not end its block")].all
  fun (src, out) => runCase (fun _ => none) .dual [] src.toList == out


-- ---------- debug ----------

/-- every builtin of the initial heap's library tables, as a Lua expression -/
def builtins : List String :=
  [("", 0), ("string.", 2), ("table.", 3), ("math.", 4), ("coroutine.", 6), ("io.", 9), ("os.", 10), ("debug.", 11),
    ("bit.", 12)].flatMap
    fun (lib, a) => match (initHeap[a]? : Option Obj) with
      | some (.tbl t) => t.kv.filterMap fun (k, v) => match k, v with
        | .str k, .prim .. => some (lib ++ String.ofList k)
        | _, _ => none
      | _ => []

/-- the debug library: a closure's upvalues in LuaJIT's order (the outer locals its body reads and writes, through
each statement, shadowed, in nested functions), set and read back; getinfo of a closure or builtin with any options,
a bad one, a negative level or no function; getmetatable and setmetatable raw (`__metatable` ignored), their bad
arguments; traceback of a value it returns as it is; each builtin's count of upvalues -/
def debugs : G String := do
  let ref : G String := pick ["a", "b", "c", "d", "e"]
  let stats ← (List.range ((← rnd 5) + 1)).mapM fun _ => do
    match ← rnd 10 with
    | 0 => pure s!"x = {← ref} + {← ref}"
    | 1 => pure s!"{← ref} = {← ref}"
    | 2 => pure s!"local {← ref} = 9; x = {← ref}"
    | 3 => pure s!"do local {← ref} = 0; x = {← ref} end"
    | 4 => pure s!"x = function(p, ...) return {← ref}, p end"
    | 5 => pure s!"for {← ref} = {← ref}, {← ref} do x = {← ref} end"
    | 6 => pure s!"repeat local {← ref} = 2 until {← ref}"
    | 7 => pure s!"if {← ref} then x = \{[{← ref}] = {← ref}, {← ref}} elseif {← ref} then x = {← ref} end"
    | 8 => pure s!"local function g() return g, {← ref} end; x = g"
    | _ => pure s!"x = (function() local {← ref} = 1; return function() return {← ref}, {← ref} end end)()"
  let ps ← pick ["", "p", "p, q", "...", "p, ..."]
  let k ← pick ["1", "2", "3", "0", "-1", "6", "\"2\"", "1.5"]
  let target ← pick ["f", "f", "g0", "print", "string.rep", "next", "(ipairs({}))", "(pairs({}))",
    "coroutine.wrap(f)", "(\"x\"):gmatch(\".\")", "type", "-1", "\"-2\"", "{}", "nil", "-0.5"]
  let opts ← pick ["\"u\"", "\"f\"", "\"l\"", "\"n\"", "\"nluf\"", "\"fu\"", "\"\"", "\"x\"", "\"uL\"", "\"Sl\"",
    "\"flnSu\"", "nil", "{}", "5"]
  let opts := if (target == "f" || target == "g0") && opts.contains 'L' then "\"un\"" else opts
  let up ← pick ["f", "g0", "next", "string.rep", "debug.getinfo", "nil", "5"]
  let prot ← pick ["nil", "false", "\"locked\""]
  let m2 ← pick ["nil", "{}", "m"]
  let bad ← pick ["", ", 1", ", \"x\"", ", nil", ", true"]
  let gm ← pick ["1", "nil", "true", "f", "print", "coroutine.create(f)", "o"]
  let tb ← pick ["{}", "nil", "false", "f", "co, {}", "co, nil", "o"]
  let all := if ← chance 4 then
    s!"local N = \{}\nfor i, h in ipairs(\{{commas builtins}}) do N[i] = debug.getinfo(h, \"u\").nups end\n" else
    "local N = 0\n"
  return all ++ s!"local a, b, c, d, e = 1, 2, 3, 4, 5
local function f({ps})
  local x
  {"\n  ".intercalate stats}
  return x
end
local g0 = function() return a, e end
local U = \{}
for i = 1, 7 do U[i] = \{pcall(debug.getupvalue, {up}, i)} end
local S = \{pcall(debug.setupvalue, {up}, {k}, 50)}
local after = \{a, b, c, d, e, pcall(f, 1, 2, 3)}
local I = \{pcall(debug.getinfo, {target}, {opts})}
local fi = I[2] and type(I[2]) == \"table\" and I[2].func
if fi then I[2].func = fi == {target} end
local m = \{__metatable = {prot}, __index = function(_, key) return key end}
local o = setmetatable(\{}, m)
local M = \{debug.getmetatable(o) == m, getmetatable(o), pcall(debug.setmetatable, o, {m2}), o.key,
  rawequal(getmetatable(o), {m2}), pcall(debug.setmetatable, o{bad}), pcall(debug.getmetatable, {gm})}
local co = coroutine.create(f)
local tr = debug.traceback({tb})
return U, S, after, I, M, tr == o or tr == f or tr == co or tr, type(debug), require(\"debug\") == debug, N"

-- what needs the host's frames or a Lua function's active lines, or sets the metatable of a type, stops the run
#guard [("return debug.traceback(\"x\", 2)", "effect debug.traceback from a level of the host's"),
    ("return (debug.getinfo(2, \"l\"))", "effect debug.getinfo of a level of the host's"),
    ("return (debug.getinfo(1, \"L\"))", "effect debug.getinfo: a Lua function's active lines"),
    ("return debug.setmetatable(1, {})", "effect debug.setmetatable of a number"),
    ("return debug.getmetatable(\"\")", "effect debug.getmetatable of a string"),
    ("return debug.getupvalue(print, 1)", "effect debug: the upvalues of print"),
    ("return debug.getlocal(1, 1)", "effect debug.getlocal"),
    ("return debug.setmetatable(package.loaded, {})", "effect setmetatable(package.loaded)"),
    ("local a, b = 1, 2 local function f() b = a; return function() return b, f end end return debug.getupvalue(f, 1), debug.getupvalue(f, 2), debug.getupvalue(f, 3)",
      "ok:\"b\",\"a\",\"f\",function")].all fun (src, out) =>
  runCase (fun _ => none) .dual [] src.toList == out

/-- the call stack: getinfo of a level (its line, its name as the call made it: a local, global, field, method,
upvalue, metamethod, for iterator, none from a builtin or after a tail call) and of a closure or chunk ('S');
tracebacks from frames made by Lua, builtins calling back, tail calls, and an error handler's of the error's frames -/
def stacks : G String := do
  let lvl ← pick ["0", "1", "2", "3", "4"]
  let opts ← pick ["\"l\"", "\"n\"", "\"nl\"", "\"S\"", "\"Sln\"", "\"f\"", "\"u\"", "nil", "\"flnSu\""]
  let msg ← pick ["\"t\"", "nil", "7", "\"t\", 0", "\"t\", 2", "\"t\", 1.5", "\"t\", -1"]
  let probe ← pick [s!"R[#R + 1] = show(debug.getinfo({lvl}, {opts}))", s!"R[#R + 1] = debug.traceback({msg})",
    "R[#R + 1] = debug.traceback()", s!"R[#R + 1] = show(debug.getinfo(l or 2, {opts}))"]
  let vias ← (List.range ((← rnd 4) + 1)).mapM fun _ => pick ["probe()", "local x = o.key", "local x = o + 1",
    "local x = o .. \"s\"", "o()", "t:m()", "t.m(t)", "tail()", "pcall(probe)", "deep(2)", "deep(0)",
    "for _ in function(_, c) if not c then probe() return 1 end end do end",
    "R[#R + 1] = select(2, xpcall(function() local y = nil + 1 end, debug.traceback))",
    "R[#R + 1] = select(2, xpcall(function() error(\"e\") end, debug.traceback))",
    "R[#R + 1] = select(2, xpcall(function() deep(1) error({}) end, debug.traceback))",
    "R[#R + 1] = select(2, xpcall(function() return (\"x\"):rep({}) end, debug.traceback))",
    "xpcall(function() error(\"e\") end, function(m) probe(3) return m end)",
    "local s = tostring(setmetatable({}, {__tostring = function() probe() return \"s\" end}))",
    "string.gsub(\"a\", \".\", function(c) probe() end)", "R[#R + 1] = show(debug.getinfo(deep, \"S\"))",
    "R[#R + 1] = show(debug.getinfo(loadstring(\"return 1\\n\\n\"), \"S\"))",
    "R[#R + 1] = show(loadstring(\"return debug.getinfo(1, 'Sl')\", \"=l\")())",
    "R[#R + 1] = (function() return debug.traceback(\"tail\") end)()",
    "R[#R + 1] = show(debug.getinfo(print, \"Sln\"))"]
  return s!"local R = \{}
local function show(i)
  if type(i) ~= \"table\" then return tostring(i) end
  local t = \{}
  for _, k in ipairs(\{\"currentline\", \"name\", \"namewhat\", \"source\", \"short_src\", \"linedefined\",
      \"lastlinedefined\", \"what\", \"nups\", \"nparams\", \"isvararg\"}) do
    t[#t + 1] = tostring(i[k])
  end
  return table.concat(t, \" \") .. \" \" .. type(i.func)
end
local function probe(l)
  {probe}
end
local o = setmetatable(\{}, \{__index = function(t, k) probe() return 1 end, __add = function(a, b) probe() return 2 end,
  __concat = function() probe() return \"c\" end, __call = function() probe() end})
local t = \{m = function(self) probe() end}
local function tail() return probe() end
local function deep(k) if k == 0 then probe() else deep(k - 1) end end
{"\n".intercalate vias}
return R"

-- a level or a traceback with the host's frames in it stops; the rest are LuaJIT's
#guard [("local function f() return debug.traceback(\"m\") end return f()", "ok:\"m\\010stack traceback:\\010\\009(host)\""),
    ("local function f() local s = debug.traceback(\"m\") return s end return (f())",
      "ok:\"m\\010stack traceback:\\010\\009c:1: in function 'f'\\010\\009c:1: in main chunk\\010\\009(host)\""),
    ("local function f(k) if k == 0 then return (debug.traceback()) end return (f(k - 1)) end return f(12)",
      "effect debug.traceback of a stack past 12 levels"),
    ("return (debug.getinfo(1, \"n\")).namewhat, debug.getinfo(0, \"n\").name", "ok:\"\",\"getinfo\""),
    ("return coroutine.wrap(function() return debug.traceback() end)()", "effect debug: a coroutine's stack"),
    ("return debug.getinfo(string.dump(function() end) and load(string.dump(function() end, true)), \"S\")",
      "effect debug.getinfo: a stripped function's lines")].all fun (src, out) =>
  runCase (fun _ => none) .dual [] src.toList == out

-- ---------- bit ----------

/-- the bit library: each function on integers, on doubles (lj_num2bit's rounding to even, past 2^31, 2^51 and 2^53,
inf, NaN), on strings and on bad arguments or too few; shift counts past 31 and negative; tohex's widths; a result's
zero times -1 (an integer on dual-number, a double on single-number) -/
def bitOps : G String := do
  let n : G String := pick ["0", "1", "-1", "5", "0x7fffffff", "0x80000000", "-0x80000000", "2^32", "2^32 + 3",
    "0xffffffff", "1.5", "2.5", "-0.5", "-1.5", "0.49999999999999994", "2^51 + 3", "2^52 + 2^51 + 5", "2^53 + 3",
    "2^60 - 2^9", "-2^63", "1e300", "1/0", "-1/0", "0/0", "-0.0", "\"0x10\"", "\" 7 \"", "\"1e3\"", "\"x\"",
    "nil", "{}", "true", "12345678", "-87654321", "0x12345678", "31", "32", "33", "-33", "255", "-9", "16", "300"]
  let call : G (String × List String) := do
    let f ← pick ["tobit", "bnot", "bswap", "band", "bor", "bxor", "lshift", "rshift", "arshift", "rol", "ror", "tohex"]
    let k ← match f with
      | "tobit" | "bnot" | "bswap" => pick [1, 1, 1, 0, 2]
      | "band" | "bor" | "bxor" => pick [1, 2, 2, 3, 4, 0]
      | _ => pick [2, 2, 2, 1, 0, 3]
    let as ← (List.range k).mapM fun _ => n
    pure (f, as)
  let calls ← (List.range 8).mapM fun _ => do
    let (f, as) ← call
    pure s!"\{pcall(bit.{f}{String.join (as.map (", " ++ ·))})}"
  let (f, as) ← call
  return s!"local x, y = {← n}, {← n}
local named = \{pcall(function() local r = bit.{f}({commas as}) return r end)}
local z = bit.band(x == x and 0 or 1, 0)
return {commas calls}, named, 1 / (z * -1), type(bit), require(\"bit\") == bit, bit.tohex(bit.bxor(12, 10), -2)"

#guard runCase (fun _ => none) .dual []
    ("return bit.tohex(-1, 0), bit.tohex(255, -4), bit.tohex(-1, 10), #bit.tohex(1, 300), bit.tohex(1, 1.9), " ++
      "bit.tobit(2^53 + 3), bit.tobit(-1.5), bit.rol(0x80000001, 1), bit.ror(1, -1), bit.bswap(0x12345678), " ++
      "bit.arshift(-256, 4), bit.rshift(-1, 32), bit.lshift(1, 33), bit.bor(1, 2, 4, 8.7), bit.tobit(\" 7 \"), " ++
      "bit.tobit(1/0), bit.bnot(0)").toList ==
  "ok:\"\",\"00FF\",\"00ffffffff\",254,\"01\",2,-2,3,2,2018915346,-16,-1,2,15,7,0,-1"

-- ---------- the FFI ----------

/-- the FFI's pure subset: cdata of scalars, arrays, structs and unions, their initializers (values, tables zero-
and one-based, by name, strings) and conversions (numbers past a type's range, fractions, booleans, nil, strings,
tables, cdata), element and field reads and writes, references into an aggregate, ffi.cast between numbers,
ffi.sizeof, ffi.string, ==, tonumber, a ctype's call, and their errors. Tags and typedef names are fresh per chunk:
LuaJIT's declarations outlive one, as test/luasem.lua runs every chunk in one state -/
def ffiOps : G String := do
  let id ← rnd 999999999
  let sc : G String := pick ["int8_t", "uint8_t", "int16_t", "uint16_t", "int32_t", "uint32_t", "int", "unsigned int",
    "short", "unsigned short", "float", "double", "bool", "char", "int64_t", "int", "double", "uint32_t", "int16_t",
    "float", "unsigned short", "bool", "int32_t"]
  let v : G String := pick ["0", "1", "-1", "7", "300", "-129", "65535", "65537", "1.5", "-2.75", "2^31", "2^32 + 5",
    "-2^31 - 1", "2^40 + 0.5", "1e20", "2^53", "0.1", "1/3", "-0.0", "true", "false", "nil", "\"5\"", "\"ab\"", "{}",
    "{1, 2}", "1/0", "0/0", "255.9", "-0.9", "2^62", "-2^63", "100000", "42", "3", "-7.5", "print", "x", "s.sub",
    "ffi.new(\"int\", 9)", "ffi.new(\"double\", -2.5)", "ffi.new(\"bool\", true)", "u"]
  let nv : G String := pick ["0", "1", "-1", "7", "300", "-129", "65535", "1.5", "-2.75", "2^31", "2^32 + 5", "0.1",
    "true", "false", "42", "-7.5", "255.9", "1e10"]
  let st := s!"s{id}"
  let tf := s!"t{id}"
  let fields ← (List.range (← pick [1, 2, 3])).mapM fun i => do pure (s!"f{i}", ← sc)
  let decl := String.join (fields.map fun (f, t) => s!"{t} {f}; ")
  let fk ← pick (fields.map (·.1))
  let n ← pick [1, 2, 3, 4]
  let et ← sc
  let idx : G String := do pick ((List.range n).map toString ++ ["0", "0.5", "-0.5", s!"{n - 1}.9"])
  let tbl : G String := do
    match ← rnd 4 with
    | 0 => pure s!"\{{← v}, {← v}}"
    | 1 => pure s!"\{[0] = {← nv}, {← nv}}"
    | 2 => pure s!"\{{fk} = {← nv}}"
    | 3 => pure s!"\{{← nv}}"
    | _ => pure s!"\{{← nv}, nil, {← nv}}"
  let init : G String := do
    match ← rnd 5 with
    | 0 => pure ""
    | 1 => pure s!", {← v}"
    | 2 => pure s!", {← v}, {← v}"
    | 3 => pure s!", {← tbl}"
    | 4 => pure s!", {← nv}, {← nv}, {← nv}, {← nv}, {← nv}"
    | _ => pure s!", {q (String.ofList ((List.range (4 * n)).map fun _ => 'z'))}"
  let op : G String := do
    match ← rnd 15 with
    | 0 => pure s!"local a = ffi.new(\"{et}[{n}]\"{← init}) return a[{← idx}], a[0], ffi.sizeof(a)"
    | 1 => pure s!"local a = ffi.new(\"{et}[{n}]\") a[{← idx}] = {← v} return a[0], a[{n - 1}]"
    | 2 => pure s!"return tonumber(ffi.cast(\"{← sc}\", {← v}))"
    | 3 => pure s!"local s = ffi.new(\"struct {st}\"{← init}) return s.{fk}, s.sub.g, s.a[1], s.a[0]"
    | 4 => pure s!"local s = ffi.new(\"struct {st}\") s.{← pick ["sub", "a", fk, "nope"]} = {← if ← chance 2 then tbl else v} return s.{fk}, s.sub.g, s.sub.h, s.a[0], s.a[1]"
    | 5 => pure s!"local u = ffi.new(\"union u{id}\", {← if ← chance 2 then tbl else nv}) return u.i, u.b[0], u.b[3], u.h[1], u.c"
    | 6 => do
      let w ← (List.range (n + 1)).mapM fun _ => pick "ab\x00c".toList
      pure s!"local a = ffi.new(\"{← pick ["char", "uint8_t", "int8_t", "unsigned char"]}[{n + 2}]\", {q (String.ofList w)}) a[{← idx}] = {← nv} return ffi.string(a), ffi.string(a, {← pick ["0", "1", "2", "1.5"]}), #ffi.string(x, {← pick ["0", "1", "4", "3"]})"
    | 7 => pure s!"return ffi.sizeof(\"struct {st}\"), ffi.sizeof(\"{et}[{n}]\"), ffi.sizeof(\"{et}[?]\", {← pick ["0", "3", "2.5", "-1"]}), ffi.sizeof(\"union u{id}\"), ffi.sizeof({tf}), ffi.sizeof(x)"
    | 8 => pure s!"return s == s, s.sub == s.sub, s.a == s.sub, s == x, s == nil, x ~= {← v}, ffi.typeof(\"{et}\") == ffi.typeof(\"{← sc}\"), {tf} == ffi.typeof(\"struct {st}\")"
    | 9 => pure s!"return type(x), type({tf}), tonumber(x), tonumber(ffi.new(\"{← sc}\", {← nv})), getmetatable(s), rawequal(x, x), ({← pick ["{}", "{[x] = 1}"]})[x]"
    | 10 => pure s!"local a = ffi.new(\"{et}[?]\", {← pick ["1", "2", "3", "0", "\"2\"", "nil"]}{← pick ["", s!", {← nv}", s!", {← nv}, {← nv}", s!", {← nv}, {← nv}, {← nv}"]}) return a[0], ffi.sizeof(a)"
    | 11 => pure s!"local c = ffi.typeof(\"{et}[{n}]\") local a = c({← nv}) return a[{n - 1}], ffi.sizeof(c)"
    | 12 => pure s!"return {← pick ["x.f", "x[true]", "s[1]", "s.nope", "u.i[0]", "x[nil]", "s.sub.nope", "u[0]"]}"
    | 13 => pure s!"local k = ffi.new(\"const {← sc}[2]\", {← nv}) {← pick ["k[0] = 1", "return k[1]"]}"
    | _ => pure s!"return ffi.string(s, {← pick ["1", "4", "8"]}), ffi.string(u, 4), ffi.string(x, ffi.sizeof(x)), {← pick ["ffi.string(1)", "ffi.string(x, \"2\")", "ffi.string({})", "ffi.string(s)", "ffi.string(true, 1)"]}"
  let ops ← (List.range 6).mapM fun _ => do pure s!"\{pcall(function() {← op} end)}"
  return s!"local ffi = require(\"ffi\")
ffi.cdef[[struct {st}a \{ int16_t g; uint8_t h; }; struct {st} \{ {decl}struct {st}a sub; int32_t a[2]; };
union u{id} \{ int32_t i; float f; uint8_t b[4]; uint16_t h[2]; uint8_t c; }; typedef struct {st} {tf};]]
local x = ffi.new(\"{et}[{n}]\", {← nv})
local s = ffi.new(\"{tf}\", \{sub = \{g = {← nv}}, a = \{{← nv}, {← nv}}})
local u = ffi.new(\"union u{id}\", {← nv})
local c = ffi.typeof(\"double[3]\")
return {commas ops}"

-- the values of LuaJIT 2.1 on x64 (single-number): conversions into integers by int64, a struct's layout, a union's
-- bytes, ffi.string's, and the error messages
#guard runCase (fun _ => none) .single []
    ("local ffi = require('ffi') ffi.cdef[[struct a { char c; double d; short s; }; union u { int i; float f; " ++
      "uint8_t b[4]; };]] local x = ffi.new('int[3]', 1.7, -2.9) local b = ffi.new('uint8_t[2]', 300, -1) " ++
      "local s = ffi.new('struct a', {[0] = 5, 2}) local u = ffi.new('union u', {b = {1, 2, 3, 4}}) " ++
      "return x[0], x[1], x[2], b[0], b[1], s.c, s.d, s.s, ffi.sizeof(s), u.i, " ++
      "tonumber(ffi.cast('uint16_t', -1)), tonumber(ffi.cast('int32_t', 2^32 + 5)), ffi.string(ffi.new('int[1]', " ++
      "0x41424344), 4), select(2, pcall(function() s.z = 1 end)), select(2, pcall(function() x[0] = 'a' end)), " ++
      "select(2, pcall(ffi.new, 'int[2]', 1, 2, 3)), s == s, x == nil, ffi.typeof('int') == ffi.typeof('int32_t')").toList ==
  "ok:1,-2,0,44,255,5,2,0,24,67305985,65535,5,\"DCBA\",\"c:1: 'struct a' has no member named 'z'\"," ++
    "\"c:1: cannot convert 'string' to 'int'\",\"too many initializers for 'int [2]'\",true,false,true"

/-- the FFI's pointers (#57): from arrays, structs, strings, nil and numbers (ffi.new, ffi.cast, a ctype's call),
their elements read and written (`p[i]`, `->`), arithmetic in and past an allocation, differences, `==` and `<`,
ffi.string of one, ffi.copy and ffi.fill, and their errors -/
def ptrOps : G String := do
  let id ← rnd 999999999
  let st := s!"q{id}"
  let it : G String := pick ["int16_t", "uint16_t", "int32_t", "uint32_t", "int", "double", "float", "bool", "uint8_t",
    "const int", "const uint8_t", "void", "const void", s!"struct {st}", "int32_t", "unsigned short", "const double"]
  let n ← pick [2, 3, 4, 5]
  let et ← pick ["int32_t", "uint8_t", "int16_t", "double", "uint32_t", "int32_t"]
  let k : G String := pick ["0", "1", "2", "0", "1", "-1", s!"{n}", "0.5", "1.9", "-0.5", "true", "\"1\"", "nil"]
  let v : G String := pick ["0", "1", "-1", "300", "65", "1.5", "true", "nil", "\"x\"", "{}", "p", "a", "2^31", "7"]
  let src : G String := pick ["a", "p", "s", "s[0]", "s[1]", "q", "nil", "0", "\"abcd\"", "\"\"", "true", "{}", "u",
    "a", "p", "ffi.new(\"double*\")", "ffi.new(\"const int[2]\")", "ffi.cast(\"uint16_t*\", a)", "\"hello world\""]
  let str : G String := pick ["\"abcd\"", "\"\"", "\"hello world\"", "\"\\1\\2\\3\\4\\5\\6\\7\\8\"", "\"\\255\\128ab\""]
  let op : G String := do
    match ← rnd 13 with
    | 0 => pure s!"local r = ffi.cast(\"{← it}*\", {← src}) return r[{← k}], r[0], r == {← src}, ffi.sizeof(r)"
    | 1 => pure s!"local r = a + {← k} return r[0], r[{← k}], r - a, a - r, r == p, r < p, r <= a, p < r"
    | 2 => pure s!"local r = ffi.new(\"{← it}*\", {← src}) return r == nil, r == {← src}, tonumber(r), type(r)"
    | 3 => pure s!"local r = ffi.cast(\"const {← pick ["char", "uint8_t", "int8_t", "int32_t", "uint16_t", "int16_t", "double"]}*\", {← str}) return r[{← k}], r[0], ffi.string(r), ffi.string(r + {← pick ["0", "1", "2"]}), ffi.string(r, {← pick ["0", "1", "3", "5"]})"
    | 4 => pure s!"local r = ffi.cast(\"{← it}*\", a) r[{← k}] = {← v} return a[0], a[1], a[{n - 1}]"
    | 5 => pure s!"local r = s + {← pick ["0", "1", "2", "3"]} return r.x, r.y, r.z, r[0].x, (r + 1).x, r - s"
    | 6 => pure s!"local r = s + {← pick ["0", "1"]} r.{← pick ["x", "y", "z", "c"]} = {← v} r[{← k}] = {← v} return s[0].x, s[1].x, s[1].y"
    | 7 => pure s!"local b = ffi.new(\"uint8_t[8]\") ffi.fill(b, {← pick ["8", "3", "0", "9", "-1", "\"2\""]}{← pick ["", ", 65", ", 300", ", -1", ", nil", ", \"7\""]}) ffi.copy(b + {← pick ["0", "1", "4", "8"]}, {← (← pick [str, src, pure "a", pure "p", pure "s"])}{← pick ["", ", 0", ", 2", ", 4", ", 8", ", -1"]}) return ffi.string(b, 8)"
    | 8 => pure s!"return {← pick ["p + 1", "1 + p", "p - 1", "p - a", "p * 2", "-p", "p + true", "p + p", "s + 1", "s - s", "u + 1", "p .. \"\"", "1 .. p", "p < 1", "p < nil", "nil < p", "p < s", "p <= a", "p > a", "p - ffi.cast(\"double*\", a)", "p < ffi.cast(\"uint8_t*\", a)", "ffi.new(\"void*\") - ffi.new(\"void*\")", "p - ffi.cast(\"const int32_t*\", a)", "c + 0", "ffi.new(\"int*\") + 0", "ffi.new(\"int*\") + 1", "ffi.new(\"int*\") - ffi.new(\"int*\")"]}"
    | 9 => pure s!"return p == {← src}, {← src} == p, a == s, s == s[0], ffi.new(\"int*\") == nil, q == {← str}, q + 0 == q, (q + 1) == q"
    | 10 => pure s!"return ffi.string({← src}{← pick ["", ", 0", ", 1", ", 4"]})"
    | 11 => pure s!"local r = ffi.cast(\"{← it}*\", {← src}) return r.x, r[0].y"
    | _ => pure s!"return {← pick ["ffi.new(\"char*\", \"x\")", "ffi.new(\"int*\", 1, 2)", "ffi.cast(\"int*\", 1)", "ffi.cast(\"intptr_t\", ffi.new(\"int*\"))", "tonumber(ffi.cast(\"int32_t\", ffi.new(\"int*\")))", "ffi.new(\"int\", p)", "ffi.cast(\"double\", p)", "ffi.new(\"int[2]\", p)", "ffi.new(\"void*\")[0]", "ffi.typeof(p) == ffi.typeof(\"int32_t*\")", "ffi.cast(\"int32_t*\", p) == p", "rawequal(ffi.cast(\"int32_t*\", p), p)", "ffi.copy(q, \"x\")", "ffi.copy(a)", "ffi.fill()", "ffi.copy(a, 1, 1)", "ffi.copy(a, \"ab\", \"1\")"]}"
  let ops ← (List.range 3).mapM fun _ => do pure s!"\{pcall(function() {← op} end)}"
  return s!"local ffi = require(\"ffi\")
ffi.cdef[[struct {st} \{ int32_t x; double y; uint8_t c[2]; };]]
local a = ffi.new(\"{et}[{n}]\", {commas ((List.range n).map fun i => toString (i * 3 + 1))})
local p = ffi.cast(\"int32_t*\", a) + {← pick ["0", "1"]}
local s = ffi.new(\"struct {st}[2]\", \{\{1, 1.5, \{2, 3}}, \{4, -2.5}})
local q = ffi.new(\"const char*\", {← str})
local u = ffi.new(\"int\", 3)
local c = ffi.typeof(\"int*\")
return {commas ops}"

-- the values of LuaJIT 2.1 on x64: an element through a pointer, a difference, ==, <, md5's str2lei, ffi.string of a
-- pointer, ffi.copy and ffi.fill, `->`, NULL, and the errors
#guard runCase (fun _ => none) .single []
    ("local ffi = require('ffi') ffi.cdef[[struct b { int x; double y; };]] local a = " ++
      "ffi.new('int[4]', 5, 6, 7) local p = a + 2 local s = ffi.new('struct b[2]', {{1, 1.5}, {2, " ++
      "2.5}}) local q = ffi.cast('const char*', 'hello') local b = ffi.new('uint8_t[8]') ffi.copy(b, " ++
      "'abc') ffi.fill(b + 4, 3, 65) return p[0], p[-1], (a + 3) - p, p == a + 2, p < a, a <= p, " ++
      "ffi.cast('const int*', ffi.new('const char*', 'abcd'))[0], ffi.string(q + 1), ffi.string(q, 3), " ++
      "q == 'hello', q + 1 == 'ello', ffi.string(b, 8), (s + 1).y, ffi.cast('struct b*', s).x, " ++
      "ffi.new('int*') == nil, tonumber(p), select(2, pcall(function() return p + true end)), select(2, " ++
      "pcall(function() return p < ffi.cast('double*', a) end)), select(2, pcall(ffi.new, 'int*', " ++
      "ffi.new('const int[2]'))), select(2, pcall(function() return (s + 1).z end)), select(2, " ++
      "pcall(function() return ffi.new('void*') - ffi.new('void*') end))").toList ==
  "ok:7,6,1,true,false,true,1684234849,\"ello\",\"hel\",true,false,\"abc\\000AAA\\000\",2.5,1,true,nil," ++
    "\"c:1: attempt to perform arithmetic on 'int *' and 'boolean'\"," ++
    "\"c:1: attempt to compare 'int *' with 'double *'\",\"cannot convert 'const int [2]' to 'int *'\"," ++
    "\"c:1: 'struct b' has no member named 'z'\"," ++
    "\"c:1: attempt to perform arithmetic on 'void *' and 'void *'\""

/-- the FFI's 64-bit integers (#58): numerals (each one object: #77), boxed reads of `int64_t` and `uint64_t`
elements, arithmetic and
comparisons of numbers and scalar cdata (signed or unsigned, by 0, past 2^63), tostring, tonumber, string.format's
`%d` and `%x`, conversions into narrower and wider types, and the errors -/
def i64Ops : G String := do
  let v : G String := pick ["1LL", "-1LL", "0LL", "1ULL", "0ULL", "18446744073709551615ULL", "9223372036854775807LL",
    "(-9223372036854775807LL - 1)", "0x7fffffffLL", "4294967296LL", "12345678901234LL", "3ULL", "0x8000000000000000ULL",
    "0", "1", "-1", "2", "7", "-7", "1.5", "-2.5", "2^53 + 1", "2^62", "-2^62", "4294967295", "63", "64", "-3",
    "ffi.new(\"int\", -3)", "ffi.new(\"uint32_t\", 4294967295)", "ffi.new(\"double\", 2.75)",
    "ffi.new(\"float\", -1.5)", "ffi.new(\"bool\", true)", "ffi.new(\"uint8_t\", 200)", "a[0]", "a[1]", "u[0]",
    "u[1]", "ffi.new(\"size_t\", 10)", "ffi.cast(\"int64_t\", -5)", "nil", "\"1\"", "{}", "true", "p", "a"]
  -- no table: `%s` would write its address
  let nt : G String := do let x ← v; pure (if x == "{}" then "-2" else x)
  let it : G String := pick ["int64_t", "uint64_t", "int8_t", "uint16_t", "int32_t", "uint32_t", "double", "float",
    "bool", "intptr_t", "size_t", "const int64_t"]
  let ar : G String := pick ["+", "-", "*", "/", "%", "^", "+", "-", "*"]
  let cmp : G String := pick ["==", "~=", "<", "<=", ">", ">="]
  let op : G String := do
    match ← rnd 10 with
    | 0 | 1 => pure s!"return tostring({← v} {← ar} {← v})"
    | 2 => pure s!"return {← v} {← cmp} {← v}, {← v} {← cmp} {← v}"
    | 3 => pure s!"return tostring(- {← v}), tonumber({← v}), type({← v})"
    | 4 => pure s!"return string.format(\"{← pick ["%d", "%x", "%5d", "%-22d|", "%X", "%s", "%.3d", "%+d", "%016x", "%i", "%#x", "% d", "%c", "%g"]}\", {← nt})"
    | 5 => pure s!"local b = ffi.new(\"{← it}[1]\") b[0] = {← v} return tostring(b[0]), ffi.sizeof(b)"
    | 6 => pure s!"return tostring(ffi.cast(\"{← pick ["int64_t", "uint64_t", "size_t"]}\", {← v})), tostring(ffi.new(\"{← pick ["int64_t", "uint64_t", "const int64_t"]}\", {← v}))"
    | 7 => pure s!"return {← pick ["#1LL", "#a", "1LL .. \"\"", "\"\" .. 1ULL", "a[0] .. a[1]", "ffi.typeof(a[0]) == ffi.typeof(\"int64_t\")", "ffi.typeof(u[0]) == ffi.typeof(\"size_t\")", "tostring(ffi.typeof(1ULL))", "tostring(ffi.typeof(\"const int64_t[2]\"))", "tostring(ffi.typeof(a))", "math.floor(1LL)", "(\"x\"):rep(2LL)", "1LL + \"1\"", "1LL < \"2\"", "1LL + p", "p + 1LL - p", "-a", "1ULL - 2"]}"
    | 8 => pure s!"local function f() return {← v} end local function mk() return function() return {← v} end end local t = \{[f()] = 1} return rawequal(f(), f()), rawequal(mk()(), mk()()), rawequal({← v}, {← v}), t[f()], t[{← v}]"
    | _ => pure s!"local x = {← v} x = x {← ar} {← v} return tostring(x), x == {← v}, tostring(a[0] {← ar} u[0]), tostring(a[1] {← ar} 1)"
  let ops ← (List.range 6).mapM fun _ => do pure s!"\{pcall(function() {← op} end)}"
  return s!"local ffi = require(\"ffi\")
local a = ffi.new(\"int64_t[2]\", {← pick ["5", "-7", "2^40", "-2^62"]}, {← pick ["3", "-1", "0", "2^33 + 1"]})
local u = ffi.new(\"uint64_t[2]\", {← pick ["5", "2^63", "0", "2^40"]}, {← pick ["1", "7", "2^64 - 2^12"]})
local p = ffi.cast(\"int32_t*\", ffi.new(\"int32_t[4]\")) + 1
return {commas ops}"

-- the values of LuaJIT 2.1 on x64: C's division and remainder, by 0, unsigned when either side is, a wrap past
-- 2^63, powers, tostring, tonumber, %d and %x, a double cdata's arithmetic, and the errors
#guard runCase (fun _ => none) .single []
    ("local ffi = require('ffi') local a = ffi.new('int64_t[2]', -7, 2^40) local u = ffi.new('uint64_t[1]', 2^63) " ++
      "return tostring(a[0] / 2), tostring(a[0] % 2), tostring(5LL / 0), tostring(u[0] + 1), tostring(-1 + 0ULL), " ++
      "tostring(2LL ^ 63), tostring(3ULL ^ -1), a[0] < 1ULL, a[0] < 1, a[1] == 2^40, tonumber(a[1] * a[1]), " ++
      "tostring(18446744073709551615LL), string.format('%d %x', 18446744073709551615ULL, -1LL), " ++
      "tostring(ffi.new('double', 2.75) * 2), select(2, pcall(function() return #a end)), select(2, " ++
      "pcall(function() return 1LL .. '' end)), ffi.typeof(a[0]) == ffi.typeof('int64_t'), select(2, " ++
      "pcall(ffi.new, 'const int64_t', {}))").toList ==
  "ok:\"-3LL\",\"-1LL\",\"-9223372036854775808LL\",\"9223372036854775809ULL\",\"18446744073709551615ULL\"," ++
    "\"-9223372036854775808LL\",\"12297829382473034411ULL\",false,true,true,0,\"-1LL\",\"-1 ffffffffffffffff\"," ++
    "\"4LL\",\"c:1: attempt to get length of 'int64_t [2]'\",\"c:1: attempt to concatenate 'int64_t' and 'string'\"," ++
    "true,\"cannot convert 'table' to 'const int64_t'\""

-- a numeral is one object for its chunk as loaded (-1LL and -(1LL) folded into it), a load of the chunk again or of
-- its dump a new one; two numerals two objects
#guard runCase (fun _ => none) .single []
    ("local function f() return 1LL end local function g() return -(1LL) end " ++
      "local function mk() return function() return 7ULL end end local t = {} " ++
      "for i = 1, 3 do t[1LL] = (t[1LL] or 0) + i end local k = {} for i = 1, 3 do k[f()] = i end " ++
      "local s = 'return 5LL' local l = loadstring(s) local d = loadstring(string.dump(l)) " ++
      "return rawequal(f(), f()), rawequal(g(), g()), rawequal(1LL, 1LL), rawequal(mk()(), mk()()), t[1LL], " ++
      "k[f()], rawequal(l(), l()), rawequal(l(), loadstring(s)()), rawequal(d(), l()), rawequal(d(), d()), " ++
      "tostring(g()), tostring(- -1LL)").toList ==
  "ok:true,true,false,true,nil,3,true,false,false,true,\"-1LL\",\"1LL\""

/-- the FFI's metatypes, enums, its other functions and C calls (#59): a struct's metatype with some of `__index`
(a table, a function), `__newindex`, the arithmetic metamethods, `__eq`, `__lt`, `__le`, `__len`, `__concat`,
`__call`, `__tostring` and a constructor's `__new`, each used on a cdata of the type, a pointer to one and the
ctype; an enum's constants (`ffi.C`'s, by name into the type) and fields; ffi.istype, offsetof, alignof, gc; and
the C library's `abs`, `strlen`, `toupper` and `memset` (the test's world, `Run.caseFx`, answers them as glibc
does), with their errors. Tags and constants are fresh per chunk, as in `ffiOps` -/
def mtOps : G String := do
  let id ← rnd 999999999
  let sm := s!"m{id}"
  let sn := s!"n{id}"
  let en := s!"e{id}"
  let k ← pick ["1", "5", "-2", "0x10", "1 << 3", "3 * 2 + 1", "-(4)", "~1"]
  let has (_ : String) : G Bool := chance 2
  let mms ← [("__index", ← pick ["{k = 7, len = function(s) return s.x + s.y end}", "function(c, k) return k end",
      "setmetatable({}, {__index = function(t, k) return k .. '?' end})", "{len = function(s) return s.x end}"]),
    ("__newindex", ← pick ["function(c, k, v) log[k] = v end", "log"]),
    ("__add", "function(a, b) return 'add' end"), ("__sub", "function(a, b) return type(a) .. type(b) end"),
    ("__mul", "function(a, b) return 2 end"), ("__eq", ← pick ["function(a, b) return true end", "function(a, b) return false end", "function(a, b) return 1 end"]),
    ("__lt", "function(a, b) return true end"), ("__le", "function(a, b) return nil end"),
    ("__len", "function(a, b) return 42 end"), ("__concat", "function(a, b) return 'cc' end"),
    ("__unm", "function(a) return 'neg' end"), ("__call", "function(self, z) return z end"),
    ("__tostring", "function(s) return 'P' .. s.x end"),
    ("__new", "function(ct, x) return ffi.new(ct, x or 9, 0.5) end")].filterM fun (n, _) => has n
  let mt := "{" ++ commas (mms.map fun (n, v) => s!"{n} = {v}") ++ "}"
  let hasM (n : String) : Bool := mms.any (·.1 == n)
  let v : G String := pick ["0", "1", "-7", "2.9", "-2.5", "true", "nil", "\"x\"", "{}", "p", "q", "300", "65"]
  let key : G String := pick ["x", "y", "k", "len", "nope", "c"]
  let tsp : List String := if hasM "__tostring" then ["tostring(p)", "tostring(pp)"] else []
  let op : G String := do
    match ← rnd 12 with
    | 0 => pure s!"return p.x, p.y, p.{← key}, pp.{← key}, P.{← key}, p:len()"
    | 1 => pure s!"p.{← key} = {← v} pp.{← key} = {← v} return p.x, p.y, log.{← key}, rawget(log, \"nope\")"
    | 2 => pure s!"return {← pick ["p + 1", "1 + p", "p - q", "q - p", "p * 2", "q + 1", "pp + 0", "p + pp", "-p", "-q", "#p", "#q", "#pp"]}"
    | 3 => pure s!"return p == p, p == P(3, 1.5), p == {← v}, {← v} == p, pp == p, p ~= q, q == q, q == nil, pp == nil"
    | 4 => pure s!"return {← pick ["p < p", "p <= pp", "q < q", "p < 1", "1 <= p", "pp < pp", "p > q"]}"
    | 5 => pure s!"return {← pick (["p .. \"s\"", "\"s\" .. p", "q .. 1", "tostring(P)", "tostring(ffi.typeof(\"struct " ++ sn ++ " *\"))"] ++ tsp)}"
    | 6 => pure s!"return {← pick ["p(1)", "pp(2)", "P(4).x", "P().x", "P(2, 3).y", "q()", "Q(5).v"]}"
    | 7 => pure s!"return ffi.istype({← pick ["P", "Q", "\"struct " ++ sm ++ "\"", "\"struct " ++ sm ++ " *\"", "\"int\"", "\"int[2]\"", "\"const int *\""]}, {← pick ["p", "pp", "q", "1", "nil", "ffi.new(\"int\")", "ffi.new(\"int[2]\")", "ffi.new(\"int *\")", "ffi.new(\"uint32_t[2]\")", "P", "\"x\""]}), ffi.offsetof({← pick ["P", "Q", "p", "\"int\"", "\"struct " ++ sn ++ "\""]}, {← pick ["\"x\"", "\"y\"", "\"v\"", "\"c\"", "\"z\"", "1"]}), ffi.alignof({← pick ["P", "q", "\"char\"", "\"double[3]\"", "\"enum " ++ en ++ "\"", "\"int16_t[?]\"", "\"void\""]})"
    | 8 => pure s!"return ffi.gc(p, nil) == p, ffi.gc(q, function() end) == q, {← pick ["ffi.gc(1, nil)", "ffi.gc(p)", "ffi.gc()", "ffi.gc(ffi.new(\"int\"), nil)", "ffi.gc(pp, nil) == pp", "ffi.metatype(P, {})", "ffi.metatype(\"int\", {})", "ffi.metatype(Q, 1)", "ffi.metatype(\"struct " ++ sn ++ " *\", {})", "ffi.istype(P)", "ffi.offsetof(P)"]}"
    | 9 => pure s!"local w = ffi.new(\"struct w{id}\", {← pick ["{\"C" ++ toString id ++ "\", 2}", "{1}", "{}", "{k = \"B" ++ toString id ++ "\"}", "{\"Z\"}", "{2.5}"]}) return C.A{id}, C.B{id}, C.C{id}, tonumber(w.k), w.z, tonumber(ffi.new(\"enum {en}\", {← pick ["\"A" ++ toString id ++ "\"", "\"C" ++ toString id ++ "\"", "\"nope\"", "3", "-1", "nil"]})), ffi.sizeof(\"enum {en}\"), tostring(w.k), type(w.k)"
    | 10 => pure s!"local b = ffi.new(\"uint8_t[8]\", 97, 98) C.memset(b + {← pick ["0", "1", "4"]}, {← pick ["65", "0", "300", "-1", "66.5"]}, {← pick ["0", "1", "3", "4"]}) return ffi.string(b, 8), C.abs({← v}), tonumber(C.strlen({← pick ["\"hello\"", "\"\"", "b", "b + 1", "\"a\\0b\""]})), C.toupper({← pick ["97", "65", "122", "48", "200", "\"x\""]})"
    | _ => do
      let w ← pick ["", "C.abs = 1 ", "C.A" ++ toString id ++ " = 2 "]
      pure (w ++ s!"return {← pick ["C.nosuch" ++ toString id, "C[1]", "C.abs", "C.abs == C.abs", "C.abs == C.toupper", "C.abs == nil", "type(C.abs)", "C.abs()", "C.abs(1, 2)", "C.abs({})", "C.memset(nil, 0, 0)", "C.toupper(true)", "type(C)", "rawequal(C, ffi.C)"]}")
  let ops ← (List.range 4).mapM fun _ => do pure s!"\{pcall(function() {← op} end)}"
  return s!"local ffi = require(\"ffi\")
ffi.cdef[[struct {sm} \{ int32_t x; double y; }; struct {sn} \{ int32_t v; uint8_t c[2]; };
enum {en} \{ A{id}, B{id} = {k}, C{id} }; struct w{id} \{ enum {en} k; int16_t z; };
int abs(int); size_t strlen(const char *); void *memset(void *s, int c, size_t n); int toupper(int);]]
local C = ffi.C
log = \{}
local P = ffi.metatype(\"struct {sm}\", {mt})
local Q = ffi.typeof(\"struct {sn}\")
local p = P(3, 1.5)
local q = Q(\{2, \{1, 2}})
local pp = ffi.new(\"struct {sm} *\", p)
return {commas ops}"

-- the values of LuaJIT 2.1 on x64: a metatype's __index (a table, a method, a miss), __newindex, __add from either
-- side, __eq on a struct and nil, __len, tostring, __call and __new, the address `==` and LuaJIT's errors without
-- one; an enum's constants and its boxed field; istype, offsetof, alignof, gc; a C call's arguments and errors
#guard runCase (fun _ => none) .single []
    ("local ffi = require('ffi') ffi.cdef[[struct pt { int x; double y; }; struct pq { int v; }; " ++
      "enum c { R, G = 4, B }; struct w { enum c k; }; int abs(int); size_t strlen(const char *); " ++
      "void *memset(void *s, int c, size_t n);]] local C = ffi.C local P = ffi.metatype('struct pt', " ++
      "{__index = {k = 7, len = function(s) return s.x + s.y end}, __add = function(a, b) return 'add' end, " ++
      "__eq = function() return true end, __len = function() return 42 end, __tostring = function(s) return " ++
      "'P' .. s.x end, __call = function(s, z) return z end, __new = function(ct, x) return ffi.new(ct, x, 0.5) " ++
      "end}) local p = P(3) local pp = ffi.new('struct pt *', p) local q = ffi.new('struct pq') local w = " ++
      "ffi.new('struct w', {'B'}) local b = ffi.new('uint8_t[4]') C.memset(b + 1, 65, 2) return p:len(), " ++
      "pp.k, 1 + p, p == nil, #p, tostring(pp), p(8), P.k, q == q, select(2, pcall(function() return p.z end)), " ++
      "select(2, pcall(function() return q < q end)), select(2, pcall(function() return #q end)), C.G, " ++
      "tonumber(w.k), tostring(w.k), ffi.istype(P, pp), ffi.istype('int', 1), ffi.offsetof(P, 'y'), " ++
      "ffi.alignof('enum c'), ffi.gc(q, nil) == q, select(2, pcall(ffi.metatype, P, {})), ffi.string(b, 4), " ++
      "C.abs(-5), tonumber(C.strlen('abc')), select(2, pcall(C.abs)), select(2, pcall(C.abs, 'x')), " ++
      "select(2, pcall(function() return C.nope end)), select(2, pcall(function() return q() end))").toList ==
  "ok:3.5,7,\"add\",true,42,\"P3\",8,7,true,\"c:1: 'struct pt' has no member named 'z'\"," ++
    "\"c:1: attempt to compare 'struct pq' with 'struct pq'\",\"c:1: attempt to get length of 'struct pq'\",4,5," ++
    "\"cdata<enum c>: 5\",true,false,8,4,true,\"cannot change a protected metatable\",\"\\000AA\\000\",5,3," ++
    "\"wrong number of arguments for function call\",\"bad argument #1 to '?' (cannot convert 'string' to " ++
    "'int')\",\"c:1: missing declaration for symbol 'nope'\",\"'struct pq' is not callable\""

-- ---------- the world: print, io.write, os ----------

/-- print and io.write, their arguments converted and what they write (`caseFx`: stdout), and os's computed part:
os.time of a date table (the zone UTC), os.date of a given time (`!` UTC, computed; else the local date), difftime;
each under pcall, by name at a site now and then -/
def effects : G String := do
  let wa : G String := pick ["\"a\"", "1.5", "2^53", "-0.0", "\"\\n\"", "\"x y\"", "10", "0/0", "1e100", "\"\"",
    "-7", "{}", "true", "nil"]
  let pa : G String := pick ["1", "\"s\"", "nil", "true", "false", "-0.0", "2.5", "1e15", "0/0", "\"\\t\"", "x"]
  let args (a : G String) : G String := do return commas (← (List.range (← rnd 4)).mapM fun _ => a)
  let fld (k : String) (vs : List String) : G String := do
    if ← chance 5 then return "" else return s!"{k} = {← pick vs}, "
  let year : G String := do
    pick [toString (1900 + (← rnd 200)), toString (1970 + (← rnd 68)), "\"2000\"", "2000.9", "1e3", "-1"]
  let date : G String := do
    let fs := (← fld "year" [← year, ← year]) ++
      (← fld "month" ["1", "2", "12", "13", "0", "-1", "1.5", "\"3\"", toString (← rnd 12)]) ++
      (← fld "day" ["1", "28", "29", "31", "0", "32", "-5", "1.7", toString (← rnd 31)]) ++
      (← fld "hour" ["0", "23", "24", "-1", "12.9", "\"10\"", "x"]) ++ (← fld "min" ["0", "59", "60", "-30", "1e3"]) ++
      (← fld "sec" ["0", "59", "61", "-1", "86400"]) ++ (if ← chance 6 then "isdst = false, " else "")
    if ← chance 6 then return s!"setmetatable(\{}, \{__index = \{{fs}}})" else return s!"\{{fs}}"
  let time : G String := pick ["0", "1", "59", "86399", "86400", "951782400", "951868800", "1e9", "1234567890",
    "2147483647", "2147483648", "-1", "-86400", "-2208988800", "4102444800", "1.5", "-0.5", "1e9 + 0.9", "\"1e9\"",
    toString (← rnd 4000000000), s!"-{← rnd 2000000000}"]
  let conv : G String := pick ["%a", "%A", "%b", "%B", "%c", "%C", "%d", "%D", "%e", "%F", "%h", "%H", "%I", "%j",
    "%m", "%M", "%n", "%p", "%r", "%R", "%S", "%t", "%T", "%u", "%U", "%w", "%W", "%x", "%X", "%y", "%Y", "%%", "-",
    " ", "at ", ":"]
  let fmt : G String := do
    match ← rnd 9 with
    | 0 => pick ["\"*t\"", "\"!*t\"", "\"\"", "\"!\"", "nil", "{}"]
    | _ =>
      let cs ← (List.range ((← rnd 4) + 1)).mapM fun _ => conv
      return q ((if ← chance 2 then "!" else "") ++ String.join cs)
  let dt : G String := pick ["5.7, 1.2", "3", "", "\"5\", \"2\"", "-1.9, 1.9", "1e9, 2e9", "0, 0", "{}", "1, nil"]
  let mut src := "local E = {}\nlocal x = 2\nlocal function c(f, ...) E[#E + 1] = {pcall(f, ...)} end\n"
  for _ in [0:(← rnd 6) + 2] do
    let call ← match ← rnd 8 with
      | 0 => pure s!"io.write, {← args wa}"
      | 1 => pure s!"print, {← args pa}"
      | 2 | 3 => pure s!"os.time, {← date}"
      | 4 | 5 | 6 => pure s!"os.date, {← fmt}, {← time}"
      | _ => pure s!"os.difftime, {← dt}"
    let call := if call.endsWith ", " then call.dropEnd 2 |>.toString else call
    src := src ++ (if ← chance 4 then
      -- a call at a site of its own: a bad argument is named, a missing field has its place
      let (f, as) := match call.splitOn ", " with | f :: as => (f, ", ".intercalate as) | [] => (call, "")
      s!"E[#E + 1] = \{pcall(function() local r = \{{f}({as})} return r end)}\n"
    else s!"c({call})\n")
  return src ++ "E[#E + 1] = 1 / (os.difftime(3, 3) * -1)\nreturn E"


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
    "local t = {}; (t).x, (t)['y'] = ...; return t.x, t.y",
    "local goto = {goto = ...}; goto.goto = goto.goto; return goto.goto"]
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

/-- string.dump and load of a dump: the function back, its upvalues new and nil, stripped or not (a stripped one's
errors at `?:0:`, an upvalue unnamed, a global or field by name; debug.getupvalue without names), the strip flag's
forms, load's modes; the dump as a string whose bytes are not read (type, tostring, `==` with itself and another
value, in a table, an error value at level 0, arithmetic, a comparison with a number, a call, a `for`, tonumber);
string.dump's bad arguments -/
def dumps : G String := do
  let body ← pick ["return a, b, u, w", "return u.x", "return gl_x.y", "return a + b", "return ({}).k.j",
    "error('m')", "error({a})", "return w()", "local r = w() return r", "return function() return u, w.x end",
    "local function g(x) if x then return g(nil) end return u end return g(1)", "return select('#', ...)",
    "u = a; return u, w", "return string.rep(a, b)", "local r = string.rep() return r", "return math.floor()",
    "for i = 1, a do u = i end return u", "return #...", "return (...)[1]"]
  let flag ← pick ["", ", true", ", false", ", nil", ", \"s\"", ", \"\"", ", \"d\"", ", \"ds\"", ", 0", ", {}"]
  let flag2 ← pick ["", ", true", ", false", ", \"s\""]
  let ld ← pick ["load(d)", "loadstring(d)", "load(d, \"=n\")", "loadstring(d, \"@x.lua\")", "load(d, nil, \"b\")",
    "load(d, nil, \"bt\")", "load(d, nil, \"t\")", "load(d, \"n\", \"\")", "load(d, 1)"]
  let args ← pick [", 1, 2", ", 'x', 3", "", ", 2, 3, 4", ", {5}, 6", ", nil, 2"]
  let use ← pick ["type(d)", "tostring(d) == d", "d == d", s!"d == string.dump(f{flag2})", "d == 1", "d ~= nil",
    "#{d, d}", "type(({d})[1])", "select('#', pcall(error, d, 0))", "(pcall(error, d, 0))", "tonumber(d)",
    "P(function() return d + 1 end)", "P(function() return d < 1 end)", "P(function() return 2 >= d end)",
    "P(function() local x = d() return x end)", "P(function() for i = d, 2 do end end)",
    "P(function() return -d end)", "P(function() return d .. setmetatable({}, {__concat = function() return 7 end}) end)",
    "P(function() d.x = 1 end)", "rawequal(d, {})", "P(function() return ({} .. d) end)", "not d"]
  let bad ← pick ["print", "string.rep", "1", "nil", "{}", "coroutine.create(f)"]
  return helper ++ s!"local u, w = \{x = 1}, print
local function f(a, b, ...)
  {body}
end
local d = string.dump(f{flag})
local g, e = {ld}
if not g then return e end
local r = \{pcall(g{args})}
local h = r[2]
local R = \{r, \{debug.getupvalue(g, 1)}, \{debug.getupvalue(g, 2)}, g == f, debug.getinfo(g, \"u\").nups,
  {use}, P(string.dump, {bad}), P(string.dump), P(load, string.dump(g){flag2})}
if type(h) == \"function\" then R.h = \{pcall(h), debug.getupvalue(h, 1)} end
return R"

-- what reads a dump's bytes stops the run: its length, a concatenation, a method, a key, as a result, `==` with a
-- string or another closure's dump, print, format, error's place, string.dump's flag; and a local's name in a
-- stripped function's error (LuaJIT finds it in the bytecode)
#guard [("return #string.dump(f)", "effect string.dump: a dump's bytes"),
    ("return string.dump(f) .. \"\"", "effect string.dump: a dump's bytes"),
    ("local t = {} t[string.dump(f)] = 1", "effect string.dump: a dump's bytes"),
    ("return ({})[string.dump(f)]", "effect string.dump: a dump's bytes"),
    ("return string.dump(f)", "effect string.dump: a dump's bytes"),
    ("return string.dump(f) == \"x\"", "effect string.dump: a dump's bytes"),
    ("return string.dump(f) == string.dump(function() end)", "effect string.dump: a dump's bytes"),
    ("print(string.dump(f))", "effect string.dump: a dump's bytes"),
    ("return string.dump(f):sub(1, 4)", "effect string.dump: a dump's bytes"),
    ("return string.dump(f) < \"x\"", "effect string.dump: a dump's bytes"),
    ("return (\"%s\"):format(string.dump(f))", "effect string.dump: a dump's bytes"),
    ("return pcall(error, string.dump(f))", "effect string.dump: a dump's bytes"),
    ("return string.dump(f, string.dump(f))", "effect string.dump: a dump's bytes"),
    ("return pcall(loadstring(string.dump(f, true)), 1)", "effect a stripped function's local named in an error"),
    ("return pcall(loadstring(string.dump(f, false)), 1)", "ok:false,\"c:1: attempt to index local 't' (a number value)\""),
    ("return type(string.dump(f)), string.dump(f) == string.dump(f), string.dump(f, true) == string.dump(f), string.dump(f) ~= {}",
      "ok:\"string\",true,false,true"),
    ("local u = 1 local function g() u = u + 1 return u end local h = load(string.dump(g)) return pcall(h), debug.getupvalue(h, 1), u",
      "ok:false,\"u\",1"),
    ("local u = 1 local function g() return u.x end return pcall(load(string.dump(g, true))), debug.getupvalue(load(string.dump(g, \"s\")), 1)",
      "ok:false,\"\",nil"),
    ("return pcall(string.dump, print), pcall(string.dump), pcall(string.dump, 1), load(string.dump(f), nil, \"t\")",
      "ok:false,false,false,nil,\"attempt to load chunk with wrong mode\"")].all fun (src, out) =>
  runCase (fun _ => none) .dual [] ("local function f(a) local t = a return t.x end " ++ src).toList == out

/-- function environments: setfenv and getfenv of closures, builtins, level 0 and 1 (non-tail calls) and bad
arguments; globals read and written through an environment with and without `__index`/`__newindex`; a closure made
under an environment keeps it; load and loadstring with an environment (a table, or anything else, ignored) -/
def fenvs : G String := do
  let env : G String := pick ["E1", "E2", "E3", "_G"]
  let fn : G String := pick ["f", "g", "h", "mk", "lf"]
  let body ← pick ["x = V(a); return x, y, V(getfenv(1)), V(getfenv()), V(getfenv(0))",
    "local r = {setfenv(1, a)} ; return V(r[1]), x, y, V(getfenv(1))",
    "function gf() return x end; x = V(a); return gf(), V(getfenv(gf))",
    "local old = getfenv(1); setfenv(1, a); local v = x; setfenv(1, old); return v, x, V(getfenv(f))",
    "return pcall(function() local r = setfenv(print, a) return r end)",
    "return z, V(getfenv(function() end))"]
  let step : G String := do
    match ← rnd 12 with
    | 0 | 1 => return s!"R[#R + 1] = \{pcall(setfenv, {← fn}, {← env})}"
    | 2 => return s!"R[#R + 1] = \{pcall(f, {← pick ["1", "\"s\"", "E1", "E2", "E3", "_G"]})}"
    | 3 => return s!"R[#R + 1] = \{pcall(g)}; h = mk()"
    | 4 => return "R[#R + 1] = {pcall(h)}"
    | 5 => return s!"R[#R + 1] = \{V(getfenv({← pick ["f", "g", "h", "mk", "lf", "print", "string.rep", "0", "1", "nil", "\"1\"", "1.5", ""]}))}"
    | 6 => return s!"R[#R + 1] = \{pcall(function() return V(getfenv({← pick ["-1", "{}", "true", "\"x\"", "0", "f", "print", "h"]})) end)}"
    | 7 => return s!"R[#R + 1] = \{pcall(setfenv, {← pick ["print", "string.rep", "{}", "nil", "-1", "\"x\"", "f"]}{← pick ["", ", 5", ", E1", ", nil"]})}"
    | 8 => return s!"lf = {← pick ["load", "loadstring"]}(\"x = tostring(x) .. 'L' return x, y, ...\", \"=l\", nil, {← pick ["E1", "E2", "E3", "nil", "5", "\"e\""]}); R[#R + 1] = \{V(getfenv(lf)), pcall(lf, 1)}"
    | 9 => return s!"R[#R + 1] = \{pcall(function() local r = \{setfenv({← fn}, {← env})} return V(r[1]) end)}"
    | 10 => return s!"R[#R + 1] = \{x, y, V(getfenv(1)), pcall(function() local e = getfenv(1) return V(e), V(getfenv(0)), x end)}"
    | _ => return s!"R[#R + 1] = \{pcall(f, {← env})}; R[#R + 1] = \{pcall(h)}"
  let steps ← (List.range ((← rnd 6) + 2)).mapM fun _ => step
  return s!"local getfenv, setfenv, pcall, tostring, print, ipairs, rawset = getfenv, setfenv, pcall, tostring, print, ipairs, rawset
x, y, z, gf = \"gx\", \"gy\", nil, nil
local E1 = \{x = 1, y = \"e1\"}
local E2 = setmetatable(\{y = \"e2\"}, \{__index = _G})
local E3 = setmetatable(\{}, \{__index = function(_, k) return tostring(k) .. \"?\" end, __newindex = function(t, k, v) rawset(t, k, tostring(v) .. \"!\") end})
local f, g, h, mk, lf
local names
local function V(v) for _, p in ipairs(names) do if v == p[1] then return p[2] end end if type(v) == \"table\" then return \"table\" end return v end
function f(a) {body} end
function g() local e = getfenv(1) return x, y, z, V(e) end
function mk() return function() return x, y, V(getfenv(1)) end end
h = mk()
names = \{\{E1, \"E1\"}, \{E2, \"E2\"}, \{E3, \"E3\"}, \{_G, \"_G\"}, \{f, \"f\"}, \{g, \"g\"}, \{h, \"h\"}, \{mk, \"mk\"}, \{print, \"print\"}}
local R = \{}
{"\n".intercalate steps}
return R, x, y, E1.x, E2.x, E3.x, gf ~= nil"

-- a level is the stack's (a builtin's frame there, or the host's, stops the run), and the thread's environment
-- (setfenv 0) stops it
#guard [("return pcall(getfenv, 1)", "effect getfenv of a builtin's level"),
    ("return getfenv(2)", "effect getfenv of a level of the host's"),
    ("local function f() return getfenv(1) end return f()", "effect getfenv of a level of the host's"),
    ("local function f() return setfenv(1, {}) end return pcall(f)", "effect setfenv of a builtin's level"),
    ("local function f() return getfenv(2) == _G end return (f())", "ok:true"),
    ("local function f() setfenv(2, {x = 1}) end local function g() f() return x end x = 2 return (g()), x", "ok:1,2"),
    ("setfenv(0, _G)", "effect setfenv of level 0: the thread's environment"),
    ("return pcall(debug.getfenv, print)", "effect debug.getfenv"),
    ("local e = setmetatable({}, {__index = _G}) local function f() y = 1 return x end x = 3 setfenv(f, e) return f(), e.y, y, getfenv(f) == e, setfenv(f, _G) == f, getfenv(1) == _G",
      "ok:3,1,nil,true,true,true"),
    ("local function f() setfenv(1, {}) end return pcall(f)", "ok:true"),
    ("return load(\"return x\", \"=l\", \"t\", {x = 4})(), loadstring(\"return x\", \"=l\", nil, {x = 5})(), load(\"return 6\", nil, nil, 1)()",
      "ok:4,5,6"),
    ("local f = function() return x end x = 1 return load(string.dump(f), nil, \"b\", {x = 7})(), load(string.dump(f))()",
      "ok:7,1")].all fun (src, out) =>
  runCase (fun _ => none) .dual [] src.toList == out

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

/-- coroutines: a body of random steps, each yielding (across pcall, in an iterator, a metamethod, table.foreachi),
changing a table the main thread changes too, nesting a coroutine, or failing; resumed a random number of times
with values each way, as `create`/`resume` or `wrap`; yields across a builtin that calls back (sort, gsub) and from
the main thread, the statuses, `running` and `isyieldable` -/
def coros : G String := do
  let v : G String := pick ["i", "x", "sh.n", "#log", "\"s\"", "nil", "{i}", "x, i", "1.5"]
  let step : G String := do
    match ← rnd 15 with
    | 0 | 1 | 2 => return s!"x = coroutine.yield({← v})"
    | 3 => return "sh.n = sh.n + 1; L(\"sh\", sh.n, x)"
    | 4 => return s!"L(\"pc\", pcall(function() local y = coroutine.yield({← v}); {← pick ["error(\"e\" .. tostring(y))", "error({y})", "return y", "error(y, 0)"]} end))"
    | 5 => return "for k in function(_, c) if c == nil then return coroutine.yield(\"it\") end end do L(\"for\", k) end"
    | 6 => return "L(\"ix\", setmetatable({}, {__index = function(_, k) return coroutine.yield(k) end}).key)"
    | 7 => return "setmetatable({}, {__newindex = function(_, k, w) L(\"ni\", coroutine.yield(k, w)) end}).f = i"
    | 8 => return "L(\"cl\", setmetatable({}, {__call = function(_, a) return coroutine.yield(\"call\", a) end})(i))"
    | 9 => return "table.foreachi({\"a\", \"b\"}, function(j, w) L(\"fe\", coroutine.yield(j, w)) end)"
    | 10 => return s!"L(\"cb\", pcall({← pick ["table.sort, {3, 1, 2}, function(a, b) coroutine.yield() return a < b end",
        "string.gsub, \"ab\", \".\", function(c) coroutine.yield(c) end", "string.gsub, \"ab\", \".\", setmetatable({}, {__index = function() coroutine.yield() end})"]}))"
    | 11 => return "local inner = coroutine.create(function(a) L(\"st\", coroutine.status(me), coroutine.status(inner0), coroutine.resume(me)); local b = coroutine.yield(a + 1); return b, coroutine.isyieldable() end)\ninner0 = inner\nL(\"in\", coroutine.resume(inner, i), coroutine.status(inner), coroutine.resume(inner, x), coroutine.resume(inner))"
    | 12 => return s!"if i > {← pick ["1", "2", "4"]} then {← pick ["error(\"stop\")", "error({i})", "return i, x", "error(x)", "local t = nil; t.f = 1"]} end"
    | 13 => return "L(\"me\", coroutine.running() == me, coroutine.isyieldable(), coroutine.status(me), i)"
    | _ => return s!"i = i + 1; L(\"i\", i, select(\"#\", coroutine.yield({← v})))"
  let body ← (List.range ((← rnd 6) + 2)).mapM fun _ => step
  let wrap ← chance 3
  let k ← rnd 7
  let arg ← pick ["k", "nil", "k, sh.n", "", "\"a\", \"b\", nil"]
  let drive := if wrap then
      s!"local w = coroutine.wrap(B)\nfor k = 1, {k + 1} do sh.n = sh.n * 2; L(\"w\", pcall(function() local r = \{w({arg})} return r end)) end"
    else
      s!"me = coroutine.create(B)\nL(\"s0\", coroutine.status(me))\nfor k = 1, {k + 1} do sh.n = sh.n * 2; L(\"r\", coroutine.resume(me{if arg == "" then "" else ", " ++ arg})); L(\"s\", coroutine.status(me)) end"
  return s!"local log, sh, me, inner0 = \{}, \{n = 1}
local function L(...) log[#log + 1] = \{...} end
local function B(...)
local x, i = ..., 0
{"\n".intercalate body}
return \"end\", x, i
end
{drive}
L(\"m\", pcall(coroutine.yield, 1), pcall(function() coroutine.yield() end), coroutine.running(), coroutine.isyieldable())
L(\"bad\", pcall(coroutine.resume, {← pick ["1", "nil", "{}", "B"]}), pcall(coroutine.{← pick ["create", "wrap", "status"]}, {← pick ["1", "nil", "{}"]}))
return log, sh.n"

-- a yield in an error handler stops the run (LuaJIT's xpcall then fails with "error in error handling"); a yield
-- in a module's chunk or a load reader cannot cross the C call
#guard [("return coroutine.resume(coroutine.create(function() return xpcall(error, function(m) return coroutine.yield(m) end) end))",
      "effect coroutine.yield in an error handler"),
    ("return coroutine.resume(coroutine.create(function() return pcall(load, function() coroutine.yield() end) end))",
      "effect load: an error in the reader"),
    ("local co = coroutine.create(function() coroutine.yield() end) coroutine.resume(co) return coroutine.status(co), coroutine.resume(co), coroutine.status(co)",
      "ok:\"suspended\",true,\"dead\"")].all fun (src, out) =>
  runCase (fun _ => none) .dual [] src.toList == out

/-- one of the chunks above -/
def chunk : G String := do
  if ← chance 8 then return ← errors
  match ← rnd 15 with
  | 0 => arith
  | 1 => strings
  | 2 | 3 => patterns
  | 4 => formats
  | 5 => tables
  | 6 => ctrl
  | 7 | 8 => diffs
  | 9 => match ← rnd 3 with | 0 => metas | 1 => opMetas | 2 => weaks | _ => compares
  | 10 => match ← rnd 7 with
    | 0 => libs | 1 => debugs | 2 => bitOps | 3 => stacks | 4 => ffiOps | 5 => i64Ops | 6 => ptrOps | _ => mtOps
  | 11 => traverse
  | 12 => if ← chance 4 then dumps else if ← chance 3 then fenvs else loads
  | 13 => coros
  | 14 => effects
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
