import LuaLean.Run

/-! Random Lua chunks with the Lean interpreter's results, for `test/luasem.lua` to run under LuaJIT and compare (the
"Decoding Lua" check: the semantics is tested against the implementation). A chunk is a random program over the
subset's numbers, strings, patterns, string.format, tables and table.sort, and its control flow (closures, varargs,
metatables, goto, pcall). `writeCases` writes them as a Lua chunk, `return {{src = .., out = ..}, ..}`; a chunk whose
Lean run needs an effect or more fuel is left out. A user of the library adds chunks of its own (calls of its modules'
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
    | 'd' | 'i' | 'x' | 'X' => pick ["0", "7", "-3", "255", "1e15", "3.7", "-2.5", "42", "123456789"]
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

/-- one of the chunks above -/
def chunk : G String := do
  match ← rnd 7 with
  | 0 => arith
  | 1 => strings
  | 2 | 3 => patterns
  | 4 => formats
  | 5 => tables
  | 6 => ctrl
  | _ => numbers

/-- `n` chunks from `gen` (each with the modules to load first, from `srcs`) and their results, to `file` -/
def writeCases (gen : G (String × List String)) (srcs : String → Option Block) (n seed : Nat)
    (file : System.FilePath) : IO Unit := do
  let mut g := mkStdGen seed
  let mut cases : Array String := #[]
  let mut skipped : List String := []
  for _ in [0:n] do
    let ((src, mods), g') := gen.run g
    g := g'
    let out := runCase srcs mods src.toList
    if out.startsWith "ok:" || out == "error" then
      cases := cases.push s!"\{src = {String.ofList (serStr src.toList)}, out = {String.ofList (serStr out.toList)}},"
    else skipped := out :: skipped
  IO.FS.writeFile file ("return {\n" ++ "\n".intercalate cases.toList ++ "\n}\n")
  IO.eprintln s!"{cases.size} cases, {skipped.length} left out{if skipped.isEmpty then "" else s!" (first: {skipped.getLast!})"}"

end Lua.Gen
