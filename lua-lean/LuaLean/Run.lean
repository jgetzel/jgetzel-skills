import LuaLean.Interp
import LuaLean.Parse

/-! Running a chunk the way `test/luasem.lua` runs it under LuaJIT, and its results as text both sides write alike:
`ok:` and each value, or `error:` and the error's value. A chunk is named `c`, as `loadstring(src, "=c")` names it. -/

namespace Lua

/-- bytes 32..126 but `"` and `\` as themselves, the rest as \ddd -/
def serStr (s : List Char) : List Char :=
  '"' :: (s.flatMap fun c =>
    if c.toNat ≥ 32 && c.toNat ≤ 126 && c != '"' && c != '\\' then [c]
    else '\\' :: Num.padLeft '0' 3 (Num.digits c.toNat)) ++ ['"']

def insertSorted (x : List Char) : List (List Char) → List (List Char)
  | [] => [x]
  | y :: ys => if strLt x y then x :: y :: ys else y :: insertSorted x ys

/-- a value as text: a table's entries sorted, a table already on the path `<cycle>` -/
def ser (h : Heap) (fuel : Nat) (path : List Nat) (v : Val) : List Char :=
  match fuel with
  | 0 => "<deep>".toList
  | fuel + 1 =>
  match v with
  | .nil => "nil".toList
  | .bool b => (if b then "true" else "false").toList
  | .num n => n.exactText
  | .str s => serStr s
  | .tbl a =>
    if path.contains a then "<cycle>".toList else
    match h[a]? with
    | some (.tbl t) =>
      let es := t.kv.filter (fun (_, v) => !v.isNil) |>.map fun (k, x) =>
        ser h fuel (a :: path) k ++ ['='] ++ ser h fuel (a :: path) x
      '{' :: List.intercalate [','] (es.foldr insertSorted []) ++ ['}']
    | _ => "<bad>".toList
  | .fn _ | .prim .. => "function".toList
  | .eff _ => "userdata".toList
  | .thr _ => "thread".toList

def outcome (r : EStateM.Result Err Heap (List Val)) : String :=
  match r with
  | .ok vs h => "ok:" ++ String.ofList (List.intercalate [','] (vs.map (ser h 100 [])))
  | .error (.val v) h => "error:" ++ String.ofList (ser h 100 [] v)
  | .error (.rt 0 m) h => "error:" ++ String.ofList (ser h 100 [] m.bare)
  | .error (.rt k _) _ => s!"effect error level {k} past the chunk"
  | .error .fuel _ => "fuel"
  | .error (.eff n _) _ => s!"effect {n}"
  | .error (.yld _) _ => "effect a yield past the chunk"

/-- every module under dir as source, by its path, dir/x.lua (`require` finds it through package.path), named by
that path in its error messages as LuaJIT names a file it loads -/
def loadSources (dir : System.FilePath) : IO (List (String × Block)) := do
  let mut r := []
  for e in ← dir.readDir do
    if e.fileName.endsWith ".lua" then
      let b ← IO.FS.readBinFile e.path
      match parseChunk (bytesOf b) (shortSrc ("@" ++ e.path.toString).toList) with
      | .ok blk => r := (e.path.toString, blk) :: r
      | .error err => throw (IO.userError s!"{e.path}: {err}")
  return r

/-- the package.path template under which `require "p.x"` is dir/x.lua: dir without p's directories -/
def libPath (p dir : String) : Option String :=
  let sub := p.replace "." "/"
  if dir == sub then some "?.lua"
  else if dir.endsWith ("/" ++ sub) then some ((dir.dropEnd sub.length).toString ++ "?.lua") else none

def srcsOf (l : List (String × Block)) (m : String) : Option Block := l.lookup m

/-- an effect while modules load: an opaque handle (configuring cjson, reading the environment) -/
def opaqueFx (name : String) (_ : List Val) : Option (List Val) := some [.eff (name ++ "()")]
def strictFx (_ : String) (_ : List Val) : Option (List Val) := none

def FUEL : Nat := 100000

/-- the chunk's results on target `tgt`, package.path `path`: the modules `mods` loaded first (effects opaque),
then the chunk (no effects) -/
def runCase (srcs : String → Option Block) (tgt : Target) (mods : List String) (src : List Char)
    (path : String := "./?.lua") : String :=
  match parseChunk src "c" with
  | .error e => s!"parse error: {e}"
  | .ok b =>
    let pre : M Unit := do
      rawset PACKAGE (lstr "path") (lstr path)
      mods.forM fun m => do
        let _ ← catchVal (callPrim srcs opaqueFx tgt FUEL "require" [] [lstr m]) pure
          (fun e => die s!"{m}: {String.ofList e.text}")
    match pre.run initHeap with
    | .error (.val e) _ => s!"load failed: {String.ofList e.text}"
    | .error e _ => s!"load failed: {outcome (.error e initHeap)}"
    | .ok () h => outcome ((runChunk srcs strictFx tgt FUEL b).run h)

end Lua
