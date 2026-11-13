import HarnessRetro.Hr

/-! transcript.lua: a Claude Code transcript (.jsonl) as compact Markdown, for reading or blind judging.

    transcript.sh FILE.jsonl [--redact OLD=NEW]... [--last]

`--last` prints only the final assistant text (probe.sh checks it for PROBE DONE). -/

namespace HarnessRetro.Transcript
open SwarmLean SwarmLean.Args
open Lean (Json JsonNumber)

/-- Lua's truthiness of a decoded field (null decodes to nil). -/
def luaT : Option Json → Bool
  | none | some .null | some (.bool false) => false
  | _ => true

/-- Lua's tostring of a decoded number: an integral one without a fraction, else `%.14g` (closely). -/
def luaNum (n : JsonNumber) : String :=
  if n.exponent == 0 then toString n.mantissa else
  let f := n.toFloat
  if f == f.floor && f.abs < 1e15 then toString f.toInt64 else toString n

/-- A string as JSON text with Python's ensure_ascii: `\uXXXX` (surrogate pairs above the BMP). -/
def quote (s : String) : String := Id.run do
  let hex4 (n : Nat) : String := let h := String.ofList (Nat.toDigits 16 n); "\\u" ++ "".pushn '0' (4 - h.length) ++ h
  let mut out := "\""
  for c in s.toList do
    let n := c.toNat
    out := out ++ match c with
      | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
      | '\x08' => "\\b" | '\x0c' => "\\f"
      | _ =>
        if n < 0x20 then hex4 n
        else if n < 0x80 then c.toString
        else if n < 0x10000 then hex4 n
        else hex4 (0xD800 + (n - 0x10000) / 1024) ++ hex4 (0xDC00 + (n - 0x10000) % 1024)
  return out ++ "\""

/-- Python's json.dumps of a decoded value: ", " and ": " separators, ASCII escapes, keys sorted; a null member is
dropped and an array ends at its first null, as the Lua's decode left them. -/
partial def dumps : Json → String
  | .null => "null"
  | .bool b => toString b
  | .num n => luaNum n
  | .str s => quote s
  | .arr a => "[" ++ ", ".intercalate ((a.toList.takeWhile (· != .null)).map dumps) ++ "]"
  | .obj kv =>
    let ms := (kv.toArray.toList.filter (·.2 != .null)).mergeSort (fun a b => a.1 ≤ b.1)
    "{" ++ ", ".intercalate (ms.map fun (k, v) => quote k ++ ": " ++ dumps v) ++ "}"

/-- A content value's text: a string as is; else its `text` blocks joined with newlines. -/
def textOf : Option Json → String
  | some (.str s) => s
  | c => "\n".intercalate ((arr c).filterMap fun b =>
      if Json.fstr b "type" == some "text" then some ((Json.fstr b "text").getD "") else none)

/-- `s` without system reminders, stripped, cut to `n` characters with a note of what was cut. -/
def clip (s : String) (n : Nat) : IO String := do
  let s := strip (← ok (Re.sub "<system-reminder>.*?</system-reminder>" "" s Re.S))
  let len := s.length
  if len ≤ n then return s
  return cut s n ++ s!" …[{len - n} more chars]"

/-- A tool call's input in one line: its first set key of a few, else the whole input. -/
def summary (inp : Json) : String := Id.run do
  for k in ["command", "file_path", "pattern", "skill", "url", "query", "description"] do
    let v := Json.field inp k
    if truthy v then
      return match v with | some (.str s) => s | some j => dumps j | none => ""
  return dumps inp

/-- The parser. -/
def spec : Spec :=
  .mk "transcript.sh" "Usage: transcript.sh [-h] [--redact <redact>] [--last] <file>

Arguments:
   file

Options:
   -h, --help            Show this help message and exit.
   --redact <redact>
   --last" [{ name := "file" }] [{ opt "--redact" with maxCount := 1000000 }, flag "--last"] [] [] none

/-- The user and assistant records of the main thread. -/
def records (path : String) : IO (Array Json) := do
  let some text ← read path | throw (IO.userError s!"{path}: No such file or directory")
  let mut recs := #[]
  for line in text.splitOn "\n" do
    if let some r := Json.decode line then
      let ty := Json.fstr r "type"
      if (ty == some "user" || ty == some "assistant") && !luaT (Json.field r "isSidechain") then recs := recs.push r
  return recs

/-- The content of a record's message. -/
def content (r : Json) : Option Json := (Json.field r "message").bind (Json.field · "content")

def main (args : List String) : IO UInt32 := do
  let some a ← parseArgs spec args | return 0
  let recs ← records (a.str "file" |>.getD "")
  if a.flag "last" then
    for r in recs.reverse do
      if Json.fstr r "type" == some "assistant" then
        let t := textOf (content r)
        if strip t != "" then IO.println t; return 0
    IO.println ""
    return 0
  let mut out : Array String := #[]
  let mut calls := 0
  let mut errors := 0
  for r in recs do
    let ty := (Json.fstr r "type").getD ""
    match (content r).getD (.str "") with
    | .str c =>
      if ty == "user" then
        let isMeta := luaT (Json.field r "isMeta")  -- skill bodies, injected context, cross-session messages
        out := out.push s!"\n### user{if isMeta then " (meta)" else ""}\n{← clip c (if isMeta then 600 else 3000)}\n"
    | c@(.arr _) | c@(.obj _) =>
      for b in arr (some c) do
        let t := Json.fstr b "type"
        if t == some "text" && strip ((Json.fstr b "text").getD "") != "" then
          out := out.push s!"\n**{ty}:** {← clip ((Json.fstr b "text").getD "") 3000}\n"
        else if t == some "tool_use" then
          calls := calls + 1
          let inp := (Json.field b "input").getD (Json.mkObj [])
          out := out.push s!"→ {(Json.fstr b "name").getD ""}: {← clip (summary inp) 400}"
        else if t == some "tool_result" then
          let body := match Json.field b "content" with
            | some (.arr x) => textOf (some (.arr x))
            | some (.obj _) => ""
            | some (.str s) => s
            | some (.num n) => luaNum n
            | some (.bool x) => toString x
            | _ => ""
          let err := luaT (Json.field b "is_error")
          if err then errors := errors + 1
          out := out.push (s!"  ← {if err then "ERROR " else ""}{← clip body 400}".replace "\n" "\n    ")
    | _ => pure ()
  let mut first : Option Float := none
  let mut last : Float := 0
  for r in recs do
    if let some ts := Json.fstr r "timestamp" then
      if let some t ← parseIso ts then
        if first.isNone then first := some t
        last := t
  let mins := match first with | some f => (last - f) / 60 | none => 0
  let mut text := s!"# Transcript: {cfixed mins 0} min, {calls} tool calls, {errors} errors\n" ++ "\n".intercalate out.toList
  for r in a.strs "redact" do
    match r.splitOn "=" with
    | old :: rest@(_ :: _) => text := plainReplace text old ("=".intercalate rest)
    | _ => pure ()
  IO.println text
  return 0

end HarnessRetro.Transcript
