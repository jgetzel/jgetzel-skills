import SwarmModel.Lua.Parse

/-! `lake env lean --run SwarmModel/LuaDump.lean <module> <file.lua>` prints the parsed file as a Lean definition
`<module>Src : Block`: a syntax tree proofs can be about (board #39). -/

open Swarm.Lua

def chars (s : List Char) : String :=
  let esc := String.join (s.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c == '\n' then "\\n"
    else if c.toNat < 32 || c.toNat > 126 then "\\x" ++ String.ofList (Num.padLeft '0' 2 (Nat.toDigits 16 c.toNat)) else c.toString)
  s!"\"{esc}\".toList"

def nm (s : String) : String := s!"\"{s}\""
def lst (l : List String) : String := "[" ++ ", ".intercalate l ++ "]"

def num : Num → String
  | .int i => if i < 0 then s!"(.int ({i}))" else s!"(.int {i})"
  | .flt f => s!"(.flt {f})"

def binop : BinOp → String
  | .add => ".add" | .sub => ".sub" | .mul => ".mul" | .div => ".div" | .mod => ".mod" | .pow => ".pow"
  | .concat => ".concat" | .eq => ".eq" | .ne => ".ne" | .lt => ".lt" | .le => ".le" | .gt => ".gt" | .ge => ".ge"

def unop : UnOp → String
  | .neg => ".neg" | .not => ".not" | .len => ".len"

mutual
partial def exp : Exp → String
  | .nil => ".nil" | .tru => ".tru" | .fls => ".fls" | .vararg => ".vararg"
  | .num n => s!"(.num {num n})"
  | .str s => s!"(.str {chars s})"
  | .func ps va b => s!"(.func {lst (ps.map nm)} {va} {block b})"
  | .var x => s!"(.var {nm x})"
  | .index t k => s!"(.index {exp t} {exp k})"
  | .call f as => s!"(.call {exp f} {lst (as.map exp)})"
  | .method o m as => s!"(.method {exp o} {nm m} {lst (as.map exp)})"
  | .bin op a b => s!"(.bin {binop op} {exp a} {exp b})"
  | .and a b => s!"(.and {exp a} {exp b})"
  | .or a b => s!"(.or {exp a} {exp b})"
  | .un op a => s!"(.un {unop op} {exp a})"
  | .table fs => s!"(.table {lst (fs.map field)})"
  | .paren e => s!"(.paren {exp e})"

partial def field : Field → String
  | .pos e => s!"(.pos {exp e})"
  | .named k e => s!"(.named {nm k} {exp e})"
  | .keyed k e => s!"(.keyed {exp k} {exp e})"

partial def stat : Stat → String
  | .loc ns es => s!"(.loc {lst (ns.map nm)} {lst (es.map exp)})"
  | .assign ts es => s!"(.assign {lst (ts.map exp)} {lst (es.map exp)})"
  | .call e => s!"(.call {exp e})"
  | .block b => s!"(.block {block b})"
  | .while c b => s!"(.while {exp c} {block b})"
  | .rpt b c => s!"(.rpt {block b} {exp c})"
  | .ite c t e => s!"(.ite {exp c} {block t} {block e})"
  | .fornum v a b st body =>
    s!"(.fornum {nm v} {exp a} {exp b} {match st with | some s => s!"(some {exp s})" | none => "none"} {block body})"
  | .forin vs es body => s!"(.forin {lst (vs.map nm)} {lst (es.map exp)} {block body})"
  | .locfn n ps va b => s!"(.locfn {nm n} {lst (ps.map nm)} {va} {block b})"
  | .ret es => s!"(.ret {lst (es.map exp)})"
  | .brk => ".brk"
  | .goto l => s!"(.goto {nm l})"
  | .label l => s!"(.label {nm l})"

partial def block (b : Block) : String := "\n  " ++ lst (b.map stat)
end

def main (args : List String) : IO UInt32 := do
  let [name, file] := args | do IO.eprintln "usage: LuaDump.lean <module> <file.lua>"; return 1
  match parseChunk (bytesOf (← IO.FS.readBinFile file)) with
  | .error e => IO.eprintln e; return 1
  | .ok b =>
    IO.println s!"/-- {file}, parsed -/\ndef {name}Src : Block :={block b}\n"
    return 0
