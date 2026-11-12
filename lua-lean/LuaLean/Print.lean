import LuaLean.Parse

/-! A syntax tree printed back as Lua, fully parenthesised: `lua-lean print`, which `lua-lean parsecheck` compares by
LuaJIT's bytecode with the source, and the chunks of `lua-lean check`. -/

namespace Lua.Print

def str (s : List Char) : String :=
  let esc := String.join (s.map fun c =>
    if c == '"' || c == '\\' || c.toNat < 32 || c.toNat > 126 then
      "\\" ++ String.ofList (Num.padLeft '0' 3 (Nat.toDigits 10 c.toNat))
    else c.toString)
  s!"\"{esc}\""

/-- a numeral LuaJIT reads back as the same number; a negative one in parentheses -/
def num (n : Num) : String :=
  let t := match n with
    | .flt f => if f.isInf then (if f < 0 then "-1/0" else "1/0") else String.ofList (Num.exactText n)
    | .int _ => String.ofList (Num.exactText n)
  if t.startsWith "-" || t.contains '/' then s!"({t})" else t

def binop : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%" | .pow => "^"
  | .concat => ".." | .eq => "==" | .ne => "~=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="

def unop : UnOp → String
  | .neg => "-" | .not => "not " | .len => "#"

def params (ps : List String) (va : Bool) : String := ", ".intercalate (ps ++ if va then ["..."] else [])

mutual
partial def exp : Exp → String
  | .nil => "nil" | .tru => "true" | .fls => "false" | .vararg => "..."
  | .num n => num n
  | .cnum v u _ => s!"{v}{if u then "ULL" else "LL"}"
  | .str s => str s
  | .func ps va b _ => s!"function({params ps va})\n{block b}end"
  | .var x => x
  | .index t k => s!"{pre t}[{exp k}]"
  | .call f as => s!"{pre f}({args as})"
  | .method o m as => s!"{pre o}:{m}({args as})"
  | .bin op a b => s!"({exp a} {binop op} {exp b})"
  | .and a b => s!"({exp a} and {exp b})"
  | .or a b => s!"({exp a} or {exp b})"
  | .un op a => s!"({unop op}{exp a})"
  | .table fs => "{" ++ ", ".intercalate (fs.map field) ++ "}"
  | .paren e => s!"({exp e})"
  | .site _ e => exp e

/-- a prefix expression: one that can be called or indexed -/
partial def pre (e : Exp) : String :=
  match e with
  | .var _ | .index .. | .call .. | .method .. | .paren _ => exp e
  | .site _ e => pre e
  | _ => s!"({exp e})"

partial def args (as : List Exp) : String := ", ".intercalate (as.map exp)

partial def field : Field → String
  | .pos e => exp e
  | .named k e => s!"{k} = {exp e}"
  | .keyed k e _ => s!"[{exp k}] = {exp e}"

partial def stat : Stat → String
  | .loc ns [] => s!"local {", ".intercalate ns}"
  | .loc ns es => s!"local {", ".intercalate ns} = {args es}"
  | .assign ts es => s!"{args ts} = {args es}"
  | .call e => exp e
  | .block b => s!"do\n{block b}end"
  | .while c b => s!"while {exp c} do\n{block b}end"
  | .rpt b c => s!"repeat\n{block b}until {exp c}"
  | .ite c t e => s!"if {exp c} then\n{block t}{els e}end"
  | .fornum v a b st body =>
    s!"for {v} = {exp a}, {exp b}{match st with | some s => ", " ++ exp s | none => ""} do\n{block body}end"
  | .forin vs es body => s!"for {", ".intercalate vs} in {args es} do\n{block body}end"
  | .locfn n ps va b _ => s!"local function {n}({params ps va})\n{block b}end"
  | .ret es => s!"return {args es}"
  | .brk => "break"
  | .goto l => s!"goto {l}"
  | .label l => s!"::{l}::"
  | .site _ st => stat st

/-- an `if`'s else part: `elseif` for a lone nested `if` -/
partial def els : Block → String
  | [] => ""
  | [.ite c t e] => s!"elseif {exp c} then\n{block t}{els e}"
  | e => s!"else\n{block e}"

partial def block (b : Block) : String := String.join (b.map (stat · ++ ";\n"))
end

end Lua.Print
