/-! The FFI's C types (LuaJIT's ctypes) as LP64 lays them out (x64's and arm64's ABI alike for these), their names
as LuaJIT's error messages give them, and the C declarations the subset parses: `ffi.cdef`'s, and the abstract
declarations `ffi.new`, `ffi.typeof`, `ffi.cast` and `ffi.sizeof` take. A declaration outside the subset (an enum,
a bitfield, a function pointer, an expression for an array's size, …) or one LuaJIT refuses parses to `none`: the run
stops there. -/

namespace Lua

inductive CType where
  | void
  | bool
  /-- an integer of `size` bytes (1, 2, 4, 8) -/
  | int (size : Nat) (signed : Bool)
  /-- plain `char`: signed on x64, unsigned on arm64 Linux (LuaJIT's CTF_UCHAR is the C compiler's) -/
  | ch
  | float
  | double
  | ptr (t : CType)
  /-- `n` elements; `none`, a variable-length array (`[?]`), its length the cdata's -/
  | arr (t : CType) (n : Option Nat)
  /-- a struct or union: its tag (a fresh `#k` for an anonymous one) and its fields -/
  | agg (union : Bool) (tag : String) (fields : List (String × CType))
  | const (t : CType)
  deriving BEq, Inhabited

namespace CType

/-- without its `const`, and whether it had one -/
def strip : CType → CType × Bool
  | .const t => ((strip t).1, true)
  | t => (t, false)

def qual (q : Bool) (t : CType) : CType := if q then .const t else t

def isScalar : CType → Bool
  | .bool | .int .. | .ch | .float | .double => true
  | _ => false

/-- an integer of 1 byte: its name and its sign differ between x64 and arm64 -/
def isByte : CType → Bool
  | .int 1 _ | .ch => true
  | _ => false

/-- plain `char` as both of what it may be: two types equal on one ABI and not the other agree here -/
def erase : CType → CType
  | .int 1 _ | .ch => .ch
  | .ptr t => .ptr (erase t)
  | .arr t n => .arr (erase t) n
  | .const t => .const (erase t)
  | t => t

/-- whether two types are one ctype; `none` when that depends on the ABI (plain `char`) -/
def same (a b : CType) : Option Bool :=
  if a == b then some true else if a.erase == b.erase then none else some false

/-- a pointer's or array's element type, `const` in a `const` array -/
def elem : CType → Option CType
  | .ptr t | .arr t _ => some t
  | .const (.arr t _) => some (.const t)
  | .const t => elem t
  | _ => none

/-- a number type's kind, as lj_cconv_compatptr tells them apart: a bool, a float, an integer -/
def numKind : CType → Option Nat
  | .bool => some 0
  | .float | .double => some 1
  | .int .. | .ch => some 2
  | _ => none

def roundUp (n a : Nat) : Nat := (n + a - 1) / a * a

mutual
def align : CType → Nat
  | .void | .bool | .ch => 1
  | .int s _ => s
  | .float => 4
  | .double | .ptr _ => 8
  | .arr t _ => align t
  | .const t => align t
  | .agg _ _ fs => alignFs fs
def alignFs : List (String × CType) → Nat
  | [] => 1
  | (_, t) :: fs => max (align t) (alignFs fs)
end

mutual
/-- its size in bytes; `none` for void and a variable-length array -/
def size : CType → Option Nat
  | .void => none
  | .bool | .ch => some 1
  | .int s _ => some s
  | .float => some 4
  | .double | .ptr _ => some 8
  | .arr t (some n) => (· * n) <$> size t
  | .arr _ none => none
  | .const t => size t
  | .agg u _ fs => (roundUp · (alignFs fs)) <$> recSize u fs 0
/-- a struct's fields after offset `o` (a union's, the largest so far) -/
def recSize (u : Bool) : List (String × CType) → Nat → Option Nat
  | [], o => some o
  | (_, t) :: fs, o => do
    let s ← size t
    recSize u fs (if u then max o s else roundUp o (align t) + s)
end

/-- lj_cconv_compatptr: whether a pointer of type `d` takes the address in a value of type `s` (a pointer, an array
or a struct), by `mode`: 0 as C does (no qualifier discarded, a `void *` on either side), 1 qualifiers ignored
(CCF_IGNQUAL: a difference, `<`), 2 the same qualifiers (CCF_SAME: what pointers point to). An integer's sign is not
looked at -/
partial def compat (mode : Nat) (d s : CType) : Bool :=
  match d.elem with
  | none => false
  | some de =>
    let (dc, dq) := de.strip
    let (sc, sq) := match s.elem with | some se => se.strip | none => (s.strip.1, false)
    let qok := if mode == 2 then dq == sq else mode == 1 || dq || !sq
    qok && ((mode == 0 && (dc == .void || sc == .void)) ||
      match dc, sc with
      | .void, .void => true
      | .ptr _, .ptr _ | .arr .., .arr .. => dc.size == sc.size && compat 2 dc sc
      | .agg .., .agg .. => dc == sc
      | _, _ => dc.numKind.isSome && dc.numKind == sc.numKind && dc.size == sc.size)

/-- a struct's or union's fields, each at its offset -/
def offsets (u : Bool) (fs : List (String × CType)) : List (String × Nat × CType) :=
  go fs 0
where go : List (String × CType) → Nat → List (String × Nat × CType)
  | [], _ => []
  | (n, t) :: fs, o =>
    let o' := if u then 0 else roundUp o (align t)
    (n, o', t) :: go fs (o' + (size t).getD 0)

/-- LuaJIT's name for it (lj_ctype_repr); `none` where that is the ABI's (a 1-byte integer's) or LuaJIT's ctype
numbering (an anonymous struct's, `struct 102`) -/
def repr (t : CType) : Option String :=
  let (ds, e) := dims t
  if ds.isEmpty then base e else (· ++ " " ++ String.join ds) <$> base e
where
  dims : CType → List String × CType
    | .arr t n => let (ds, e) := dims t; (s!"[{n.elim "?" toString}]" :: ds, e)
    | t => ([], t)
  base : CType → Option String
    | .void => some "void"
    | .bool => some "bool"
    | .float => some "float"
    | .double => some "double"
    | .int 2 s => some (if s then "short" else "unsigned short")
    | .int 4 s => some (if s then "int" else "unsigned int")
    | .int 8 s => some (if s then "int64_t" else "uint64_t")
    | .ptr t => match t with
      | .arr .. | .ptr (.arr ..) => none
      | t => (fun b => if b.endsWith "*" then b ++ "*" else b ++ " *") <$> base t
    | .agg u tag _ => if tag.startsWith "#" then none else some ((if u then "union " else "struct ") ++ tag)
    | .const t => match t with
      | .ptr _ | .arr .. | .const _ => none
      | t => ("const " ++ ·) <$> base t
    | _ => none

end CType

/-- what `ffi.cdef` has declared: typedef names, struct and union tags (`struct a`, `union u`), and the number of
anonymous ones so far -/
structure CDecls where
  types : List (String × CType) := []
  tags : List (String × CType) := []
  next : Nat := 0

/-! ## The C parser -/

inductive CTok where
  | id (s : String)
  | num (n : Nat)
  | p (c : Char)
  deriving BEq

def isIdStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_'

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10) else none

/-- a declaration's tokens; `none` at a character outside the subset (a string, a `#` line, `$`) -/
partial def ctoks : List Char → Option (List CTok)
  | [] => some []
  | '/' :: '*' :: r =>
    let rec skip : List Char → Option (List Char)
      | '*' :: '/' :: r => some r
      | _ :: r => skip r
      | [] => none
    skip r >>= ctoks
  | '/' :: '/' :: r => ctoks (r.dropWhile (· != '\n'))
  | '.' :: '.' :: '.' :: r => (CTok.p '…' :: ·) <$> ctoks r
  | c :: r =>
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c' then ctoks r
    else if isIdStart c then
      let w := (c :: r).takeWhile isIdChar
      (CTok.id (String.ofList w) :: ·) <$> ctoks ((c :: r).drop w.length)
    else if c.isDigit then
      let (n, rest) : Option Nat × List Char := match c, r with
        | '0', x :: r' => if x == 'x' || x == 'X' then
            let ds := r'.takeWhile (hexVal · |>.isSome)
            (if ds.isEmpty then none else some (ds.foldl (fun a d => a * 16 + (hexVal d).getD 0) 0), r'.drop ds.length)
          else
            let ds := (c :: r).takeWhile Char.isDigit
            -- an octal numeral: outside the subset but for 0
            (if ds.length == 1 then some 0 else none, (c :: r).drop ds.length)
        | _, _ =>
          let ds := (c :: r).takeWhile Char.isDigit
          (some (ds.foldl (fun a d => a * 10 + (d.toNat - '0'.toNat)) 0), (c :: r).drop ds.length)
      match n, rest with
      | some n, x :: _ => if isIdChar x then none else (CTok.num n :: ·) <$> ctoks rest
      | some n, [] => some [CTok.num n]
      | none, _ => none
    else if "*[](){};,?:=".contains c then (CTok.p c :: ·) <$> ctoks r
    else none

/-- the parser's state: the tokens left and the declarations so far -/
abbrev CPar := StateT (List CTok × CDecls) Option

namespace CPar

def peek : CPar (Option CTok) := do pure (← get).1.head?
def adv : CPar Unit := modify fun (ts, d) => (ts.drop 1, d)
def fail {α} : CPar α := StateT.lift none
def isP (c : Char) : CPar Bool := do pure ((← peek) == some (.p c))
def expect (c : Char) : CPar Unit := do if ← isP c then adv else fail
def decls : CPar CDecls := do pure (← get).2
def setDecls (d : CDecls) : CPar Unit := modify fun (ts, _) => (ts, d)

/-- the words of a type's specifier -/
def baseWords : List String :=
  ["void", "bool", "_Bool", "char", "short", "int", "long", "float", "double", "signed", "unsigned"]

def keywords : List String :=
  baseWords ++ ["const", "volatile", "struct", "union", "enum", "typedef", "extern", "static", "inline", "register",
    "restrict", "__restrict", "__attribute__", "__declspec", "__extension__", "__asm__", "asm", "auto", "_Complex",
    "complex", "__cdecl", "__stdcall", "__fastcall", "__thiscall", "__ptr32", "__ptr64", "__const", "__volatile__",
    "__inline", "__inline__", "_Alignas", "__alignof__", "sizeof", "__typeof__"]

/-- LuaJIT's built-in typedefs (lj_ctype.h's) the subset has -/
def builtinType : String → Option CType
  | "int8_t" => some (.int 1 true) | "uint8_t" => some (.int 1 false)
  | "int16_t" => some (.int 2 true) | "uint16_t" => some (.int 2 false)
  | "int32_t" => some (.int 4 true) | "uint32_t" => some (.int 4 false)
  | "int64_t" | "intptr_t" | "ptrdiff_t" | "ssize_t" => some (.int 8 true)
  | "uint64_t" | "uintptr_t" | "size_t" => some (.int 8 false)
  | _ => none

/-- the type a specifier's words name -/
def ofWords (ws : List String) : Option CType :=
  let sgn : Option Bool := if ws.contains "unsigned" then some false else if ws.contains "signed" then some true else none
  if ws.contains "unsigned" && ws.contains "signed" then none else
  let rest := (ws.filter (fun w => w != "signed" && w != "unsigned")).toArray.qsort (· < ·) |>.toList
  match rest, sgn with
  | [], some s => some (.int 4 s)
  | ["int"], s => some (.int 4 (s.getD true))
  | ["char"], none => some .ch
  | ["char"], some s => some (.int 1 s)
  | ["short"], s | ["int", "short"], s => some (.int 2 (s.getD true))
  | ["long"], s | ["int", "long"], s | ["long", "long"], s | ["int", "long", "long"], s => some (.int 8 (s.getD true))
  | ["void"], none => some .void
  | ["bool"], none | ["_Bool"], none => some .bool
  | ["float"], none => some .float
  | ["double"], none => some .double
  | _, _ => none

/-- a fresh tag for an anonymous struct or union -/
def fresh : CPar String := do
  let d ← decls
  setDecls { d with next := d.next + 1 }
  return s!"#{d.next}"

mutual
/-- a declaration's specifiers: its type (`const` kept), and whether it is a typedef -/
partial def spec (words : List String) (cnst : Bool) (named : Option CType) (td : Bool) : CPar (CType × Bool) := do
  match ← peek with
  | some (.id "const") => adv; spec words true named td
  | some (.id "typedef") => adv; spec words cnst named true
  | some (.id "extern") => adv; spec words cnst named td
  | some (.id w) =>
    if baseWords.contains w then
      if named.isSome then fail
      adv; spec (w :: words) cnst named td
    else if w == "struct" || w == "union" then
      if named.isSome || !words.isEmpty then fail
      adv; let t ← recSpec (w == "union"); spec words cnst (some t) td
    else if keywords.contains w then fail
    else if named.isNone && words.isEmpty then
      match (← decls).types.lookup w, builtinType w with
      | some t, _ | none, some t => adv; spec words cnst (some t) td
      | none, none => fail
    else finish words cnst named td
  | _ => finish words cnst named td
where finish (words : List String) (cnst : Bool) (named : Option CType) (td : Bool) : CPar (CType × Bool) := do
  let t ← match named, words with
    | some t, [] => pure t
    | none, _ :: _ => match ofWords words with | some t => pure t | none => fail
    | _, _ => fail
  return (CType.qual cnst t, td)

/-- a struct's or union's specifier after its keyword: a definition (given a tag or a fresh one), or a tag declared
before -/
partial def recSpec (u : Bool) : CPar CType := do
  let kw := if u then "union " else "struct "
  let tag ← match ← peek with
    | some (.id t) => if keywords.contains t then fail else do adv; pure (some t)
    | _ => pure none
  if ← isP '{' then
    adv
    let fs ← fields []
    expect '}'
    if (fs.map (·.1)).eraseDups.length != fs.length then fail
    let tag ← match tag with | some t => pure t | none => fresh
    let d ← decls
    if (d.tags.lookup (kw ++ tag)).isSome then fail
    let t := CType.agg u tag fs
    setDecls { d with tags := (kw ++ tag, t) :: d.tags }
    return t
  else match tag with
    | some t => match (← decls).tags.lookup (kw ++ t) with | some ty => pure ty | none => fail
    | none => fail

/-- a struct's fields until its `}`: each named, of a complete type -/
partial def fields (acc : List (String × CType)) : CPar (List (String × CType)) := do
  if ← isP '}' then return acc.reverse
  let (base, td) ← spec [] false none false
  if td then fail
  let rec more (acc : List (String × CType)) : CPar (List (String × CType)) := do
    let (n, t, fn) ← declarator base false
    if fn then fail
    let some n := n | fail
    if (t.size).isNone then fail
    let acc := (n, t) :: acc
    if ← isP ',' then adv; more acc else do expect ';'; pure acc
  fields (← more acc)

/-- a declarator over `base`: its name (none in an abstract one), its type, and whether it declares a function
(its parameters are skipped: a C function is the world's) -/
partial def declarator (base : CType) (abstract : Bool) : CPar (Option String × CType × Bool) := do
  let rec ptrs (t : CType) : CPar CType := do
    if ← isP '*' then
      adv
      let rec quals (t : CType) : CPar CType := do
        if (← peek) == some (.id "const") then adv; quals (.const t) else pure t
      ptrs (← quals (.ptr t))
    else pure t
  let t ← ptrs base
  let name ← match ← peek with
    | some (.id n) => if keywords.contains n || abstract then fail else do adv; pure (some n)
    | _ => pure none
  if ← isP '(' then
    if abstract || name.isNone then fail
    let rec skip (depth : Nat) : CPar Unit := do
      match ← peek with
      | some (.p '(') => adv; skip (depth + 1)
      | some (.p ')') => adv; if depth > 1 then skip (depth - 1)
      | some _ => adv; skip depth
      | none => fail
    skip 0
    return (name, t, true)
  let rec dims (first : Bool) (acc : List (Option Nat)) : CPar (List (Option Nat)) := do
    if ← isP '[' then
      adv
      match ← peek with
      | some (.p '?') => if !first || !abstract then fail else do adv; expect ']'; dims false (none :: acc)
      | some (.num n) => adv; expect ']'; dims false (some n :: acc)
      | _ => fail
    else pure acc.reverse
  let ds ← dims true []
  return (name, ds.foldr (fun n t => .arr t n) t, false)
end

/-- `ffi.cdef`'s declarations: typedefs are named, structs and unions defined; a function's or a variable's
declaration declares one of the world's symbols (`ffi.C`'s), which the semantics does not keep -/
partial def cdefs : CPar Unit := do
  match ← peek with
  | none => pure ()
  | some (.p ';') => adv; cdefs
  | _ =>
    let (base, td) ← spec [] false none false
    if ← isP ';' then adv; cdefs else
    let rec go : CPar Unit := do
      let (n, t, fn) ← declarator base false
      let some n := n | fail
      if td then
        if fn then fail
        let d ← decls
        if (d.types.lookup n).isSome || (builtinType n).isSome then fail
        setDecls { d with types := (n, t) :: d.types }
      if ← isP ',' then adv; go else expect ';'
    go
    cdefs

end CPar

/-- `ffi.cdef`'s string under the declarations so far -/
def parseCdef (s : List Char) (d : CDecls) : Option CDecls := do
  let ts ← ctoks s
  let ((), _, d) ← CPar.cdefs.run (ts, d)
  pure d

/-- an abstract declaration (`int[4]`, `struct a`, `const char *`, `uint8_t[?]`): its type; a struct or union it
defines joins the declarations, as LuaJIT's parser keeps it -/
def parseType (s : List Char) (d : CDecls) : Option (CType × CDecls) := do
  let ts ← ctoks s
  let (t, rest, d) ← (do
    let (base, td) ← CPar.spec [] false none false
    if td then CPar.fail
    let (_, t, fn) ← CPar.declarator base true
    if fn then CPar.fail
    pure t : CPar CType).run (ts, d)
  if !rest.isEmpty then none
  pure (t, d)

#guard (parseType "int[4]".toList {}).map (·.1) == some (.arr (.int 4 true) (some 4))
#guard (parseType "const char *".toList {}).map (·.1) == some (.ptr (.const .ch))
#guard (parseType "unsigned char[?]".toList {}).map (·.1) == some (.arr (.int 1 false) none)
#guard (parseType "int[2][3]".toList {}).map (·.1) == some (.arr (.arr (.int 4 true) (some 3)) (some 2))
#guard ((parseCdef "typedef struct { int x; double y; } pt; struct n { pt p[2]; uint8_t c; };".toList {}).bind
    fun d => (parseType "struct n".toList d).map (·.1.size)) == some (some 40)
#guard (parseCdef "int printf(const char *fmt, ...); typedef int (*cb)(int);".toList {}).isNone
#guard (parseCdef "int printf(const char *fmt, ...);".toList {}).isSome
#guard (CType.repr (.arr (.arr (.const (.int 4 true)) (some 3)) (some 2))) == some "const int [2][3]"
#guard (CType.repr (.arr (.int 4 true) none)) == some "int [?]"
-- LuaJIT's: a string to `const int *` and `char *` no, to `const uint8_t *` yes; `const double *` to `const void *`
-- yes, to `void *` no; `const int **` to `int **` no; `-` of `uint32_t *` and `const int *` yes
#guard !CType.compat 0 (.ptr (.const (.int 4 true))) (.arr (.const .ch) none) &&
  CType.compat 0 (.ptr (.const (.int 1 false))) (.arr (.const .ch) none) && !CType.compat 0 (.ptr .ch) (.arr (.const .ch) none) &&
  CType.compat 0 (.ptr (.const .void)) (.ptr (.const .double)) && !CType.compat 0 (.ptr .void) (.ptr (.const .double)) &&
  !CType.compat 0 (.ptr (.ptr (.int 4 true))) (.ptr (.ptr (.const (.int 4 true)))) &&
  CType.compat 1 (.ptr (.int 4 false)) (.ptr (.const (.int 4 true)))

end Lua
