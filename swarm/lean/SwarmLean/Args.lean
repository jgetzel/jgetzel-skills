import SwarmLean.Util

/-! The command line as main.lua's argparse parser reads it: the same grammar, errors and `-h` texts. A command group
declares its parsers as `Spec`s; `parse` runs the argparse state machine (argparse.lua's ParseState) over them. -/

namespace SwarmLean.Args

/-- A parsed value. -/
inductive V
  | s (x : String)
  | i (x : Int)
  | ids (x : List Int)
  | ss (x : List String)
  | b (x : Bool)
  deriving Repr, BEq, Inhabited

/-- A converter: the value, or the error text (none: argparse's "malformed argument"). -/
abbrev Conv := String → Except (Option String) V

/-- main.lua's `int`: Python's type=int. -/
def int : Conv := fun s => match parseInt s with
  | some n => .ok (.i n)
  | none => .error none

/-- main.lua's `id_list`: `3,5` (or `3`), distinct ids in the order given. -/
def idList : Conv := fun s =>
  let pieces := commaPieces (s.replace " " "")
  let rec go (seen : List Int) : List String → Except (Option String) (List Int)
    | [] => .ok seen.reverse
    | x :: xs => match parseInt x with
      | none => .error (some s!"not a list of task ids: '{s}'")
      | some n => go (if seen.contains n then seen else n :: seen) xs
  (go [] pieces).map .ids

/-- main.lua's `prio`: a priority 0 to 3. -/
def prio : Conv := fun s => match parseInt s with
  | some n => if 0 ≤ n && n ≤ 3 then .ok (.i n) else .error (some s!"not a priority (0-3): '{s}'")
  | none => .error (some s!"not a priority (0-3): '{s}'")

/-- An option (`p:option`/`p:flag`). -/
structure Opt where
  aliases : List String
  /-- where the value goes: the long name without dashes and with `_` for `-`, or a `:target` -/
  target : String
  /-- 0: a flag; 1: takes one argument -/
  nargs : Nat := 1
  default : Option String := none
  conv : Option Conv := none
  choices : List String := []
  minCount : Nat := 0
  maxCount : Nat := 1
  /-- a help flag: prints this text (the parser's `-h`) -/
  help : Option String := none
  deriving Inhabited

/-- A positional argument (`p:argument`). -/
structure Pos where
  name : String
  minArgs : Nat := 1
  maxArgs : Nat := 1
  default : Option String := none
  conv : Option Conv := none
  choices : List String := []
  deriving Inhabited

/-- A parser: a command's arguments, options, mutexes (by target), subcommands and `-h` text. -/
inductive Spec where
  | mk (name : String) (help : String) (args : List Pos) (opts : List Opt) (mutexes : List (List String))
      (cmds : List Spec) (cmdTarget : Option String)

/-- The command's name. -/
def Spec.name : Spec → String | .mk n .. => n
/-- The subcommands. -/
def Spec.cmds : Spec → List Spec | .mk _ _ _ _ _ c _ => c

/-- What a parse gives: each target's value (an unset one is absent). -/
abbrev Parsed := List (String × V)

/-- A flag `--x` with target `x`. -/
def flag (long : String) : Opt := { aliases := [long], target := (long.drop 2).toString.replace "-" "_", nargs := 0 }

/-- An option `--x <x>` with target `x`. -/
def opt (long : String) (default : Option String := none) (conv : Option Conv := none) : Opt :=
  { aliases := [long], target := (long.drop 2).toString.replace "-" "_", default, conv }

/-- The `-h, --help` of a parser whose help text is `h`. -/
def helpOpt (h : String) : Opt := { aliases := ["-h", "--help"], target := "help", nargs := 0, help := some h }

/-- How a parse ends: an error text, or a help text to print with exit 0. -/
inductive Stop
  | error (msg : String)
  | help (text : String)

/-- An option or argument being filled. -/
structure ElemSt where
  isOpt : Bool
  idx : Nat
  name : String := ""
  invocations : Nat := 0
  args : List String := []
  vals : List V := []
  isOpen : Bool := false
  deriving Inhabited

/-- The parse state (argparse.lua's ParseState). -/
structure St where
  opts : Array Opt := #[]
  optSt : Array ElemSt := #[]
  aliasMap : List (String × Nat) := []
  poss : Array Pos := #[]
  posSt : Array ElemSt := #[]
  argI : Nat := 0
  cmds : List Spec := []
  /-- the open option's index -/
  cur : Option Nat := none
  mutexes : List (List String) := []
  /-- each mutex's index, and the element (option or argument) that used it -/
  mutexUsed : List (Nat × (Bool × Nat)) := []
  result : Parsed := []
  handleOptions : Bool := true
  requireCmd : Bool := false
  /-- the current parser's command target -/
  cmdTarget : Option String := none

abbrev P := StateT St (Except Stop)

def err (msg : String) : P α := throw (.error msg)

def setResult (k : String) (v : V) : P Unit :=
  modify fun s => { s with result := (k, v) :: s.result.filter (·.1 != k) }

/-- argparse's get_tip: a suggestion for a mistyped name among `names`. -/
def tip (names : List String) (wrong : String) : String :=
  let drop1 (s : String) (i : Nat) : String := String.ofList (s.toList.take i ++ s.toList.drop (i + 1))
  let pool : List (String × String) := names.flatMap fun n => (List.range n.length).map fun i => (drop1 n i, n)
  let cands := (List.range (wrong.length + 1)).foldl (fun acc i =>
    let p := drop1 wrong i
    if names.contains p then (if acc.contains p then acc else acc ++ [p])
    else (pool.filter (·.1 == p)).foldl (fun a (_, n) => if a.contains n then a else a ++ [n]) acc) []
  match cands with
  | [] => ""
  | [c] => s!"\nDid you mean '{c}'?"
  | cs =>
    let q := (cs.map fun c => s!"'{c}'").toArray.qsort (· < ·)
    s!"\nDid you mean one of these: {" ".intercalate q.toList}?"

/-- argparse's `bound`. -/
def bound (noun : String) (mn mx : Nat) (isMax : Bool) : String :=
  let pre := if mn != mx then "at " ++ (if isMax then "most" else "least") ++ " " else ""
  let n := if isMax then mx else mn
  pre ++ toString n ++ " " ++ noun ++ (if n == 1 then "" else "s")

/-- Switches to parser `p` (its options join the ones already known; its arguments open). -/
def switch (p : Spec) : P Unit := do
  let .mk _ h args opts mx cmds tgt := p
  for o in helpOpt h :: opts do
    let s ← get
    let i := s.opts.size
    set { s with opts := s.opts.push o, optSt := s.optSt.push { isOpt := true, idx := i },
                 aliasMap := o.aliases.map (·, i) ++ s.aliasMap }
  modify fun s => { s with mutexes := s.mutexes ++ mx, cmds, requireCmd := !cmds.isEmpty, cmdTarget := tgt }
  for a in args do
    let s ← get
    let i := s.poss.size
    let e : ElemSt := { isOpt := false, idx := i, name := s!"argument '{a.name}'", invocations := 1, isOpen := a.maxArgs > 0 }
    set { s with poss := s.poss.push a, posSt := s.posSt.push e }
  -- an argument that takes no values is closed at once; none here does

/-- Converts and checks one value of an element. -/
def convert (choices : List String) (conv : Option Conv) (isOpt : Bool) (name arg : String) : P V := do
  if !choices.isEmpty && !choices.contains arg then
    err s!"{if isOpt then "argument for " else ""}{name} must be one of {", ".intercalate (choices.map fun c => s!"'{c}'")}"
  match conv with
  | none => pure (.s arg)
  | some f => match f arg with
    | .ok v => pure v
    | .error (some e) => err e
    | .error none => err s!"malformed argument '{arg}'"

/-- The stored value of an element from its values. -/
def finish (target : String) (nargs minA maxA minC maxC : Nat) (vals : List V) (append : Bool) : P Unit := do
  if nargs == 0 then setResult target (.b true)
  else if append then
    let prev := match (← get).result.lookup target with | some (.ss l) => l | _ => []
    let add := vals.filterMap fun | .s x => some x | _ => none
    setResult target (.ss (prev ++ add))
  else if maxA == 1 then
    if minA == 0 && minC != maxC then setResult target (.ss (vals.filterMap fun | .s x => some x | _ => none))
    else match vals with
      | v :: _ => setResult target v
      | [] => pure ()
  else setResult target (.ss (vals.filterMap fun | .s x => some x | .i n => some (toString n) | _ => none))

/-- Closes option `i`: checks its argument count and stores it. -/
def closeOpt (i : Nat) : P Unit := do
  let s ← get
  let o := s.opts[i]!
  let e := s.optSt[i]!
  if !e.isOpen then return
  set { s with optSt := s.optSt.set! i { e with isOpen := false } }
  if e.args.length < o.nargs then
    if e.args.isEmpty && o.nargs == 1 then err s!"{e.name} requires an argument"
    err s!"{e.name} requires {bound "argument" o.nargs o.nargs false}"
  if let some h := o.help then throw (.help h)
  finish o.target o.nargs o.nargs o.nargs o.minCount o.maxCount e.vals (o.maxCount > 1 && o.nargs > 0)

/-- Closes the open option, if any. -/
def close : P Unit := do
  if let some i := (← get).cur then
    closeOpt i
    modify fun s => { s with cur := none }

/-- Records that element (`isOpt`, `i`) is used, failing if another element of one of its mutexes was. -/
def checkMutexes (isOpt : Bool) (i : Nat) : P Unit := do
  let s ← get
  let target := if isOpt then s.opts[i]!.target else s.poss[i]!.name
  let name := if isOpt then s.optSt[i]!.name else s.posSt[i]!.name
  for (mx, k) in s.mutexes.zipIdx do
    if mx.contains target then
      match (← get).mutexUsed.lookup k with
      | some (o, j) =>
        if (o, j) != (isOpt, i) then
          let st ← get
          let other := if o then st.optSt[j]!.name else st.posSt[j]!.name
          err s!"{name} can not be used together with {other}"
      | none => modify fun s => { s with mutexUsed := (k, (isOpt, i)) :: s.mutexUsed }

/-- Passes one value to option `i`; false when it is then full (closed). -/
def passOpt (i : Nat) (arg : String) : P Bool := do
  let o := (← get).opts[i]!
  let e := (← get).optSt[i]!
  let v ← convert o.choices o.conv true e.name arg
  modify fun s => { s with optSt := s.optSt.set! i { e with args := e.args ++ [arg], vals := e.vals ++ [v] } }
  if e.args.length + 1 ≥ o.nargs then
    closeOpt i
    return false
  return true

/-- Invokes option `i` under the alias `name`. -/
def invoke (i : Nat) (name : String) : P Unit := do
  close
  modify fun s => { s with optSt := s.optSt.set! i { s.optSt[i]! with name := s!"option '{name}'" } }
  checkMutexes true i
  let o := (← get).opts[i]!
  let e := (← get).optSt[i]!
  if e.invocations ≥ o.maxCount then err s!"{e.name} must be used {bound "time" o.minCount o.maxCount true}"
  let e := { e with invocations := e.invocations + 1, isOpen := true, args := [], vals := [] }
  modify fun s => { s with optSt := s.optSt.set! i e }
  if o.nargs == 0 then closeOpt i
  else modify fun s => { s with cur := some i }

/-- Closes argument `i`: checks its count and stores it. -/
def closePos (i : Nat) : P Unit := do
  let s ← get
  let a := s.poss[i]!
  let e := s.posSt[i]!
  if !e.isOpen then return
  set { s with posSt := s.posSt.set! i { e with isOpen := false } }
  if e.args.length < a.minArgs then
    if e.args.isEmpty then err s!"missing {e.name}"
    err s!"{e.name} requires {bound "argument" a.minArgs a.maxArgs false}"
  finish a.name 1 a.minArgs a.maxArgs 1 1 e.vals false

/-- Passes one value to argument `i`; false when it is then full. -/
def passPos (i : Nat) (arg : String) : P Bool := do
  let a := (← get).poss[i]!
  let e := (← get).posSt[i]!
  let v ← convert a.choices a.conv false e.name arg
  modify fun s => { s with posSt := s.posSt.set! i { e with args := e.args ++ [arg], vals := e.vals ++ [v] } }
  if e.args.length + 1 ≥ a.maxArgs then
    closePos i
    return false
  return true

/-- The option an alias names, or the unknown-option error. -/
def getOpt (name : String) : P Nat := do
  match (← get).aliasMap.lookup name with
  | some i => pure i
  | none => err s!"unknown option '{name}'{tip ((← get).aliasMap.map (·.1)).eraseDups name}"

/-- Passes a plain word: to the open option, the current argument, or as a subcommand. -/
def pass (arg : String) : P Unit := do
  let s ← get
  if let some i := s.cur then
    if !(← passOpt i arg) then modify fun s => { s with cur := none }
  else if s.argI < s.poss.size then
    checkMutexes false s.argI
    if !(← passPos s.argI arg) then modify fun s => { s with argI := s.argI + 1 }
  else
    match s.cmds.find? (·.name == arg) with
    | none =>
      if s.cmds.isEmpty then err "too many arguments"
      else err s!"unknown command '{arg}'{tip (s.cmds.map (·.name)) arg}"
    | some c =>
      setResult c.name (.b true)
      if let some t := s.cmdTarget then setResult t (.s c.name)
      switch c


/-- Ends the parse: closes what is open, applies defaults, checks required options and a missing command. -/
def finalize : P Unit := do
  close
  let s ← get
  for i in [s.argI:s.poss.size] do
    let a := (← get).poss[i]!
    let e := (← get).posSt[i]!
    match e.args, a.default with
    | [], some dv =>
      -- argparse leaves an unpassed optional argument at its default
      modify fun s => { s with posSt := s.posSt.set! i { e with isOpen := false } }
      setResult a.name (.s dv)
    | _, _ => closePos i
  if (← get).requireCmd then err "a command is required"
  for i in [0:(← get).opts.size] do
    let o := (← get).opts[i]!
    let e := (← get).optSt[i]!
    let e := if e.name == "" then { e with name := s!"option '{o.aliases.getLast!}'" } else e
    modify fun s => { s with optSt := s.optSt.set! i e }
    if e.invocations == 0 then
      if let some dv := o.default then
        modify fun s => { s with optSt := s.optSt.set! i { e with invocations := 1, isOpen := true } }
        discard <| passOpt i dv
        closeOpt i
    let e := (← get).optSt[i]!
    if e.invocations < o.minCount then
      if e.invocations == 0 then err s!"missing {e.name}"
      err s!"{e.name} must be used {bound "time" o.minCount o.maxCount false}"

/-- Parses `args` with `root` (the command word itself not included in `args`), as argparse would after the root
parser switched to it; `rootTarget` is the root's command target and `rootHelp` its own `-h` text. -/
def parse (root : Spec) (rootTarget : String) (rootHelp : String) (args : List String) : Except Stop Parsed := do
  let run : P Unit := do
    -- the root parser's -h stays known after the switch, as in argparse
    switch (.mk "swarm" rootHelp [] [] [] [] none)
    modify fun s => { s with requireCmd := false, cmds := [] }
    setResult rootTarget (.s root.name)
    switch root
    for a in args do
      let s ← get
      if s.handleOptions && a.startsWith "-" && a.length > 1 then
        if (a.drop 1).startsWith "-" then
          if a.length == 2 then
            if s.aliasMap.lookup a |>.isSome then invoke (← getOpt a) a else close
            modify fun s => { s with handleOptions := false }
          else
            match a.splitOn "=" with
            | name :: rest@(_ :: _) =>
              let i ← getOpt name
              if (← get).opts[i]!.nargs == 0 then err s!"option '{name}' does not take arguments"
              invoke i name
              pass ("=".intercalate rest)
            | _ => invoke (← getOpt a) a
        else
          let cs := (a.drop 1).toString.toList
          let rec shorts : List Char → P Unit
            | [] => pure ()
            | c :: rest => do
              let name := "-" ++ c.toString
              let i ← getOpt name
              invoke i name
              if !rest.isEmpty && (← get).opts[i]!.nargs > 0 then pass (String.ofList rest)
              else shorts rest
          shorts cs
      else pass a
    finalize
  let ((), s) ← run.run {}
  return s.result

/-- A string value. -/
def Parsed.str (p : Parsed) (k : String) : Option String := match p.lookup k with
  | some (.s x) => some x
  | _ => none

/-- An integer value. -/
def Parsed.int (p : Parsed) (k : String) : Option Int := match p.lookup k with
  | some (.i x) => some x
  | _ => none

/-- An id-list value. -/
def Parsed.ids (p : Parsed) (k : String) : Option (List Int) := match p.lookup k with
  | some (.ids x) => some x
  | _ => none

/-- A list-of-words value. -/
def Parsed.strs (p : Parsed) (k : String) : List String := match p.lookup k with
  | some (.ss x) => x
  | some (.s x) => [x]
  | _ => []

/-- A flag. -/
def Parsed.flag (p : Parsed) (k : String) : Bool := match p.lookup k with
  | some (.b x) => x
  | _ => false

end SwarmLean.Args
