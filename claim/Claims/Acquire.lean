import Claims.Ledger

/-! The claim loop of `swarm run` and `claim run`: try each usable machine, wait for room, give up when nothing can ever
fit. -/

namespace Claims

/-- What the loop needs of its caller. `cands` are the machines asked for (none: here), `usable` those of them that are
connected; `stateOf` says why one is not. `prog` prefixes the messages and `capHint` names the command that changes a cap. -/
structure Ask where
  prog : String
  capHint : String
  cands : List (Option String)
  usable : List (Option String)
  stateOf : Option String → String
  id : String
  /-- a count or `all` -/
  cores : String
  mem_kb : Int
  who : String
  cmd : String
  /-- this process's pid, the holder of a claim here -/
  pid : Int
  pollMs : Nat

/-- Claims on one of `a.usable` and waits for room: the machine and the cores granted, or none (after saying why) when
nothing can ever run it. The claims on the machines not chosen are released. -/
def acquire {m : Type → Type} [Monad m] (h : Host m) (a : Ask) : m (Option (Option String × Int)) := do
  let nameOf (c : Option String) := c.getD "here"
  let mut won : Option (Option String × Int) := none
  let mut first := true
  let mut told := false
  repeat
    let mut seen : List (Option String × Try) := []
    let mut gone := false
    for c in a.usable do
      if won.isSome then break
      let holder := if c.isNone then s!"p{a.pid}" else "t"
      let r := parseTry ((← call h c ["try", a.id, a.cores, toString a.mem_kb, holder, a.who, a.cmd]).getD "")
      match r with
      | .ok n => won := some (c, n)
      | .gone => gone := true
      | x => seen := seen ++ [(c, x)]
    if won.isSome then break
    let anyWait := seen.any fun (_, x) => match x with | .wait .. => true | _ => false
    let isFirst := first
    first := false
    if !anyWait && (isFirst || !gone) then
      for c in a.usable do release h c a.id
      h.err (s!"{a.prog}: nothing can run this job: " ++ "; ".intercalate (a.cands.map fun c =>
        s!"{nameOf c}: " ++ match a.stateOf c, (seen.lookup c) with
          | "connected", some (.never x y) => s!"needs more than the cap ({x} cores, {gi y}G)"
          | "connected", some .off => "off"
          | "connected", _ => "unreachable"
          | s, _ => s) ++ s!". Lower --cores/--mem, or `{a.capHint}`.")
      return none
    if !told then
      told := true
      h.err (s!"{a.prog}: waiting for room: " ++ "; ".intercalate (seen.map fun (c, x) => s!"{nameOf c}: " ++ match x with
        | .wait fc fm ah => s!"{fc} cores, {gi fm}G free, {ah} ahead"
        | _ => "no room"))
    h.sleep a.pollMs
  let some (chosen, got) := won | return none
  for c in a.usable do if c != chosen then release h c a.id
  return some (chosen, got)

/-- The environment of a job that holds `cs` cores and `mem_kb`, on top of `nixConfig` (NIX_CONFIG as it is). -/
def jobEnv (cs : String) (mem_kb : Int) (nixConfig : Option String) : List (String × String) :=
  [("SWARM_CORES", cs), ("SWARM_MEM_KB", toString mem_kb), ("MAKEFLAGS", "-j" ++ cs), ("CARGO_BUILD_JOBS", cs),
    ("NIX_BUILD_CORES", cs), ("NIX_CONFIG", (match nixConfig with | some x => x ++ "\n" | none => "") ++ s!"cores = {cs}\nmax-jobs = 1")]

end Claims
