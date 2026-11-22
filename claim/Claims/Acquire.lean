import Claims.Ledger

/-! The claim loop of `swarm run` and `claim run`: try each usable machine, wait for room, give up when nothing can ever
fit. -/

namespace Claims

/-- What the loop needs of its caller. `cands` are the machines asked for (none: here), `usable` those of them that are
connected; `stateOf` says why one is not. `prog` prefixes the messages and `capCmd` is the command whose `cap` and `on` change a machine's limits. -/
structure Ask where
  prog : String
  capCmd : String
  cands : List (Option String)
  usable : List (Option String)
  stateOf : Option String → String
  id : String
  /-- a count or `all` (the whole machine, alone; `mem_kb` is then ignored) -/
  cores : String
  mem_kb : Int
  /-- the expected wall time (s): what lets the request start before an older waiter (§2.2) -/
  est : Option Int := none
  who : String
  cmd : String
  /-- this process's pid, the holder of a claim here -/
  pid : Int
  pollMs : Nat

/-- Real idle cores of a machine: `ncpu - max busy claimed`, at least 0. -/
def idleCores (l : Ls) : Float :=
  let cc : Int := l.claims.foldl (fun s c => s + c.cores) 0
  let used := if l.busy > Float.ofInt cc then l.busy else Float.ofInt cc
  let x := Float.ofInt l.ncpu - used
  if x < 0 then 0 else x

/-- `us` by real idle cores, most first; a tie keeps the order given (here first), a machine that did not answer goes last. -/
def rankByIdle (xs : List (Option String × Option Float)) : List (Option String × Option Float) :=
  xs.mergeSort fun a b => match a.2, b.2 with
    | some x, some y => x >= y
    | some _, none => true
    | none, some _ => false
    | none, none => true

/-- Claims on one of `a.usable` and waits for room: the machine, the cores and the memory granted, or none (after saying why)
when nothing can ever run it. The claims on the machines not chosen are released. -/
def acquire {m : Type → Type} [Monad m] (h : Host m) (a : Ask) : m (Option (Option String × Int × Int)) := do
  let nameOf (c : Option String) := c.getD "here"
  let mut won : Option (Option String × Int × Int) := none
  let mut first := true
  let mut told : Option String := none
  let mut lastWhy : Int := 0
  let mut order := a.usable
  if a.usable.length > 1 then
    let mut reads : List (Option String × Option Float) := []
    for c in a.usable do
      reads := reads ++ [(c, (parseLs ((← call h c ["ls"]).getD "")).map idleCores)]
    let ranked := rankByIdle reads
    order := ranked.map (·.1)
    h.err (s!"{a.prog}: placing: " ++ ", ".intercalate (a.usable.map fun c =>
      s!"{nameOf c} " ++ match ranked.lookup c with | some (some x) => s!"{fixed x 1} idle" | _ => "unreachable") ++
      s!" → {nameOf (order.headD none)}")
  repeat
    let mut seen : List (Option String × Try) := []
    let mut gone := false
    for c in order do
      if won.isSome then break
      let holder := if c.isNone then s!"p{a.pid}" else "t"
      let r := parseTry ((← call h c ["try", a.id, a.cores, toString a.mem_kb, (a.est.elim "-" toString), holder, a.who, a.cmd]).getD "")
      match r with
      | .ok n g => won := some (c, n, g)
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
          | "connected", some (.never x y) =>
            if a.cores == "all" then s!"the cap ({x} cores, {gi y}G) is below the whole machine"
            else s!"needs more than the cap ({x} cores, {gi y}G)"
          | "connected", some .off => "off"
          | "connected", _ => "unreachable"
          | s, _ => s) ++
        (if a.cores == "all" then s!". Ask for a count of cores, or lift the cap: `{a.capCmd} cap <machine> --cores all --mem all`."
         else s!". Lower --cores/--mem, or `{a.capCmd} cap`/`on`."))
      return none
    -- what it waits on, read from the ledger at most once a minute, said again when the reason changes
    let now ← h.now
    if told.isNone || now - lastWhy ≥ 60 then
      lastWhy := now
      let mut parts : List String := []
      for (c, x) in seen do
        let why ← match x with
          | .wait fc fm ah => do
            let l := parseLs ((← call h c ["ls"]).getD "")
            pure ((l.bind (·.waitLine now a.id)).getD s!"{fc} cores, {gi fm}G free, {ah} ahead")
          | _ => pure "no room"
        parts := parts ++ [s!"{nameOf c}: {why}"]
      let line := s!"{a.prog}: waiting for room: " ++ "; ".intercalate parts
      if told.map waitKey != some (waitKey line) then
        h.err line
        told := some line
    h.sleep a.pollMs
  let some (chosen, got, mem) := won | return none
  for c in a.usable do if c != chosen then release h c a.id
  return some (chosen, got, mem)

/-- The environment of a job that holds `cs` cores and `mem_kb`, on top of `nixConfig` (NIX_CONFIG as it is). -/
def jobEnv (cs : String) (mem_kb : Int) (nixConfig : Option String) : List (String × String) :=
  [("SWARM_CORES", cs), ("SWARM_MEM_KB", toString mem_kb), ("MAKEFLAGS", "-j" ++ cs), ("CARGO_BUILD_JOBS", cs),
    ("NIX_BUILD_CORES", cs), ("NIX_CONFIG", (match nixConfig with | some x => x ++ "\n" | none => "") ++ s!"cores = {cs}\nmax-jobs = 1")]

end Claims
