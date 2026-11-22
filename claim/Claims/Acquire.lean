import Claims.Ledger

/-! The claim loop of `swarm run` and `claim run`: try each usable machine, wait for room, give up when nothing can ever
fit. -/

namespace Claims

/-- How long (s) every machine a sized request waits on must find it short of memory by unclaimed use (`Ls.memShort`)
before `acquire` lowers a defaulted size or refuses a given one (board #104). -/
def STEADY : Int := 120

/-- The least memory (KiB) `acquire` lowers a defaulted size to: 1 GiB. -/
def MIN_LOWER : Int := 1048576

/-- What `acquire` does with a sized request short of memory by unclaimed use on every machine it waits on, after `held`
of `steady` seconds, with `room` the most any of them could give it: wait `left` seconds more, lower a defaulted size
(`fixed` false) to nine tenths of the room (available memory moves) when that is at least `MIN_LOWER`, or refuse. -/
inductive Short | wait (left : Int) | lower (memKb : Int) | refuse
  deriving BEq, Repr

def short (fixed : Bool) (room held steady : Int) : Short :=
  if held < steady then .wait (steady - held)
  else if fixed || room * 9 / 10 < MIN_LOWER then .refuse
  else .lower (room * 9 / 10)

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
  /-- `cores` and `mem_kb` were asked for (`--cores`, `--mem`); a defaulted one is lowered to a cap it is over, and memory
  to what unclaimed use leaves (`short`) -/
  coresFixed : Bool := true
  memFixed : Bool := true
  steadyS : Int := STEADY

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
when nothing can ever run it. The claims on the machines not chosen are released. A request no machine can ever fit does
not wait: a defaulted size over the cap is lowered to it, and a sized request short of memory by unclaimed use on every
machine it waits on for `steadyS` is lowered or refused (`short`), each with a stderr line; the wait line says which. -/
def acquire {m : Type → Type} [Monad m] (h : Host m) (a : Ask) : m (Option (Option String × Int × Int)) := do
  let nameOf (c : Option String) := c.getD "here"
  let mut won : Option (Option String × Int × Int) := none
  let mut first := true
  let mut told : Option String := none
  let mut lastWhy : Int := 0
  let mut order := a.usable
  let mut cores := a.cores
  let mut mem := a.mem_kb
  let mut shortSince : Option Int := none
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
      let r := parseTry ((← call h c ["try", a.id, cores, toString mem, (a.est.elim "-" toString), holder, a.who, a.cmd]).getD "")
      match r with
      | .ok n g => won := some (c, n, g)
      | .gone => gone := true
      | x => seen := seen ++ [(c, x)]
    if won.isSome then break
    let anyWait := seen.any fun (_, x) => match x with | .wait .. => true | _ => false
    let isFirst := first
    first := false
    if !anyWait && (isFirst || !gone) then
      -- a defaulted size over a machine's cap: lowered to the cap
      let capped := seen.findSome? fun (c, x) => match x, cores.toInt? with
        | .never capc capm, some n =>
          let n' := if a.coresFixed then n else min n capc
          let g' := if a.memFixed then mem else min mem capm
          if 1 ≤ n' && n' ≤ capc && g' ≤ capm && (n' != n || g' != mem) then some (c, capc, capm, n', g') else none
        | _, _ => none
      if let some (c, x, y, n', g') := capped then
        h.err s!"{a.prog}: claiming {n'} cores, {gi g'}G, not {cores} cores, {gi mem}G: {nameOf c}'s cap is {x} cores, {gi y}G"
        cores := toString n'
        mem := g'
        first := true
        continue
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
      -- per machine waited on: the room it could give when it finds the request short of memory by unclaimed use
      let mut rooms : List (Option Int) := []
      for (c, x) in seen do
        match x with
        | .wait fc fm ah =>
          let l := parseLs ((← call h c ["ls"]).getD "")
          rooms := rooms ++ [if cores == "all" then none else l.bind fun l => if l.memShort mem then some (l.memRoom now) else none]
          parts := parts ++ [s!"{nameOf c}: " ++ ((l.bind (·.waitLine now a.id)).getD s!"{fc} cores, {gi fm}G free, {ah} ahead")]
        | _ => parts := parts ++ [s!"{nameOf c}: no room"]
      let room := if !rooms.isEmpty && rooms.all (·.isSome) then (rooms.filterMap id).max? else none
      let mut tail := ""
      match room with
      | none => shortSince := none
      | some room =>
        let since := shortSince.getD now
        shortSince := some since
        let why := s!"unclaimed use leaves at most {gi room}G with every claim ended"
        match short a.memFixed room (now - since) a.steadyS with
        | .wait left =>
          let act := (match short a.memFixed room a.steadyS a.steadyS with | .lower kb => s!"lowered to {gi kb}G" | _ => "refused")
          tail := s!"; {why}: {act} in {spanHM left}" ++ (if a.memFixed then " (--mem was given)" else "")
        | .lower kb =>
          h.err s!"{a.prog}: claiming {gi kb}G, not {gi mem}G: {why}, for {spanHM (now - since)}; the job may use more than it claims"
          mem := kb
          shortSince := none
          told := none
          continue
        | .refuse =>
          for c in a.usable do release h c a.id
          h.err (s!"{a.prog}: nothing can run this job: it needs {gi mem}G, and {why}, for {spanHM (now - since)}" ++
            (if a.memFixed then ". Lower --mem." else s!", under the {gi MIN_LOWER}G it could be lowered to."))
          return none
      let line := s!"{a.prog}: waiting for room: " ++ "; ".intercalate parts ++ tail
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
