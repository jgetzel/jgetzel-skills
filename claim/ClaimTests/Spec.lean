import ClaimTests.Harness
import ClaimTests.Script
import Claims.Admit

/-! sw-compute-backfill.md §7, the `claims_spec` group: the shipped script against the model `Claims.Admit`, the cases
of the assumption `ScriptAdmits` (Claims/Assumptions.lean). `admit_awk` runs `ADMIT_AWK` alone on 2000 generated cases,
`script_try` runs `try` whole on 60 of them against a scratch ledger; both start with the desktop's case.
`lock_exclusive` is the 50 claims at once against a stale lock, for `LockExclusive`. -/

namespace Claims.Tests.Spec
open Claims.Tests.Script
open Claims Claims.Admit Claims.Tests

/-- A fixed-seed LCG (Knuth's MMIX constants): the same cases on every run. -/
abbrev Gen := StateM UInt64

/-- A draw in `0 .. n-1`. -/
def nat (n : Nat) : Gen Nat := do
  let s := (← get) * 6364136223846793005 + 1442695040888963407
  set s
  return (s >>> 33).toNat % n

/-- A draw in `a .. b`. -/
def range (a b : Int) : Gen Int := return a + (← nat (b - a + 1).toNat)

/-- True `k` times in `n`. -/
def chance (k n : Nat) : Gen Bool := return (← nat n) < k

/-- KiB per memory unit: the generator draws memory in MiB so the interesting regions are dense. -/
def U : Int := 1024

def NOW : Int := 1000000

/-- One case: the machine and ledger, and the request. -/
def gen : Gen (Machine × Req) := do
  let ncpu ← range 1 12
  let total := U * (← range 1 16)
  -- half the machines are calm (no cap, no reservation, idle, all memory available), where heads are seldom held and
  -- backfill decides; the rest draw every limit
  let calm ← chance 1 2
  let avail ← do if calm then pure total else (U * ·) <$> range 0 (total / U)
  let cap ← do
    if calm || (← chance 1 2) then pure (none, none) else
      let c ← do if ← chance 1 3 then pure none else some <$> range 0 14
      let g ← do if ← chance 1 3 then pure none else some <$> (U * ·) <$> range 0 14
      pure (c, g)
  let res ← do if calm || (← chance 1 2) then pure (0, 0) else pure (← range 0 14, U * (← range 0 14))
  let busy ← do if calm || (← chance 1 2) then pure 0 else range 0 (ncpu * 100)
  let off ← chance 1 20
  let nclaims ← nat 5
  let claims ← (List.range nclaims).mapM fun _ => do
    let est ← do if ← chance 1 3 then pure none else some <$> range 1 200
    pure (⟨← range 1 (min 6 ncpu), U * (← range 0 3), ← range (NOW - 60) NOW, est⟩ : Admit.Claim)
  -- tickets named from a pool of five, each name once (they are file names)
  let pool := ["a", "b", "c", "d", "e"]
  let n ← nat 5
  let ids ← (List.range n).foldlM (fun (acc : List String) _ => do
    let left := pool.filter (!acc.contains ·)
    pure (acc ++ [left[← nat left.length]!])) []
  let tickets ← ids.mapM fun id => do
    -- most of them big for the machine, so a head often waits for a claim to end
    let cores ← do
      if ← chance 1 5 then pure none else if ← chance 1 4 then some <$> range 1 (min 9 ncpu) else some <$> range ((ncpu + 1) / 2) ncpu
    let mem ← do if cores.isSome then (U * ·) <$> range 0 (total / U / 2) else pure 0
    -- a third with the yield's clock running, about half of those past it
    let since ← do if ← chance 1 3 then some <$> range (NOW - 2 * Admit.YIELD) NOW else pure none
    pure (⟨id, ← range (NOW - 5) NOW, cores, mem, since⟩ : Admit.Ticket)
  let id ← do
    if !ids.isEmpty && (← chance 1 2) then pure ids[← nat ids.length]! else pure (pool.filter (!ids.contains ·) ++ ["r"])[0]!
  -- the request: often small and short, the job backfill is for
  let cores ← do
    if ← chance 1 5 then pure none else if ← chance 1 2 then some <$> range 1 2 else some <$> range 1 (min 9 ncpu)
  let mem ← do if cores.isSome then (U * ·) <$> range 0 (total / U / 2) else pure 0
  let est ← do if ← chance 1 3 then pure none else if ← chance 1 2 then some <$> range 1 60 else some <$> range 1 200
  let m : Machine := { ncpu, total, busy, avail, cap, res, off, now := NOW, claims, tickets }
  let r : Req := { id, cores, mem, est }
  -- one case in four is backfill's own: a calm machine whose claims carry estimates, an older head that needs the whole
  -- machine (sized, or exclusive in one of three) and a one-core request with a short estimate behind it
  -- an exclusive request finds an empty ledger in one case of two, so some are granted
  -- one case in six of the rest is the yield's own: a calm machine but for unclaimed use, mostly no claim, an older
  -- exclusive head whose clock may run or be past the yield, and a request that is exclusive, the whole machine sized, or
  -- one core (mostly without an estimate), often with its own ticket and clock
  if !(← chance 1 4) then
    if !(← chance 1 6) then return (if cores.isNone && (← chance 1 2) then { m with claims := [] } else m, r)
    let busy ← range (ncpu * 40) (ncpu * 100)
    let claims ← do if ← chance 1 4 then pure claims else pure []
    let hs ← do if ← chance 1 2 then some <$> range (NOW - 2 * Admit.YIELD) NOW else pure none
    let k ← nat 3
    let rc := if k == 0 then none else if k == 1 then some ncpu else some 1
    let est ← do if rc == some 1 && (← chance 2 3) then pure none else some <$> range 1 200
    let os ← do if ← chance 2 3 then some <$> range (NOW - 2 * Admit.YIELD) NOW else pure none
    let own : List Admit.Ticket ← do
      if ← chance 2 3 then pure [⟨"r", NOW - 10, rc, 0, os⟩] else pure []
    let m : Machine := { m with busy, claims, avail := total, cap := (none, none), res := (0, 0), off := false }
    let m : Machine := { m with tickets := ⟨"a", NOW - 30, none, 0, hs⟩ :: own }
    return (m, { id := "r", cores := rc, mem := 0, est })
  let excl ← chance 1 3
  let e ← range 1 60
  let claims := claims.map fun c => { c with est := some (c.est.getD 100) }
  let tickets := (⟨"a", NOW - 5, if excl then none else some ncpu, 0, none⟩ : Admit.Ticket) :: tickets.filter (·.id != "a")
  -- in half of them unclaimed use keeps the head off too, which no longer holds it
  let cc := (claims.map (·.cores)).sum
  let busy ← do if ← chance 1 2 then pure 0 else range (100 * cc) (100 * max cc ncpu)
  let m : Machine := { m with busy, avail := total, cap := (none, none), res := (0, 0), off := false }
  let m : Machine := { m with claims, tickets }
  return (m, { id := "r", cores := some 1, mem := 0, est := some e })

def GiB : Int := 1048576

/-- The desktop on 2026-11-15: 12 free cores and 23 GiB available, two 4-core claims (one with no estimate) and unclaimed
use; the oldest ticket asks 8 cores and 30 GiB, more memory than it could have with every claim ended (23 + 4), so it is
held, and the 3-core 12 GiB request behind it, three hours waiting, is granted. -/
def desktop : Machine × Req :=
  ({ ncpu := 24, total := 64 * GiB, busy := 1500, avail := 23 * GiB, cap := (none, none), res := (0, 0), off := false,
     now := NOW, claims := [⟨4, 2 * GiB, NOW - 600, some 1200⟩, ⟨4, 2 * GiB, NOW - 60, none⟩],
     tickets := [⟨"old", NOW - 10860, some 8, 30 * GiB, none⟩, ⟨"young", NOW - 10800, some 3, 12 * GiB, none⟩] },
   { id := "young", cores := some 3, mem := 12 * GiB, est := none })

/-- The user's Slurm-style rule (2026-11-21): a whole-machine head that a claim ending in 90 s and unclaimed use keep off
(8 cores, a 6-core claim, 8 busy: 1 past the noise floor; it was held before). A younger 1-core job without an estimate
waits, one whose 50 s end before the head's shadow is granted, one of 200 s waits; ten minutes blocked only by unclaimed
use with no claim, the head yields and the job without an estimate is granted. -/
def slurm : List (Machine × Req) :=
  let m : Machine := { desktop.1 with ncpu := 8, total := 16 * GiB, busy := 800, avail := 16 * GiB }
  let m : Machine := { m with claims := [⟨6, GiB, NOW, some 90⟩], tickets := [⟨"head", NOW - 60, none, 0, none⟩] }
  let r (e : Option Int) : Req := { id := "young", cores := some 1, mem := 0, est := e }
  let y : Machine := { m with busy := 300, claims := [], tickets := [⟨"head", NOW - 900, none, 0, some (NOW - Admit.YIELD)⟩] }
  [(m, r none), (m, r (some 50)), (m, r (some 200)), (y, r none), ({ y with tickets := [⟨"head", NOW - 900, none, 0, some (NOW - 10)⟩] }, r none)]

/-- The desktop's case and the Slurm-style ones first, then 1994 generated ones. -/
def cases : List (Machine × Req) := desktop :: (slurm ++ Id.run (((List.range 1994).mapM (fun _ => gen)).run' 20261115))

/-- Hundredths as the script's `%.2f`. -/
def hund (b : Int) : String := s!"{b / 100}.{if b % 100 < 10 then "0" else ""}{b % 100}"

def optS (o : Option Int) (none_ : String) : String := o.elim none_ toString

/-- A claim line, live (holder `t` past now), with `~est` when it has one. -/
def claimLine (m : Machine) (c : Admit.Claim) : String :=
  s!"{c.cores} {c.mem} t{m.now + 100000} {c.start} {c.est.elim "" (s!"~{·} ")}w cmd"

def ticketLine (t : Admit.Ticket) : String := s!"{t.first} {optS t.cores "all"} {t.mem} {t.since.elim "" (s!"@{·} ")}w"

/-- The awk's stdin. -/
def input (m : Machine) : String :=
  String.join (m.claims.map (s!"c {claimLine m ·}\n")) ++ String.join (m.tickets.map fun t => s!"q {t.id} {ticketLine t}\n")

/-- The awk's `-v` variables, as `try` sets them. -/
def vars (m : Machine) (r : Req) : List String :=
  [s!"now={m.now}", s!"ncpu={m.ncpu}", s!"total={m.total}", s!"busy={hund m.busy}", s!"avail={m.avail}",
   s!"capc={capC m}", s!"capm={capM m}", s!"resc={m.res.1}", s!"resm={m.res.2}", s!"limc={limC m}", s!"limm={limM m}",
   s!"off={if m.off then 1 else 0}", s!"id={r.id}", s!"first={first m r}", s!"since={optS (ownSince m r) ""}", s!"cores={optS r.cores "all"}",
   s!"mem={r.mem}", s!"est={optS r.est "-"}"].flatMap fun v => ["-v", v]

def showClaim (c : Admit.Claim) : String := s!"⟨{c.cores}, {c.mem}, {c.start}, {repr c.est}⟩"
def showTicket (t : Admit.Ticket) : String := s!"⟨{t.id.quote}, {t.first}, {repr t.cores}, {t.mem}, {repr t.since}⟩"

/-- The case as Lean, for a mismatch. -/
def showCase (m : Machine) (r : Req) : String :=
  s!"(\{ ncpu := {m.ncpu}, total := {m.total}, busy := {m.busy}, avail := {m.avail}, cap := {repr m.cap}, " ++
  s!"res := {repr m.res}, off := {m.off}, now := {m.now}, claims := [{", ".intercalate (m.claims.map showClaim)}], " ++
  s!"tickets := [{", ".intercalate (m.tickets.map showTicket)}] }, \{ id := {r.id.quote}, cores := {repr r.cores}, " ++
  s!"mem := {r.mem}, est := {repr r.est} })"

/-- What the coverage counts: each region of the rule the generator must keep reaching. -/
def regions (m : Machine) (r : Req) : List String :=
  let d := Admit.decide m r
  let ahead := !(aheadOf m r).isEmpty
  let ok := d matches .ok ..
  let others := m.tickets.filter (·.id != r.id)
  (if ok && ahead then ["backfill grant"] else []) ++
  (if !m.off && !tooBig m r && fitsNow m r && ahead && !ok then ["backfill refusal"] else []) ++
  ((others.filter fun t => t.cores.isSome && held m t).map fun _ => "held sized ticket") ++
  ((others.filter fun t => t.cores.any (fun c => c ≤ limC m && t.mem ≤ limM m) && held m t).map
    fun _ => "held sized ticket by memory or the yield") ++
  ((others.filter fun t => t.cores.isNone && held m t).map fun _ => "held exclusive ticket") ++
  ((others.filter fun t => yielded m t).map fun _ => "yielded ticket") ++
  ((others.filter fun t => t.since.isSome && !yielded m t && !held m t).map fun _ => "ticket with the yield's clock running") ++
  (if (head m r).isSome && outside m > 0 && !m.off && !tooBig m r then ["head with unclaimed use"] else []) ++
  (if ok && ahead && outside m > 0 then ["backfill grant past unclaimed use"] else []) ++
  (if !ok && ahead && outside m > 0 && r.est.isNone && fitsNow m r && !m.off && !tooBig m r then ["no estimate waits past unclaimed use"] else []) ++
  (if (d matches .wait ..) && (sinceOf m r).isSome && ownSince m r == none then ["since started"] else []) ++
  (if (d matches .wait ..) && (sinceOf m r).isSome && (ownSince m r).isSome then ["since kept"] else []) ++
  (if (d matches .wait ..) && (sinceOf m r).isNone && (ownSince m r).isSome then ["since cleared"] else []) ++
  (if ok && r.cores.isNone then ["exclusive grant"] else []) ++
  (if ok && ahead && (head m r).any (·.cores.isNone) then ["backfill grant past an exclusive head"] else []) ++
  (if d matches .never .. then ["never"] else []) ++ (if d matches .off then ["off"] else [])

def test_admit_awk (t : T) : IO Unit := do
  -- one sh runs every case's awk: the program is $1, each case's lines a printf
  let sh := String.join (cases.map fun (m, r) =>
    s!"printf '{(input m).replace "\n" "\\n"}' | LC_ALL=C awk {" ".intercalate (vars m r)} \"$1\"\n")
  put (t.d ++ "/cases.sh") sh
  let out ← t.exec ["sh", t.d ++ "/cases.sh", ADMIT_AWK]
  unless out.code == 0 && out.stderr.isEmpty do fail s!"the awk failed ({out.code}): {out.stderr}"
  let got := splitlines out.stdout
  eq got.length cases.length "one line per case"
  for ((m, r), g) in cases.zip got do
    let want := Admit.awkLine m r
    unless g == want do
      fail s!"ADMIT_AWK says {g.quote}, the model {want.quote}\n  case {showCase m r}\n  printf '{(input m).replace "\n" "\\n"}' | LC_ALL=C awk {" ".intercalate (vars m r)} \"$ADMIT_AWK\""
  eq (Admit.decide desktop.1 desktop.2).line s!"ok 3 {12 * GiB}" "the desktop's case"
  eq (slurm.map fun (m, r) => (Admit.decide m r).line) ["wait 1 15728640 1", "ok 1 0", "wait 1 15728640 1", "ok 1 0", "wait 6 16777216 1"]
    "the Slurm-style cases"
  let counts := (cases.flatMap fun (m, r) => regions m r).foldl (fun (acc : List (String × Nat)) k =>
    match acc.find? (·.1 == k) with
    | some _ => acc.map fun (k', n) => if k' == k then (k', n + 1) else (k', n)
    | none => acc ++ [(k, 1)]) []
  let names := ["backfill grant", "backfill refusal", "held sized ticket", "held sized ticket by memory or the yield",
    "held exclusive ticket", "exclusive grant", "backfill grant past an exclusive head", "never", "off", "yielded ticket",
    "ticket with the yield's clock running", "head with unclaimed use", "backfill grant past unclaimed use",
    "no estimate waits past unclaimed use", "since started", "since kept", "since cleared"]
  for k in names do
    let n := ((counts.find? (·.1 == k)).map (·.2)).getD 0
    if n < 20 then fail s!"coverage: {n} cases of {k}, under 20; counts {counts}"

/-- The ledger's claims as `(cores, mem, start, est)` and its tickets as `(id, first, cores, mem, since)`, sorted. -/
def rows (m : Machine) : List String × List String :=
  ((m.claims.map fun c => s!"{c.cores} {c.mem} {c.start} {optS c.est "-"}").mergeSort (· ≤ ·),
   (m.tickets.map fun t => s!"{t.id} {t.first} {optS t.cores "all"} {t.mem} {optS t.since "-"}").mergeSort (· ≤ ·))

/-- What `try` left in the ledger dir `d`, as `rows` shows it. -/
def ledger (d : String) : IO (List String × List String) := do
  let names (sub : String) : IO (List String) := do
    let es ← System.FilePath.readDir (d ++ "/" ++ sub)
    return (es.toList.map (·.fileName)).filter (!·.startsWith ".")
  let cs ← (← names "claims").mapM fun f => do
    let w := words (← IO.FS.readFile s!"{d}/claims/{f}")
    let est := (w.getD 4 "").dropWhile (· == '~')
    return s!"{w.getD 0 ""} {w.getD 1 ""} {w.getD 3 ""} {if (w.getD 4 "").startsWith "~" then est.toString else "-"}"
  let ts ← (← names "queue").mapM fun f => do
    let w := words (← IO.FS.readFile s!"{d}/queue/{f}")
    let s := w.getD 3 ""
    return s!"{f} {w.getD 0 ""} {w.getD 1 ""} {w.getD 2 ""} {if s.startsWith "@" then (s.drop 1).toString else "-"}"
  return (cs.mergeSort (· ≤ ·), ts.mergeSort (· ≤ ·))

def test_script_try (t : T) : IO Unit := do
  -- the first 45 cases and the next 15 exclusive requests
  let picked := cases.take 45 ++ ((cases.drop 45).filter (·.2.cores.isNone)).take 15
  for ((m, r), i) in picked.zip (List.range picked.length) do
    let d := s!"{t.d}/c{i}"
    mkdir (d ++ "/claims"); mkdir (d ++ "/queue")
    if m.cap != (none, none) then put (d ++ "/cap") s!"{optS m.cap.1 "-"} {optS m.cap.2 "-"}\n"
    if m.res != (0, 0) then put (d ++ "/reserve") s!"{m.res.1} {m.res.2}\n"
    if m.off then put (d ++ "/off") ""
    for (c, j) in m.claims.zip (List.range m.claims.length) do put s!"{d}/claims/k{j}" (claimLine m c ++ "\n")
    for q in m.tickets do put s!"{d}/queue/{q.id}" (ticketLine q ++ "\n")
    put (d ++ "/stat") ("cpu  0 0 0 0 0 0 0 0 0 0\n" ++ String.join ((List.range m.ncpu.toNat).map fun k => s!"cpu{k} 0 0 0 0 0 0 0 0 0 0\n"))
    put (d ++ "/meminfo") s!"MemTotal:       {m.total} kB\nMemAvailable:   {m.avail} kB\n"
    let out ← t.exec ["sh", "-c", SCRIPT, "sh", "try", r.id, optS r.cores "all", toString r.mem, optS r.est "-", "t", "w", "cmd"]
      [("SWARM_COMPUTE_DIR", some d), ("SWARM_COMPUTE_NOW", some (toString m.now)), ("SWARM_COMPUTE_BUSY", some (hund m.busy)),
       ("SWARM_COMPUTE_STAT", some (d ++ "/stat")), ("SWARM_COMPUTE_MEM", some (d ++ "/meminfo"))]
    let want := (Admit.decide m r).line
    unless strip out.stdout == want do
      fail s!"try says {(strip out.stdout).quote} ({out.code}, {out.stderr.quote}), the model {want.quote}\n  case {showCase m r}"
    let got ← ledger d
    unless got == rows (Admit.after m r) do
      fail s!"try left {repr got}, the model {repr (rows (Admit.after m r))}\n  case {showCase m r}"

def tests : List Case := [("admit_awk", test_admit_awk), ("script_try", test_script_try),
  ("lock_exclusive", Script.test_script_50_stale_lock_one_winner)]

end Claims.Tests.Spec
