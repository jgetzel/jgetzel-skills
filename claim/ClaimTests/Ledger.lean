import Claims.Ledger

/-! The script's answers and the `ls` rendering, as pure functions (moved from swarm's Tests/Compute.lean). -/

open Claims

#guard parseTry "ok 4 1024" == .ok 4 1024
#guard parseTry "ok 4" == .gone
#guard parseTry "wait 2 1024 3" == .wait 2 1024 3
#guard parseTry "never 8 16" == .never 8 16
#guard parseTry "off" == .off
#guard parseTry "" == .gone
#guard parseTry "wait 2" == .gone

def lsSample : String := "24 9.30 25165824 15000000 24 25165824 0 4 8388608
c 6 8388608 p31 700 ~600 sr-3 nix build .#x
c 2 2097152 t999 800 sr-5 cargo test
q t1 880 22 2097152 sr-7
q t2 890 all 0 bench
"

#guard (parseLs lsSample).map (fun l => (l.ncpu, l.cap_mem_kb, l.off, l.res_cores, l.res_mem_kb, l.claims.length, l.queue.length)) == some (24, 25165824, false, 4, 8388608, 2, 2)
-- a claim with `~600` has its estimate and its who; one without has none
#guard (parseLs lsSample).bind (·.claims.head?) == some { cores := 6, mem_kb := 8388608, holder := "p31", start := 700, est := some 600, who := "sr-3", cmd := "nix build .#x" }
#guard ((parseLs lsSample).bind (·.claims[1]?)).map (fun c => (c.est, c.who, c.cmd)) == some (none, "sr-5", "cargo test")
-- a ticket with `all` is exclusive
#guard ((parseLs lsSample).map (·.queue.map (·.cores))) == some [some 22, none]
#guard (parseLs "1 2").isNone
-- only a binary's own script's header: 7 fields are no longer one
#guard (parseLs "8 0.00 100 100 8 100 0\n").isNone
#guard ((parseLs lsSample).map (render "here" · 1000)) == some [
  "here: 8 of 20 cores claimed (cap 24 of 24, 4 reserved, 9.3 busy), 10.0 of 16.0G claimed (8.0G reserved, 14.3G available)",
  "  sr-3   6 cores  8.0G  5m of ~10m  nix build .#x",
  "  sr-5   2 cores  2.0G  3m  cargo test",
  "  waiting: sr-7 22 cores 2.0G 2m, held by the reservation",
  "  waiting: bench whole machine 1m, held: reserved"]
#guard ((parseLs "8 0.00 100 100 8 100 1 0 0\n").map (render "desktop" · 0)) == some ["desktop: off"]
-- nothing reserved, nothing held
#guard ((parseLs "8 0.00 16777216 16777216 8 16777216 0 0 0\nq b 5 all 0 b\n").map (render "here" · 65)) == some [
  "here: 0 of 8 cores claimed (cap 8 of 8, 0.0 busy), 0.0 of 16.0G claimed (16.0G available)",
  "  waiting: b whole machine 1m"]
-- an exclusive waiter under a cap below the machine, with unclaimed use: every reason
#guard ((parseLs "8 4.00 16777216 16777216 4 16777216 0 1 0\nq b 5 all 0 b\n").map (render "here" · 5)) == some [
  "here: 0 of 4 cores claimed (cap 4 of 8, 1 reserved, 4.0 busy), 0.0 of 16.0G claimed (16.0G available)",
  "  waiting: b whole machine 0s, held: reserved, cap below the machine"]
-- unclaimed use alone holds no one (2026-11-21); the yield does, ten minutes on
#guard ((parseLs "8 4.00 16777216 16777216 8 16777216 0 0 0\nq b 5 all 0 @5 b\n").map (render "here" · 300 |>.getLast!)) ==
  some "  waiting: b whole machine 4m"
#guard ((parseLs "8 4.00 16777216 16777216 8 16777216 0 0 0\nq b 5 all 0 @5 b\n").map (render "here" · 605 |>.getLast!)) ==
  some "  waiting: b whole machine 10m, held: 4.0 cores unclaimed use"
#guard ((parseLs "8 4.00 16777216 16777216 8 16777216 0 0 0\nq b 5 all 0 @5 b\n").map (·.queue.map (·.since))) == some [some 5]
#guard ((parseLs lsSample).map (·.json 1000 |>.compress |>.splitOn "\"limit_cores\":20" |>.length)) == some 2
#guard ((parseLs lsSample).map (·.json 1000 |>.compress |>.splitOn "\"est_s\":600" |>.length)) == some 2
#guard ((parseLs lsSample).map (·.json 1000 |>.compress |>.splitOn "\"est_s\":null" |>.length)) == some 2
#guard ((parseLs lsSample).map (·.json 1000 |>.compress |>.splitOn "\"exclusive\":true,\"first\":890,\"held\":true,\"id\":\"t2\"" |>.length)) == some 2

open Claims.Admit in
/-- An idle 8-core, 16-unit machine at t = 1000 with no cap, no reservation and an empty ledger. -/
def idle : Machine :=
  { ncpu := 8, total := 16, busy := 0, avail := 16, cap := (none, none), res := (0, 0), off := false, now := 1000, claims := [],
    tickets := [] }

open Claims.Admit in
def req (cores : Option Int) (est : Option Int) : Req := { id := "r", cores, mem := 1, est }

open Claims.Admit in
/-- The §2.2 example: a 6-core claim ending in 90 s, an 8-core head waiting. -/
def ex : Machine := { idle with claims := [⟨6, 1, 1000, some 90⟩], tickets := [⟨"h", 990, some 8, 1, none⟩] }

open Claims.Admit in
#guard (decide ex (req (some 2) (some 50))).line == "ok 2 1"
open Claims.Admit in
#guard (decide ex (req (some 2) (some 200))).line == "wait 2 15 1"
open Claims.Admit in
#guard (decide ex (req (some 2) none)).line == "wait 2 15 1"
-- the claim has no estimate: the head's start is unknown, nothing passes it
open Claims.Admit in
#guard (decide { ex with claims := [⟨6, 1, 1000, none⟩] } (req (some 2) (some 1))).line == "wait 2 15 1"
-- a held sized ticket (more than the limit) is not ahead
open Claims.Admit in
#guard (decide { ex with tickets := [⟨"h", 990, some 9, 1, none⟩] } (req (some 2) none)).line == "ok 2 1"
-- the oldest ticket first, the id breaking a tie bytewise
open Claims.Admit in
#guard (decide { idle with tickets := [⟨"a", 1000, some 1, 1, none⟩] } (req (some 1) none)).line == "wait 8 16 1"
open Claims.Admit in
#guard (decide { idle with tickets := [⟨"s", 1000, some 1, 1, none⟩] } (req (some 1) none)).line == "ok 1 1"
-- off and never
open Claims.Admit in
#guard (decide { idle with off := true } (req (some 1) none)).line == "off"
open Claims.Admit in
#guard (decide { idle with cap := (some 4, none) } (req (some 5) none)).line == "never 4 16"
-- a reservation of 4 of 8: a 6-core request is held, a 2-core one runs
open Claims.Admit in
#guard (decide { idle with res := (4, 0), tickets := [⟨"h", 990, some 6, 1, none⟩] } (req (some 2) none)).line == "ok 2 1"
open Claims.Admit in
#guard limC { idle with res := (4, 0), cap := (some 6, none) } == 4 && limM { idle with res := (0, 20) } == 0

-- exclusive: an empty quiet machine
open Claims.Admit in
#guard (decide idle (req none none)).line == "ok 8 16"
open Claims.Admit in
#guard (decide { idle with claims := [⟨1, 1, 1000, none⟩] } (req none none)).line == "wait 7 15 0"
open Claims.Admit in
#guard (decide { idle with cap := (some 4, some 8) } (req none none)).line == "never 4 8"
-- an exclusive head behind a 6-core claim ending in 90 s: a 2-core est-50 request passes it, an est-200 one waits
open Claims.Admit in
def exx : Machine := { idle with claims := [⟨6, 1, 1000, some 90⟩], tickets := [⟨"h", 990, none, 0, none⟩] }
open Claims.Admit in
#guard (decide exx (req (some 2) (some 50))).line == "ok 2 1"
open Claims.Admit in
#guard (decide exx (req (some 2) (some 200))).line == "wait 2 15 1"
-- a reservation holds the exclusive ticket: a younger 2-core request without an estimate runs
open Claims.Admit in
#guard (decide { idle with res := (1, 0), tickets := [⟨"h", 990, none, 0, none⟩] } (req (some 2) none)).line == "ok 2 1"
-- unclaimed use does not (2026-11-21): the head keeps its place, and with no claim its shadow is now, so nothing passes
open Claims.Admit in
#guard (decide { idle with busy := 300, tickets := [⟨"h", 990, none, 0, none⟩] } (req (some 2) none)).line == "wait 6 16 1"
open Claims.Admit in
#guard (decide { idle with busy := 300, tickets := [⟨"h", 990, none, 0, none⟩] } (req (some 2) (some 50))).line == "wait 6 16 1"
-- ten minutes blocked only by unclaimed use, it yields: held, and the younger request runs
open Claims.Admit in
#guard (decide { idle with busy := 300, tickets := [⟨"h", 990, none, 0, some 400⟩] } (req (some 2) none)).line == "ok 2 1"
open Claims.Admit in
#guard (decide { idle with busy := 300, tickets := [⟨"h", 990, none, 0, some 401⟩] } (req (some 2) none)).line == "wait 6 16 1"
-- unclaimed use and a claim ending in 90 s keep the head off: a younger job ending by then passes it, one without an
-- estimate or ending later waits (the old rule held this head and let both run)
open Claims.Admit in
def exo : Machine := { exx with busy := 800 }
open Claims.Admit in
#guard (decide exo (req (some 1) (some 50))).line == "ok 1 1" && (decide exo (req (some 1) none)).line == "wait 1 15 1" &&
  (decide exo (req (some 1) (some 200))).line == "wait 1 15 1"
-- the yield's clock: an exclusive request on a machine with no claim and unclaimed use starts it, keeps it, and a claim
-- clears it
open Claims.Admit in
#guard ((after { idle with busy := 300 } (req none none)).tickets.map (·.since)) == [some 1000]
open Claims.Admit in
#guard ((after { idle with busy := 300, tickets := [⟨"r", 900, none, 0, some 950⟩] } (req none none)).tickets.map (·.since)) == [some 950]
open Claims.Admit in
#guard ((after { idle with busy := 300, claims := [⟨1, 1, 1000, none⟩], tickets := [⟨"r", 900, none, 0, some 950⟩] } (req none none)).tickets.map (·.since)) == [none]
open Claims.Admit in
#guard ((after { idle with claims := [⟨1, 1, 1000, none⟩] } (req none none)).tickets.map (·.since)) == [none]
-- a sized request: more cores than unclaimed use leaves, within the cap
open Claims.Admit in
#guard ((after { idle with busy := 300 } (req (some 7) none)).tickets.map (·.since)) == [some 1000]
-- an ncpu-core claim live: nothing else fits
open Claims.Admit in
#guard (decide { idle with claims := [⟨8, 1, 1000, none⟩] } (req (some 1) none)).line == "wait 0 15 0"
-- after: a grant adds the claim with its estimate, a wait writes the ticket
open Claims.Admit in
#guard ((after ex (req (some 2) (some 50))).claims.map (·.est)) == [some 90, some 50]
open Claims.Admit in
#guard ((after ex (req (some 2) (some 200))).tickets.map (·.id)) == ["h", "r"]

-- the desktop (2026-11-15): 12 free cores, 23 GiB available. The oldest ticket asks 8 cores and 30 GiB, more than it could
-- have with every claim ended (23 + 4 GiB), so it is held, and the 3-core 12 GiB request behind it runs
-- a queued note is shown after the tickets, and moves nothing
#guard ((parseLs "8 0.00 16777216 16777216 8 16777216 0 0 0\nq w 989140 2 1024 w\nn t9999999 1200 999280 hpl-1414 timing-queue timing run\n").map
  (render "desktop" · 1000000 |>.drop 1)) == some ["  waiting: w 2 cores 0.0G 3h", "  queued: hpl-1414 timing run (owner timing-queue) ~20m, since 12m"]

open Claims.Admit in
def desk : Machine :=
  { ncpu := 24, total := 67108864, busy := 1500, avail := 24117248, cap := (none, none), res := (0, 0), off := false,
    now := 1000000, claims := [⟨4, 2097152, 999400, some 1200⟩, ⟨4, 2097152, 999940, none⟩],
    tickets := [⟨"old", 989140, some 8, 31457280, none⟩, ⟨"young", 989200, some 3, 12582912, none⟩] }
open Claims.Admit in
#guard held desk ⟨"old", 989140, some 8, 31457280, none⟩ && (freeC desk, freeM desk) == (12, 24117248)
open Claims.Admit in
#guard (decide desk ⟨"young", some 3, 12582912, none⟩).line == "ok 3 12582912"
-- once 26 GiB are available it would fit with every claim ended: an ordinary head again, whose start the claim without an
-- estimate leaves unknown, so nothing passes it
open Claims.Admit in
#guard !held { desk with avail := 27262976 } ⟨"old", 989140, some 8, 31457280, none⟩ &&
  (decide { desk with avail := 27262976 } ⟨"young", some 3, 12582912, some 60⟩).line == "wait 12 27262976 1"
-- the rendering says why: unclaimed use, not the reservation
#guard ((parseLs "24 15.00 67108864 24117248 24 67108864 0 0 0\nc 4 2097152 t9999999 999400 ~1200 a x\nc 4 2097152 t9999999 999940 b y\nq old 989140 8 31457280 old\n").map
  (render "desktop" · 1000000 |>.getLast!)) == some "  waiting: old 8 cores 30.0G 3h, held by unclaimed memory use"

-- the wait line names what the head waits on
#guard ((parseLs "8 4.00 16777216 16777216 8 16777216 0 0 0\nc 4 2097152 t9999999 992200 hpl-ci ci\nq me 999000 all 0 timing\n").bind
  (·.waitLine 1000000 "me")) == some "whole machine waits on hpl-ci (4 cores, no estimate, 2h10m)"
#guard ((parseLs "8 4.00 16777216 16777216 8 16777216 0 0 0\nc 4 2097152 t9999999 999400 ~1200 b x\nq me 999000 all 0 timing\n").bind
  (·.waitLine 1000000 "me")) == some "whole machine waits on b (4 cores, ~10m left)"
#guard ((parseLs "8 4.00 16777216 16777216 8 16777216 0 0 0\nq me 999000 all 0 @999700 timing\n").bind
  (·.waitLine 1000000 "me")) == some "whole machine waits on 4.0 cores unclaimed use, yields in 5m"
#guard ((parseLs "8 4.00 16777216 16777216 8 16777216 0 0 0\nq me 999000 all 0 @999000 timing\n").bind
  (·.waitLine 1000000 "me")) == some "whole machine held: 4.0 cores unclaimed use; younger jobs go first"
#guard ((parseLs "8 4.00 16777216 16777216 8 16777216 0 0 0\nc 4 2097152 t9999999 992200 hpl-ci ci\nq h 990000 all 0 bench\nq me 999000 2 1048576 w\n").bind
  (·.waitLine 1000000 "me")) == some "2 cores 1.0G, 1 ahead: bench (whole machine, 2h46m) waits on hpl-ci (4 cores, no estimate, 2h10m)"
#guard ((parseLs "8 0.00 16777216 16777216 8 16777216 0 0 0\nq me 999000 2 1048576 w\n").bind (·.waitLine 1000000 "nobody")) == none
#guard waitKey "desktop: whole machine waits on hpl-ci (4 cores, no estimate, 2h10m)" ==
  waitKey "desktop: whole machine waits on hpl-ci (4 cores, no estimate, 2h11m)"
#guard spanHM 7800 == "2h10m" && spanHM 7200 == "2h" && spanHM 59 == "59s"
