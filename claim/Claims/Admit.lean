/-! The admission model (sw-compute-backfill.md §6.1): what `try` decides, as pure definitions over the machine and ledger
as the script reads them under its lock. `ADMIT_AWK` (Claims/Ledger.lean) is this function in awk; Ledger's `limit_*` and
`held` are these definitions'. The names and shapes are the contract of the proofs and the differential test. -/

namespace Claims.Admit

/-- A live claim: its size, its start, its estimate (none: unknown, and every old line). -/
structure Claim where
  cores : Int
  mem : Int
  start : Int
  est : Option Int

/-- A live ticket; `cores` none: exclusive (`all`). -/
structure Ticket where
  id : String
  first : Int
  cores : Option Int
  mem : Int

/-- The machine and its ledger as `try` reads them under the lock, after `clean`. -/
structure Machine where
  ncpu : Int
  total : Int
  busy : Int                         -- hundredths of a core (the script's %.2f)
  avail : Int                        -- KiB
  cap : Option Int × Option Int      -- the cap file; none: `-`, or no file
  res : Int × Int                    -- the reserve file; (0, 0): none
  off : Bool
  now : Int
  claims : List Claim
  tickets : List Ticket              -- every live ticket, the requester's own included

/-- A request; `cores` none: exclusive (`all`), and then `mem` is ignored. -/
structure Req where
  id : String
  cores : Option Int
  mem : Int
  est : Option Int

inductive Answer
  | ok (cores mem : Int) | wait (fc fm ahead : Int) | never (capc capm : Int) | off
  deriving BEq, Repr

/-- The room sized jobs may take of `size`: the cap, less the reservation clamped to the machine. -/
def lim (cap size res : Int) : Int := min cap (size - min size (max 0 res))

def capC (m : Machine) : Int := m.cap.1.getD m.ncpu
def capM (m : Machine) : Int := m.cap.2.getD m.total
def limC (m : Machine) : Int := lim (capC m) m.ncpu m.res.1
def limM (m : Machine) : Int := lim (capM m) m.total m.res.2
def cc (m : Machine) : Int := (m.claims.map (·.cores)).sum
def cm (m : Machine) : Int := (m.claims.map (·.mem)).sum
def outside (m : Machine) : Int := max 0 ((m.busy - 100 * cc m + 50).tdiv 100 - max 1 (m.ncpu / 8))
def freeC (m : Machine) : Int := min (limC m - cc m) (m.ncpu - cc m - outside m)
def freeM (m : Machine) : Int := min (limM m - cm m) m.avail

/-- No cap below the whole machine. -/
def whole (m : Machine) : Bool := capC m ≥ m.ncpu && capM m ≥ m.total
/-- Nothing but claims keeps an exclusive job off: no reservation, no unclaimed use past the noise floor. -/
def quiet (m : Machine) : Bool := m.res == (0, 0) && outside m == 0

def held (m : Machine) (t : Ticket) : Bool := match t.cores with
  | some c => c > limC m || t.mem > limM m
  | none => !whole m || !quiet m

/-- (first, id) order; String's `<` is bytewise on these ids, as LC_ALL=C. The one place the queue order is set. -/
def before (a b : Int × String) : Bool := a.1 < b.1 || (a.1 == b.1 && decide (a.2 < b.2))
def first (m : Machine) (r : Req) : Int := ((m.tickets.find? (·.id == r.id)).map (·.first)).getD m.now
def aheadOf (m : Machine) (r : Req) : List Ticket :=
  m.tickets.filter fun t => t.id != r.id && !held m t && before (t.first, t.id) (first m r, r.id)
def head (m : Machine) (r : Req) : Option Ticket :=
  (aheadOf m r).foldl (fun a t => match a with
    | none => some t
    | some h => if before (t.first, t.id) (h.first, h.id) then some t else some h) none

def endOf (m : Machine) (c : Claim) : Option Int := c.est.map fun e => max m.now (c.start + e)
def events (m : Machine) : List Int := m.now :: m.claims.filterMap (endOf m)
def released (m : Machine) (τ : Int) : Int × Int :=
  let g := m.claims.filter fun c => (endOf m c).any (· ≤ τ)
  ((g.map (·.cores)).sum, (g.map (·.mem)).sum)
def fitsAt (m : Machine) (h : Ticket) (τ : Int) : Bool := match h.cores with
  | some c => c ≤ freeC m + (released m τ).1 && h.mem ≤ freeM m + (released m τ).2
  | none => m.claims.all fun c => (endOf m c).any (· ≤ τ)
/-- The head's estimated start. -/
def shadow (m : Machine) (h : Ticket) : Option Int := ((events m).filter (fitsAt m h)).min?

def tooBig (m : Machine) (r : Req) : Bool := match r.cores with
  | some c => c > capC m || r.mem > capM m
  | none => !whole m
def fitsNow (m : Machine) (r : Req) : Bool := match r.cores with
  | some c => c ≤ freeC m && r.mem ≤ freeM m
  | none => m.claims.isEmpty && quiet m
/-- What a grant claims. -/
def take (m : Machine) (r : Req) : Int × Int := match r.cores with
  | some c => (c, r.mem)
  | none => (m.ncpu, m.avail)

def decide (m : Machine) (r : Req) : Answer :=
  if m.off then .off else
  if tooBig m r then .never (capC m) (capM m) else
  let bf := match head m r, r.est with
    | some h, some e => (shadow m h).any (m.now + e ≤ ·)
    | _, _ => false
  if fitsNow m r && ((aheadOf m r).isEmpty || bf) then .ok (take m r).1 (take m r).2
  else .wait (max 0 (freeC m)) (max 0 (freeM m)) (aheadOf m r).length

/-- The line `try` prints. -/
def Answer.line : Answer → String
  | .ok c g => s!"ok {c} {g}" | .wait a b n => s!"wait {a} {b} {n}" | .never a b => s!"never {a} {b}" | .off => "off"

def grant (m : Machine) (r : Req) : Machine :=
  { m with claims := m.claims ++ [⟨(take m r).1, (take m r).2, m.now, r.est⟩],
           tickets := m.tickets.filter (·.id != r.id) }

/-- The ledger `try` leaves: a grant adds the claim and drops the ticket; a wait writes the ticket; never and off
drop it. -/
def after (m : Machine) (r : Req) : Machine :=
  let rest := m.tickets.filter (·.id != r.id)
  match decide m r with
  | .ok .. => grant m r
  | .wait .. => { m with tickets := rest ++ [⟨r.id, first m r, r.cores, if r.cores.isSome then r.mem else 0⟩] }
  | _ => { m with tickets := rest }

/-- `h` is the machine's head: a live ticket, not held, before every other live ticket that is not held. -/
def head0 (m : Machine) (h : Ticket) : Prop :=
  h ∈ m.tickets ∧ held m h = false ∧
  ∀ t ∈ m.tickets, t.id ≠ h.id → held m t = false → before (h.first, h.id) (t.first, t.id) = true

/-- What the script's own checks guarantee of its input: no negative size, a sized request of at least a core, a
machine with a core, available memory within the total, tickets named by distinct file names. -/
def WF (m : Machine) (r : Req) : Prop :=
  1 ≤ m.ncpu ∧ 0 ≤ m.total ∧ 0 ≤ m.busy ∧ 0 ≤ m.avail ∧ m.avail ≤ m.total ∧
  (∀ x ∈ m.cap.1, 0 ≤ x) ∧ (∀ x ∈ m.cap.2, 0 ≤ x) ∧ 0 ≤ m.res.1 ∧ 0 ≤ m.res.2 ∧
  (∀ c ∈ m.claims, 0 ≤ c.cores ∧ 0 ≤ c.mem ∧ ∀ e ∈ c.est, 0 ≤ e) ∧
  (∀ t ∈ m.tickets, (∀ x ∈ t.cores, 0 ≤ x) ∧ 0 ≤ t.mem) ∧ (m.tickets.map (·.id)).Nodup ∧
  (∀ x ∈ r.cores, 1 ≤ x) ∧ 0 ≤ r.mem ∧ (∀ e ∈ r.est, 0 ≤ e)

/-- The cap and reserve files, for the reserve theorems. -/
structure Files where
  cap : Option Int × Option Int
  res : Int × Int
  off : Bool
def setReserve (f : Files) (c g : Int) : Files := { f with res := (c, g) }
def setCap (f : Files) (c g : Option Int) : Files := { f with cap := (c, g) }

end Claims.Admit
