import Claims.Machines
import Claims.Ledger

/-! `claim`'s commands over a ledger: the show, `cap`, `off`, `on`; `swarm compute` is this with another `prog`. -/

namespace Claims
open Lean (Json)

/-- `claim`'s help. -/
def help : String := "claim: sized claims on a machine's cores and memory (ledger: $SWARM_COMPUTE_DIR, else
$XDG_STATE_HOME/swarm-compute, else ~/.local/state/swarm-compute)

  claim [--json] [here|<machine>]                  the claims, waiting claims, cap, reservation and load of every machine, or of one
  claim cap <machine|here> [--cores N|all] [--mem G|all]   the most that claims may take (all: no cap)
  claim reserve <machine|here> <cores> [--mem G]   the part of the machine kept for you, now: claims wait for the rest;
                                                   states the whole reservation, so `reserve here 0` lifts it
  claim off|on <machine|here>                      refuses every claim / allows them again
  claim queue add <machine|here> --id ID --who W [--est S] [--ttl S] [--pid P] [--owner O] -- <cmd…>
                                                   shows a job as queued under the machine (display only: it holds no cores and
                                                   no place in line); run again to renew. It lapses after --ttl seconds (default
                                                   900), or, with --pid (here only), when that process is gone
  claim queue rm <machine|here> ID                 removes it
  claim run [--cores N|all] [--mem G] [--est S] [--who NAME] -- <cmd…>
                                                   claims here (default 2 cores, 2G), waits, runs the command at the lowest
                                                   priority, drops the claim; exits with the command's code, 255 when nothing
                                                   can fit. A default over the cap is lowered to it; memory that unclaimed
                                                   use keeps short for 2 minutes lowers a default and refuses a --mem. --est S (seconds the job takes) lets it start before older waiters
                                                   that cannot start sooner. --cores all: the whole machine, alone (no --mem)
  claim op <machine|here> <try|drop|ls|qadd|qrm|cap|reserve|off|on> <args…>
                                                   the ledger script's op, its output as is (exit 1: no answer, 2: bad args)

A machine is `here` or one of `hc machine ls`; claims on others go through `hc exec`."

/-- The options of `queue add`; the command comes apart from them. -/
structure QOpts where
  id : Option String := none
  who : Option String := none
  est : Option String := none
  ttl : Option String := none
  pid : Option String := none
  owner : Option String := none

/-- `<prog> …`: the show (`words` empty, or one machine), `cap <machine>` with `cores` and `mem` as given, `reserve <machine>
<cores>` with `mem`, or `off|on <machine>`. An error is the message to die with. -/
def compute {m : Type → Type} [Monad m] (h : Host m) (prog : String) (words : List String) (json : Bool)
    (cores mem : Option String) (q : QOpts := {}) (cmd : List String := []) : m (Except String Unit) := do
  -- `here` alone needs no `hc`
  let ms ← if words.contains "here" then pure [] else hcMachines h
  let usage : String := s!"{prog} [--json] [here|<machine>] | cap <machine|here> [--cores N|all] [--mem G|all] | reserve <machine|here> <cores> [--mem G] | off|on <machine|here> | queue add <machine|here> --id ID --who W [--est S] [--ttl S] [--pid P] [--owner O] -- <cmd…> | queue rm <machine|here> ID"
  let target (n : String) : Except String (Option String) :=
    if n == "here" then .ok none
    else if (ms.lookup n).isNone then .error s!"no machine {n} in `hc machine ls`" else .ok (some n)
  let gib (what x : String) : Except String String := match parseFloat x with
    | some g => .ok (toString (Int.ofNat (g * 1048576).floor.toUInt64.toNat))
    | none => .error s!"{what}: not a size in G: {x}"
  match words with
  | [] | [_] =>
    let now ← h.now
    let all : List (String × Option String) := ("here", none) :: ms.map fun (n, _) => (n, some n)
    let shown := match words with
      | [n] => all.filter fun (x : String × Option String) => x.1 == n
      | _ => all
    if shown.isEmpty then return .error (match words with
      | n :: _ => if ["cap", "reserve", "off", "on"].contains n then usage else s!"no machine {n} in `hc machine ls`"
      | [] => usage)
    let mut out := []
    let mut js := []
    for (n, c) in shown do
      let st := match c with | none => "connected" | some _ => ((ms.lookup n).bind (machineStr · "state")).getD "?"
      let l ← if st == "connected" then pure ((← call h c ["ls"]).bind parseLs) else pure none
      match l with
      | some l => out := out ++ render n l now; js := js ++ [(n, l.json now)]
      | none =>
        let s := if st == "connected" then "unreachable" else st
        out := out ++ [s!"{n}: {s}"]; js := js ++ [(n, Json.mkObj [("state", .str s)])]
    if json then h.out (Json.mkObj js).compress else for l in out do h.out l
    return .ok ()
  | ["cap", n] =>
    let c ← match target n with | .ok c => pure c | .error e => return .error e
    let cs ← match cores with
      | none => pure "="
      | some "all" => pure "-"
      | some x => if (parseInt x).any (· ≥ 1) then pure x else return .error s!"--cores: not a count: {x}"
    let mm ← match mem with
      | none => pure "="
      | some "all" => pure "-"
      | some x => match gib "--mem" x with | .ok v => pure v | .error e => return .error e
    if (← call h c ["cap", cs, mm]).isNone then return .error s!"{n}: no answer"
    return .ok ()
  | ["reserve", n, c] =>
    let t ← match target n with | .ok t => pure t | .error e => return .error e
    let cs ← match parseInt c with
      | some x => if x ≥ 0 then pure (toString x) else return .error s!"reserve: not a count: {c}"
      | none => return .error s!"reserve: not a count: {c}"
    let mm ← match mem with
      | none => pure "0"
      | some x => match gib "--mem" x with | .ok v => pure v | .error e => return .error e
    if (← call h t ["reserve", cs, mm]).isNone then return .error s!"{n}: no answer"
    return .ok ()
  | ["queue", "add", n] =>
    let t ← match target n with | .ok t => pure t | .error e => return .error e
    let some id := q.id | return .error "queue add: --id is required"
    let some who := q.who | return .error "queue add: --who is required"
    if cmd.isEmpty then return .error "queue add: the command is required after --"
    let pos (what : String) (x : Option String) : Except String String := match x with
      | none => .ok "-"
      | some s => match parseInt s with
        | some v => if v ≥ 1 then .ok (toString v) else .error s!"{what}: not a positive number: {s}"
        | none => .error s!"{what}: not a positive number: {s}"
    let est ← match pos "--est" q.est with | .ok v => pure v | .error e => return .error e
    let ttl ← match pos "--ttl" (q.ttl.orElse fun _ => some "900") with | .ok v => pure v | .error e => return .error e
    let pid ← match pos "--pid" q.pid with | .ok v => pure v | .error e => return .error e
    if pid != "-" && t.isSome then return .error "queue add: --pid is for this machine only"
    if (← call h t ["qadd", id, q.owner.getD "-", who, est, ttl, pid, " ".intercalate cmd]).isNone then return .error s!"{n}: no answer"
    return .ok ()
  | ["queue", "rm", n, id] =>
    let t ← match target n with | .ok t => pure t | .error e => return .error e
    if (← call h t ["qrm", id]).isNone then return .error s!"{n}: no answer"
    return .ok ()
  | [w, n] =>
    if w != "off" && w != "on" then return .error usage
    let c ← match target n with | .ok c => pure c | .error e => return .error e
    if (← call h c [w]).isNone then return .error s!"{n}: no answer"
    return .ok ()
  | _ => return .error usage

end Claims
