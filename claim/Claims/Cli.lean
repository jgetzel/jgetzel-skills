import Claims.Machines
import Claims.Ledger

/-! `claim`'s commands over a ledger: the show, `cap`, `off`, `on`; `swarm compute` is this with another `prog`. -/

namespace Claims
open Lean (Json)

/-- `claim`'s help. -/
def help : String := "claim: sized claims on a machine's cores and memory (ledger: $SWARM_COMPUTE_DIR, else
$XDG_STATE_HOME/swarm-compute, else ~/.local/state/swarm-compute)

  claim [--json]                                   every machine's claims, waiting claims, cap and load
  claim cap <machine|here> [--cores N|all] [--mem G|all]   the most that claims may take (all: no cap)
  claim off|on <machine|here>                      refuses every claim / allows them again
  claim run [--cores N|all] [--mem G] [--who NAME] -- <cmd…>
                                                   claims here (default 2 cores, 2G), waits, runs the command, drops
                                                   the claim; exits with the command's code, 255 when nothing can fit
  claim op <machine|here> <try|drop|ls|cap|off|on> <args…>
                                                   the ledger script's op, its output as is (exit 1: no answer, 2: bad args)

A machine is `here` or one of `hc machine ls`; claims on others go through `hc exec`."

/-- `<prog> …`: the show (`words` empty), `cap <machine>` with `cores` and `mem` as given, or `off|on <machine>`. An error is
the message to die with. -/
def compute {m : Type → Type} [Monad m] (h : Host m) (prog : String) (words : List String) (json : Bool)
    (cores mem : Option String) : m (Except String Unit) := do
  let ms ← hcMachines h
  let usage : String := s!"{prog} [--json] | cap <machine|here> [--cores N|all] [--mem G|all] | off|on <machine|here>"
  let target (n : String) : Except String (Option String) :=
    if n == "here" then .ok none
    else if (ms.lookup n).isNone then .error s!"no machine {n} in `hc machine ls`" else .ok (some n)
  match words with
  | [] =>
    let now ← h.now
    let all : List (String × Option String) := ("here", none) :: ms.map fun (n, _) => (n, some n)
    let mut out := []
    let mut js := []
    for (n, c) in all do
      let st := match c with | none => "connected" | some _ => ((ms.lookup n).bind (machineStr · "state")).getD "?"
      let l ← if st == "connected" then pure ((← call h c ["ls"]).bind parseLs) else pure none
      match l with
      | some l => out := out ++ render n l now; js := js ++ [(n, l.json)]
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
      | some x => match parseFloat x with
        | some g => pure (toString (Int.ofNat (g * 1048576).floor.toUInt64.toNat))
        | none => return .error s!"--mem: not a size in G: {x}"
    if (← call h c ["cap", cs, mm]).isNone then return .error s!"{n}: no answer"
    return .ok ()
  | [w, n] =>
    if w != "off" && w != "on" then return .error usage
    let c ← match target n with | .ok c => pure c | .error e => return .error e
    if (← call h c [w]).isNone then return .error s!"{n}: no answer"
    return .ok ()
  | _ => return .error usage

end Claims
