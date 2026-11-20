import Std.Time
import Claims.Cli
import Claims.Acquire

/-! `claim`: compute claims for anything that wants a machine's cores, with or without swarm (`claim -h`). -/

open Claims

/-- The world: processes (stdin closed, stderr passed on), sleep, the standard streams, the clock. -/
def host : Host IO where
  run argv := do
    let some cmd := argv.head? | return none
    try
      let child ← IO.Process.spawn { cmd, args := argv.tail.toArray, stdin := .null, stdout := .piped, stderr := .inherit }
      let out ← child.stdout.readToEnd
      return some ((← child.wait).toNat, out)
    catch _ => return none
  sleep ms := IO.sleep ms.toUInt32
  err s := IO.eprintln s
  out s := IO.println s
  now := return (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val

/-- Splits the words after the subcommand into positionals and `--flag [value]`s (the flags in `valued` take one). -/
def split (valued : List String) : List String → List String × List (String × Option String) → Except String (List String × List (String × Option String))
  | [], (p, f) => .ok (p.reverse, f)
  | x :: rest, (p, f) =>
    if valued.contains x then
      match rest with
      | v :: rest => split valued rest (p, (x, some v) :: f)
      | [] => .error s!"{x} needs a value"
    else if x == "--json" then split valued rest (p, (x, none) :: f)
    else if x.startsWith "--" then .error s!"unknown option {x}"
    else split valued rest (x :: p, f)

/-- `claim run [--cores N|all] [--mem G] [--est S] [--who NAME] -- cmd…`. -/
def runCmd (args : List String) : IO UInt32 := do
  let (opts, cmd) := (args.takeWhile (· != "--"), (args.dropWhile (· != "--")).drop 1)
  let die (e : String) : IO UInt32 := do IO.eprintln s!"claim: {e}"; return 1
  if cmd.isEmpty then return ← die "usage: claim run [--cores N|all] [--mem G] [--est S] [--who NAME] -- <cmd…>"
  let (pos, fl) ← match split ["--cores", "--mem", "--est", "--who"] opts ([], []) with
    | .ok r => pure r
    | .error e => return ← die e
  unless pos.isEmpty do return ← die s!"unexpected {pos.head!} before --"
  let cores ← match fl.lookup "--cores" with
    | some (some "all") => pure "all"
    | some (some c) => match parseInt c with
      | some n => if n ≥ 1 then pure (toString n) else return ← die s!"--cores: not a count: {c}"
      | none => return ← die s!"--cores: not a count: {c}"
    | _ => pure "2"
  if cores == "all" && (fl.lookup "--mem").isSome then return ← die "--mem: not with --cores all (the available memory is claimed)"
  let est ← match fl.lookup "--est" with
    | some (some s) => match parseInt s with
      | some n => if n ≥ 1 then pure (some n) else return ← die s!"--est: not a number of seconds: {s}"
      | none => return ← die s!"--est: not a number of seconds: {s}"
    | _ => pure none
  let mem_kb ← match fl.lookup "--mem" with
    | some (some g) => match parseFloat g with
      | some x => if x > 0 then pure (Int.ofNat (x * 1048576).floor.toUInt64.toNat) else return ← die s!"--mem: not a size in G: {g}"
      | none => return ← die s!"--mem: not a size in G: {g}"
    | _ => pure (if cores == "all" then 0 else 2097152)
  let user := (← IO.getEnv "USER").getD "human"
  let who := match fl.lookup "--who" with | some (some w) => w | _ => user
  let pid := (← IO.Process.getPID).toNat
  let poll := ((← IO.getEnv "SWARM_COMPUTE_POLL_MS").bind (·.toNat?)).getD 5000
  let id := s!"{String.map (fun c => if c.isAlphanum || c == '.' || c == '_' || c == '-' then c else '_') who}-{pid}-{← host.now}"
  let line := " ".intercalate cmd
  let ask : Ask := {
    prog := "claim", capCmd := "claim", cands := [none], usable := [none], stateOf := fun _ => "connected",
    id := id, cores := cores, mem_kb := mem_kb, est := est, who := who, cmd := line, pid := pid, pollMs := poll }
  let some (_, got, gotMem) ← acquire host ask | return 255
  let cs := toString got
  let env := (jobEnv cs gotMem (← IO.getEnv "NIX_CONFIG")).map fun (k, v) => (k, some v)
  let rc ← try
      let child ← IO.Process.spawn { cmd := "sh", args := (#["-c", LOWPRIO_ARGV, "sh"] ++ cmd.toArray), env := env.toArray }
      pure (← child.wait)
    catch e => IO.eprintln s!"claim: {e}"; pure 127
  release host none id
  return rc

/-- `claim op <machine|here> <op> args…`: the script's op, its output as is. -/
def opCmd (mach : String) (args : List String) : IO UInt32 := do
  match ← callRaw host (if mach == "here" then none else some mach) args with
  | none => return 1
  | some (c, o) => IO.print o; return (if c == 0 then 0 else if c == 2 then 2 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["-h"] | ["--help"] | ["help"] => IO.println help; return 0
  | "op" :: mach :: op :: rest => opCmd mach (op :: rest)
  | "run" :: rest => runCmd rest
  | "queue" :: rest =>
    let (opts, cmd) := (rest.takeWhile (· != "--"), (rest.dropWhile (· != "--")).drop 1)
    match split ["--id", "--who", "--est", "--ttl", "--pid", "--owner"] opts ([], []) with
    | .error e => IO.eprintln s!"claim: {e}"; return 1
    | .ok (pos, fl) =>
      let g (k : String) := fl.lookup k |>.bind id
      match ← compute host "claim" ("queue" :: pos) false none none
          { id := g "--id", who := g "--who", est := g "--est", ttl := g "--ttl", pid := g "--pid", owner := g "--owner" } cmd with
      | .ok () => return 0
      | .error e => IO.eprintln s!"claim: {e}"; return 1
  | _ =>
    match split ["--cores", "--mem"] args ([], []) with
    | .error e => IO.eprintln s!"claim: {e}"; return 1
    | .ok (pos, fl) =>
      match ← compute host "claim" pos (fl.lookup "--json").isSome ((fl.lookup "--cores").bind id) ((fl.lookup "--mem").bind id) with
      | .ok () => return 0
      | .error e => IO.eprintln s!"claim: {e}"; return 1
