import SwarmLean.World

/-! machine.lua's memory reading and machine line, which board and claim print. The rest of machine.lua (processes,
holders, the full note) is board task #100's; until then `note` asks the Lua CLI for it. -/

namespace SwarmLean.Machine

variable {m : Type → Type}

/-- A pressure reading: Linux PSI some avg10 (`memory`, `cpu`), or macOS `level`, `load` and `cores`. -/
structure Psi where
  memory : Option Float := none
  cpu : Option Float := none
  level : Option String := none
  load : Option Float := none
  cores : Option Int := none

/-- The /proc root (machine.PROC): $SWARM_PROC as set, else /proc. -/
def procRoot [Monad m] [Env m] : m String := return (← Env.var "SWARM_PROC").getD "/proc"

/-- The system (machine.OS): $SWARM_OS as set, else this build's. -/
def osName [Monad m] [Env m] : m String :=
  return (← Env.var "SWARM_OS").getD (if System.Platform.isOSX then "Darwin" else "Linux")

/-- Lua's `s:match(pat .. "(%d+)")`: the digits after the first `pat` in `s`. -/
def numAfter (s pat : String) (frac : Bool := false) : Option String :=
  match s.splitOn pat with
  | _ :: rest :: _ =>
    let ds := rest.toList.takeWhile fun c => c.isDigit || (frac && c == '.')
    if ds.isEmpty then none else some (String.ofList ds)
  | _ => none

/-- macOS readings to (avail KiB, total KiB, pressure) (machine.darwin_mem). -/
def darwinMem (memsize : String) (vmstat : Option String) (level loadavg ncpu : String) : Option (Int × Int × Psi) := do
  let total ← parseInt memsize
  let vm ← vmstat
  let pg := ((numAfter vm "page size of ").bind parseInt).getD 4096
  let count (k : String) : Int := match (vm.splitOn s!"Pages {k}:")[1]? with
    | some r => (parseInt (String.ofList ((r.toList.dropWhile isSpace).takeWhile Char.isDigit))).getD 0
    | none => 0
  let pages := count "free" + count "inactive" + count "speculative" + count "purgeable"
  let lvl := match parseInt level with
    | some 1 => some "normal" | some 2 => some "warn" | some 4 => some "critical" | _ => none
  let load := (String.ofList ((loadavg.toList.dropWhile fun c => !(c.isDigit || c == '.')).takeWhile fun c => c.isDigit || c == '.'))
  pure (fdiv (pages * pg) 1024, fdiv total 1024, { level := lvl, load := parseFloat load, cores := parseInt ncpu })

/-- Memory available and total in KiB and the pressure, none when unreadable (machine.mem). -/
def mem [Monad m] [Env m] [Fs m] [Proc m] : m (Option (Int × Int × Psi)) := do
  if (← osName) == "Darwin" then
    let sc (k : String) : m String := do
      return strip ((← Proc.output ["sysctl", "-n", k] none []).map (·.stdout) |>.getD "")
    let vm := (← Proc.output ["vm_stat"] none []).map (·.stdout)
    return darwinMem (← sc "hw.memsize") vm (← sc "kern.memorystatus_vm_pressure_level") (← sc "vm.loadavg") (← sc "hw.ncpu")
  let root ← procRoot
  let some s ← Fs.read (root ++ "/meminfo") | return none
  let field (k : String) : Option Int := (s.splitOn "\n").findSome? fun l =>
    match l.splitOn ":" with
    | key :: rest@(_ :: _) =>
      if key == k then parseInt (String.ofList ((":".intercalate rest).toList.dropWhile isSpace |>.takeWhile Char.isDigit)) else none
    | _ => none
  let psi (r : String) : m Float := do
    return (((← Fs.read s!"{root}/pressure/{r}").bind fun t => numAfter t "some avg10=" true).bind parseFloat).getD 0
  match field "MemAvailable", field "MemTotal" with
  | some a, some t => return some (a, t, { memory := some (← psi "memory"), cpu := some (← psi "cpu") })
  | _, _ => return none

/-- Memory or CPU pressure is high (machine.pressure_high). -/
def pressureHigh (avail total : Int) (psi : Psi) : Bool :=
  match psi.level with
  | some l => l != "normal"
  | none => psi.memory.getD 0 > 10 || Float.ofInt avail < 0.15 * Float.ofInt total

/-- The one machine line (machine.machine_line). -/
def line (avail total : Int) (psi : Psi) : String :=
  let memS := s!"machine: {fixed (Float.ofInt avail / 1048576) 1}/{fixed (Float.ofInt total / 1048576) 1}G mem available, "
  match psi.memory with
  | none =>
    memS ++ s!"pressure {psi.level.getD "unknown"}, load {(psi.load.map fmtG).getD "?"} on {(psi.cores.map toString).getD "?"} cores"
  | some mm => memS ++ s!"pressure10 mem {fmtG mm}% cpu {fmtG (psi.cpu.getD 0)}%"

end SwarmLean.Machine
