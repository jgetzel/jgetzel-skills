import SwarmLean.Cmd
import SwarmLean.Cmd.OpsHelp
import SwarmLean.Lib.Run
import SwarmLean.Lib.Cost
import SwarmLean.Lib.Compute
import Claims.Acquire
import Claims.Machines

/-! `swarm run [--on M] [--env X]... cmd…` (run.cmd_run): a build or test here, or on another hc machine against a copy
of this worktree, recorded as a job. -/

namespace SwarmLean.Cmd.Run
open Args _root_.SwarmLean.Run _root_.SwarmLean.Compute
open Lean (Json)
open Claims (gi span)

/-- The `run` parser; the command (everything from the first positional or `--` on) is split off first (`split`). -/
def spec : Spec :=
  .mk "run" helpRun [] [flag "--no-devshell", flag "--detach", opt "--on", opt "--cores", opt "--mem", { opt "--env" with maxCount := 1000000 }] [] [] none

/-- main.lua's split_run on the words after `run`: the options, and the command (`--` dropped). -/
def split (args : List String) : List String × List String :=
  let rec go (i : Nat) (fuel : Nat) : Nat :=
    match fuel, args[i]? with
    | f + 1, some x =>
      if x == "--on" || x == "--env" || x == "--cores" || x == "--mem" then go (i + 2) f
      else if x.startsWith "--on=" || x.startsWith "--env=" || x.startsWith "--cores=" || x.startsWith "--mem=" || x == "--no-devshell" || x == "--detach" || x == "-h" || x == "--help" then go (i + 1) f
      else i
    | _, _ => i
  let i := go 0 (args.length + 1)
  let rest := args.drop i
  (args.take i, if rest.head? == some "--" then rest.tail else rest)

/-- run.sanitize: every character but `[%w_.-]` as `_`. -/
def sanitize (s : String) : String := s.map fun c => if c.isAlphanum || c == '_' || c == '.' || c == '-' then c else '_'

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]

/-- The job's line inside the project's nix dev shell (sw-run-devshell): $1 the line, $2 the tree, $3 the profile directory. A
profile of the shell is built once per flake.nix+flake.lock (under the run's claim, serialised by flock), each job then
`nix develop <profile> -c`. Left as it is: IN_NIX_SHELL set, no nix, no flake.nix, no devShells.default for this system
(remembered as `.none`). A build that fails ends the job (exit 1) with the nix error's last lines. -/
def devshellScript : String := String.intercalate "\n" [
  "plain() { exec sh -c \"$1\"; }",
  "[ -n \"$IN_NIX_SHELL\" ] && plain \"$@\"",
  "command -v nix >/dev/null 2>&1 || plain \"$@\"",
  "[ -f \"$2/flake.nix\" ] || plain \"$@\"",
  "d=$3; h=$(cat \"$2/flake.nix\" \"$2/flake.lock\" 2>/dev/null | sha256sum | cut -c1-16); p=$d/$h",
  "if [ ! -e \"$p\" ] && [ ! -e \"$p.none\" ]; then",
  "  mkdir -p \"$d\" || plain \"$@\"",
  "  e=$d/err.$$",
  "  (",
  "    command -v flock >/dev/null 2>&1 && flock 9",
  "    [ -e \"$p\" ] || [ -e \"$p.none\" ] && exit 0",
  "    sys=$(nix eval --impure --raw --expr builtins.currentSystem 2>\"$e\") || exit 1",
  "    if ! nix eval \"$2#devShells.$sys.default.name\" >/dev/null 2>\"$e\"; then",
  "      grep -q 'does not provide attribute' \"$e\" && { : > \"$p.none\"; exit 0; }",
  "      exit 1",
  "    fi",
  "    nix develop \"$2\" --profile \"$p\" -c true >/dev/null 2>\"$e\" || exit 1",
  "    find \"$d\" -maxdepth 1 -type l -mtime +0 ! -name \"$h*\" -exec rm -f {} + 2>/dev/null",
  "    find \"$d\" -maxdepth 1 -name '*.none' -mtime +0 ! -name \"$h*\" -exec rm -f {} + 2>/dev/null",
  "    exit 0",
  "  ) 9>\"$d/lock\"",
  "  if [ $? -ne 0 ]; then",
  "    tail -n 8 \"$e\" >&2; rm -f \"$e\"",
  "    echo 'swarm: the dev shell did not build; --no-devshell runs without it' >&2",
  "    exit 1",
  "  fi",
  "  rm -f \"$e\"",
  "fi",
  "[ -e \"$p\" ] || plain \"$@\"",
  "touch -h \"$p\" 2>/dev/null",
  "exec nix develop \"$p\" -c sh -c \"$1\""]

/-- Whether `line` already starts with `nix develop`, `nix shell` or `nix run`. -/
def startsNix (line : String) : Bool :=
  match (line.splitOn " ").filter (· ≠ "") with
  | "nix" :: w :: _ => w == "develop" || w == "shell" || w == "run"
  | _ => false

/-- `line` run by the dev-shell script on tree `src` with profiles under `pdir` (both shell words, already quoted). -/
def devshellWrap (line src pdir : String) : String :=
  "sh -c " ++ shquote devshellScript ++ " swarm-devshell " ++ shquote line ++ " " ++ src ++ " " ++ pdir

/-- `.claude/swarm.json`'s `run` object, or {}. -/
def readCfg (top : String) : m Json := do
  match ((← Fs.read (joinPath top ".claude/swarm.json")).bind Json.decode).bind (Json.field · "run") with
  | some c@(.obj _) => return c
  | _ => return Json.mkObj []

/-- git's stdout, stripped, when it exits 0 (proc.git). -/
def git (args : List String) (cwd : Option String := none) : m (Option String) := return (← Git.git args cwd).map strip

/-- Tree of the working state (tracked and untracked, not ignored), written into a copy of the index; reads wt only. -/
def treeOf (wt : String) : m (Option String) := do
  let some idx ← git ["-C", wt, "rev-parse", "--path-format=absolute", "--git-path", "index"] | return none
  if (← git ["-C", wt, "rev-parse", "HEAD"]).isNone then return none
  let tmp := strip (← Sys.exec ["mktemp"] {}).stdout
  discard <| Sys.exec ["cp", "-p", idx, tmp] {}  -- keeps the index mtime, or git trusts stale stat data (racy git)
  let env := [("GIT_INDEX_FILE", some tmp), ("GIT_OPTIONAL_LOCKS", some "0")]
  discard <| Sys.exec ["git", "-C", wt, "add", "-A"] { env }
  let out := strip (← Sys.exec ["git", "-C", wt, "write-tree"] { env }).stdout
  discard <| Sys.remove tmp
  return if out == "" then none else some out

/-- `{file: blob hash}` for the plain files of `files` (one git call). -/
def hashes (top : String) (files : List String) : m (List (String × String)) := do
  let mut names := []
  for f in files do
    if (← Sys.kind (joinPath top f) false) == .file && !hasSub f "\n" then names := names ++ [f]
  let r ← Sys.exec ["git", "-C", top, "hash-object", "--stdin-paths"] { input := some ("\n".intercalate names ++ "\n") }
  return names.zip (splitlines r.stdout)

/-- The script a measured job's scope runs: `$1` is the job's directory, holding `cmd` (the command line) and receiving
`measure` (`<cpu s> <peak KiB>`, from the scope's own cgroup, read before the scope ends). -/
def measureScript : String := String.intercalate "\n" [
  "d=$1; sh -c \"$(cat \"$d/cmd\")\"; rc=$?",
  "cg=/sys/fs/cgroup$(sed -n 's/^0:://p' /proc/self/cgroup 2>/dev/null)",
  "if [ -r \"$cg/cpu.stat\" ] && [ -r \"$cg/memory.peak\" ]; then",
  "  u=$(sed -n 's/^usage_usec //p' \"$cg/cpu.stat\"); p=$(cat \"$cg/memory.peak\")",
  "  case $u$p in ''|*[!0-9]*) ;; *) echo \"$(( (u + 999999) / 1000000 )) $(( (p + 1023) / 1024 ))\" > \"$d/measure\";; esac",
  "fi",
  "exit $rc"]

/-- The same where there is no user scope: the children's rusage (CPU seconds, rounded up; peak KiB) of `$1/cmd`. -/
def rusageScript : String :=
  "import resource,subprocess,sys\nd=sys.argv[1]\nrc=subprocess.call(['sh','-c',open(d+'/cmd').read()])\nr=resource.getrusage(resource.RUSAGE_CHILDREN)\n" ++
  "k=r.ru_maxrss//(1024 if sys.platform=='darwin' else 1)\nopen(d+'/measure','w').write('%d %d\\n'%(-(-int((r.ru_utime+r.ru_stime)*1000000)//1000000),k))\nsys.exit(rc if rc>=0 else 128-rc)"

/-- `sh -c (measured unit memKb dir)` runs `dir/cmd` and writes `<cpu s> <peak KiB>` of it and its children to `dir/measure`: in its
own systemd user scope (`MemoryMax` when `memKb` is given), reading the scope's cgroup (`cpu.stat`, `memory.peak`); elsewhere
by rusage (python3), else not at all. The arguments carry no `$` (systemd-run reads `$$` in them). -/
def measured (unit : String) (memKb : Option Int) (dir : String) : String :=
  let cap := memKb.elim "" fun kb => s!"-p MemoryMax={kb}K -p MemorySwapMax=0 "
  let warn := if memKb.isSome then "echo 'swarm: memory not capped here (no systemd user scope); --mem is a reservation only' >&2; " else ""
  s!"if systemd-run --user --scope --quiet true 2>/dev/null; then exec systemd-run --user --scope --quiet --collect --unit={unit} {cap}-- sh {shquote (dir ++ "/measure.sh")} {shquote dir}; " ++
  s!"else {warn}if command -v python3 >/dev/null 2>&1; then exec python3 -c {shquote rusageScript} {shquote dir}; else exec sh -c \"$(cat {shquote (dir ++ "/cmd")})\"; fi; fi"

/-- A finished job as a history row, filed under the user's command (`key`): its wall time and its CPU seconds and peak memory,
a local job's from `measured` (`mfile`; 0 when it could not be read), a remote job's the last RSS and %CPU watchd read on that
machine (the %CPU over the wall time). -/
def recordJob (who : String) (on : Option String) (jid cmd key repo : String) (s : Int) (mfile : String) : m Unit := do
  let (mach, cpu, rss) ← match on with
    | none =>
      let nums := (strip ((← Fs.read mfile).getD "")).splitOn " " |>.filterMap parseInt
      pure (← Sys.hostname, nums.getD 0 0, nums.getD 1 0)
    | some mach =>
      let db ← Store.txn [.«meta»] fun db => (db, db)
      let ms := (db.getMeta "machines").bind (·.v) |>.bind Json.decode
      let last := ((ms.bind (Json.field · mach)).bind (Json.field · "jobs")).bind (Json.field · jid) |>.getD (Json.mkObj [])
      pure (mach, ((Json.fint last "cpu").getD 0 * s + 50) / 100, (Json.fint last "rss_kb").getD 0)
  discard <| Cost.record { ts := ← Clock.now, machine := mach, repo, agent := who, source := "run", cmd, key := some key, wall_s := s, cpu_s := cpu, peak_kb := rss }

/-- The job's exit as the record and the message say it: a code, or lost. -/
inductive Code | n (c : Int) | lost

/-- What a job's end (`finishJob`) and its run on another machine (`runRemote`) take of `run`'s state. -/
structure JobCtx where
  who : String
  jid : String
  on : Option String
  nested : Bool
  claimId : String
  waitS : Int
  t0 : Float
  full : String
  line : String
  repo : String
  jobs : String
  logf : String
  memFlag : Option Int
  detached : Bool
  task : Option Int

/-- An event of job `jid`, logged as `who`'s. -/
def jobEv (who jid kind : String) (data : Json) : m Unit := do
  let now ← Clock.now
  Store.txn [] fun db => (db.log now (some who) kind (some jid) (some (Json.encode data)), ())

/-- The job's line through the dev shell, under the config's `prefix` (its `{cores}` filled in). -/
def wrapFull (cfg : Json) (cs line src pdir : String) : String :=
  let w := devshellWrap line src pdir
  match Json.fstr cfg "prefix" with | some p => p.replace "{cores}" cs ++ " " ++ w | none => w

/-- `fl` at the lowest priority, under its `--mem` cap in scope `unit` when one was given. -/
def mkJob (unit : String) (memFlag : Option Int) (fl : String) : String :=
  (memFlag.map fun kb => Claims.memCap unit kb).getD id (Claims.lowPrio fl)

/-- `run --detach` once the claim is held and the job id allocated: the rest of the run goes on in a background process
(the same `swarm run`, `SWARM_RUN_RESUME` carrying the claim), and this returns once it is up (board #205). Its own
function, as `finishJob` and `runRemote`, so Crash.lean's walk of `run` applies its lemma instead of walking it inline. -/
def detachStart (a : Parsed) (argv : List String) (claimId jid jobs unit cwd : String) (chosen : Option String)
    (gotCores gotMem waitS : Int) (estF : Option Int) : m UInt32 := do
  let exe := (← Sys.readlink "/proc/self/exe").getD "swarm"
  let cargs := ["run"] ++ (if a.flag "no_devshell" then ["--no-devshell"] else []) ++ ((a.str "on").elim [] (["--on", ·])) ++
    ((a.str "cores").elim [] (["--cores", ·])) ++ ((a.str "mem").elim [] (["--mem", ·])) ++ ((a.strs "env").flatMap (["--env", ·])) ++ ["--"] ++ argv
  let rj := Json.encode (obj [("claim", some (.str claimId)), ("machine", chosen.map .str), ("cores", some (Json.int gotCores)),
    ("mem", some (Json.int gotMem)), ("wait", some (Json.int waitS)), ("jid", some (.str jid))])
  let out := jobs ++ "/out"
  let ready := jobs ++ "/ready"
  discard <| Sys.remove ready
  let names := (← Sys.environ).map (·.1) |>.filter fun k => k != "SWARM_RUN_RESUME" && !k.isEmpty && !(k.get 0).isDigit &&
    k.all fun c => c.isAlphanum || c == '_'
  let sd := ["systemd-run", "--user", "--collect", "--quiet", "--unit=" ++ unit, "--working-directory=" ++ cwd,
    "-p", "StandardOutput=file:" ++ out, "-p", "StandardError=file:" ++ out, "--setenv=SWARM_RUN_RESUME"] ++ names.map ("--setenv=" ++ ·) ++ [exe] ++ cargs
  let script := "if [ -z \"${SWARM_DETACH_NO_SYSTEMD:-}\" ] && " ++ shjoin sd ++ " 2>/dev/null; then :; else cd " ++ shquote cwd ++
    " && setsid nohup " ++ shjoin (exe :: cargs) ++ " >" ++ shquote out ++ " 2>&1 </dev/null & fi"
  discard <| Sys.exec ["sh", "-c", script] { env := [("SWARM_RUN_RESUME", some rj)], stdoutFile := some "/dev/null", merge := true }
  let mut up := false
  for _ in [0:300] do
    if (← Sys.kind ready false) == .file then up := true; break
    Sys.sleep 100
  if !up then
    Env.err s!"swarm: the background run of j{jid} did not start in 30s; see {out}"
    throw (Exit.mk 255)
  Env.out s!"job j{jid} started on {chosen.getD "this machine"} ({d gotCores} cores, {estF.elim "no estimate" fun e => "~" ++ span e}); you get its end line as a message. `swarm stay --until job:{jid}` waits for it."
  return 0

/-- A job's end: `run`'s own claim released, the job-end event and the job's row, the log's tail and the end line out,
and for a detached run the end line posted (`postEnd`). -/
def finishJob (ctx : JobCtx) (code : Code) (tree : Option String) (sync back : Option Float) (kept : List String)
    (hc : Option String) : m UInt32 := do
  let who := ctx.who
  let jid := ctx.jid
  let on := ctx.on
  let nested := ctx.nested
  let claimId := ctx.claimId
  let waitS := ctx.waitS
  let t0 := ctx.t0
  let full := ctx.full
  let line := ctx.line
  let repo := ctx.repo
  let jobs := ctx.jobs
  let logf := ctx.logf
  let memFlag := ctx.memFlag
  let detached := ctx.detached
  let task := ctx.task
  if on.isNone && !nested then Claims.release host on claimId
  let s := (← Sys.nowF) - t0 |>.floor |>.toInt64.toInt
  jobEv who jid "job-end" (obj [("machine", on.map .str), ("exit", some (match code with | .n c => Json.int c | .lost => .str "lost")),
    ("s", some (Json.int s)), ("wait_s", some (Json.int waitS)), ("sync_s", sync.map Lean.toJson), ("back_s", back.map Lean.toJson), ("tree", tree.map .str)])
  -- every job is a row, filed under the user's command (sw-compute-backfill.md §2.1)
  -- the repo name `history` reads (unsanitised, from the common dir), not the sanitised run dir's
  try recordJob who on jid full (Cost.key line) ((← Cost.repoName).getD repo) s (jobs ++ "/measure") catch _ => pure ()
  let lines := splitlines ((← Fs.read logf).getD "")
  let tail := lines.drop (lines.length - JOB_TAIL)
  let lost := match code with | .lost => true | _ => false
  let sec := s % 60
  let endLine := (s!"job j{jid} {match code with | .n c => "exit " ++ d c | .lost => "lost"} on {on.getD "this machine"}, {fdiv s 60}m{if sec < 10 then "0" else ""}{sec}s" ++
    (if waitS > 0 then s!", waited {waitS / 60}m{if waitS % 60 < 10 then "0" else ""}{waitS % 60}s" else "") ++
    (match sync, back with | some x, some y => s!" (sync {fixed x 1}s, back {fixed y 1}s)" | _, _ => "") ++
    (match tree with | some t => ", tree " ++ (t.take 7).toString | none => "") ++ "; log: " ++ logf ++
    (if kept.isEmpty then "" else s!"\nkept your local edits; the job's versions of {", ".intercalate kept} are in {jobs}/kept/") ++
    (match lost, hc with | true, some h => s!"\nthe terminal {h} may still be running: `hc wait {h}` later" | _, _ => "") ++
    (match memFlag, code with
      | some kb, .n 137 => s!"\nkilled at its --mem cap ({gi kb} GiB)? Try a bigger --mem."
      | _, _ => ""))
  if !tail.isEmpty then Env.out ("\n".intercalate tail)
  Env.out endLine
  if detached then
    let ok := match code with | .n 0 => true | _ => false
    postEnd who task ((if ok || tail.isEmpty then "" else "\n".intercalate tail ++ "\n") ++ endLine)
  return match code with | .lost => 255 | .n c => (c.toNat % 256).toUInt32

/-- `run` on machine `mach`: the worktree synced to a copy there, the job in an hc terminal, its changed files and the
config's `bring_back` brought back, then `finishJob`. -/
def runRemote (ctx : JobCtx) (mach top cs unit dir rel wtname : String) (cfg : Json) (jenv : List (String × String))
    (devOn : Bool) (rec0 : List (String × Option Json)) : m UInt32 := do
  let who := ctx.who
  let jid := ctx.jid
  let on := ctx.on
  let claimId := ctx.claimId
  let t0 := ctx.t0
  let full := ctx.full
  let line := ctx.line
  let repo := ctx.repo
  let jobs := ctx.jobs
  let memFlag := ctx.memFlag
  let task := ctx.task
  let sub (x : String) := x.replace "{cores}" cs
  let ms ← Claims.hcMachines host
  let mc := ms.lookup mach
  if mc.bind (Json.fstr · "state") != some "connected" then
    Env.err s!"swarm: machine {mach} is {match mc with | some x => (Json.fstr x "state").getD "nil" | none => "not in `hc machine ls`"}; the job never ran. Pick another (see the machine note)."
    Claims.release host on claimId
    throw (Exit.mk 255)
  let sshv ← sshCmd
  let ssh := shjoin sshv
  let tgt := ((mc.bind (Json.fstr · "target")).getD "nil")
  let now ← Clock.now
  let live ← Store.txn [.event] fun db => (db, liveJobs db now)
  let mut busy := 0
  for j in live do
    if j.s "machine" == some mach && j.s "wt" == some top then
      if let some p := (Json.field j.data "pid").bind Json.int? then
        if ← Sys.pidAlive p then busy := busy + 1
  let src := dir ++ "/src" ++ (if busy > 0 then "." ++ toString (busy + 1) else "")
  let lsOut := ((← Git.git ["-C", top, "ls-files", "-z", "-c", "-o", "--exclude-standard"] none).getD "")
  let files := (lsOut.splitOn "\x00").filter (· ≠ "")
  let before ← hashes top files
  let mk ← Sys.exec (sshv ++ [tgt, "mkdir -p " ++ shquote src]) {}
  if mk.code != 0 then
    let last := splitlines (strip mk.stderr)
    Env.err s!"swarm: sync to {mach} failed (mkdir exit {mk.code}: {last.getLastD "?"}); the job never ran."
    Claims.release host on claimId
    throw (Exit.mk 255)
  let rs ← Sys.exec ["rsync", "-rlpD", "--checksum", "--delete", "--exclude=.git", "--filter=:- .gitignore",
    "-e", ssh, top ++ "/", tgt ++ ":" ++ src ++ "/"] {}
  let sync := (← Sys.nowF) - t0
  if rs.code != 0 then
    let last := splitlines (strip rs.stderr)
    Env.err s!"swarm: sync to {mach} failed (rsync exit {rs.code}: {last.getLastD "?"}); the job never ran."
    Claims.release host on claimId
    throw (Exit.mk 255)
  let exports := ((jenv.map fun (k, v) => k ++ "=" ++ shquote v).mergeSort (· ≤ ·))
  let setO : List (String × String) := match Json.field cfg "set" with
    | some (.obj kv) => kv.toList.map fun (k, v) => (k, sub ((Json.str? v).getD ""))
    | _ => []
  let exports := exports ++ ((setO.mergeSort fun x y => x.1 ≤ y.1).map fun (k, v) =>
    k ++ "=\"" ++ v.replace "{dir}" ("$HOME/" ++ dir) ++ "\"")
  let jobCmd := mkJob unit memFlag (if devOn then wrapFull cfg cs line ("\"$HOME/" ++ src ++ "\"") ("\"$HOME/" ++ dir ++ "/devshell\"") else full)
  let metaD := s!"\"$HOME/{dir}/jobs/{jid}\""
  let script := "; ".intercalate [
    s!"mkdir -p {metaD} && cd \"$HOME/{src}\" || exit 255",
    -- the claim's holder becomes this shell; the claim goes when it exits
    s!"f=\"$\{SWARM_COMPUTE_DIR:-$\{XDG_STATE_HOME:-$HOME/.local/state}/swarm-compute}/claims/{claimId}\"; trap 'rm -f \"$f\"' EXIT",
    s!"if [ -f \"$f\" ]; then sed \"s/^\\([^ ]* [^ ]* \\)[^ ]* /\\1p$$ /\" \"$f\" > \"$\{f%/*}/.h$$\" && mv \"$\{f%/*}/.h$$\" \"$f\"; fi",
    "[ -d .git ] || git init -q",
    s!"git add -A && git write-tree > {metaD}/tree",
    s!"\{ (cd {shquote rel} && {if exports.isEmpty then "" else "export " ++ " ".intercalate exports ++ " && "}{jobCmd}) < /dev/null; echo $? > {metaD}/rc; } 2>&1 | tee {metaD}/log",
    s!"git ls-files -z -m -o --exclude-standard > {metaD}/files",
    s!"exit \"$(cat {metaD}/rc 2>/dev/null || echo 255)\""]
  let name := String.ofList (((who ++ "-j" ++ jid).toLower.toList.map fun c => if c.isLower || c.isDigit || c == '_' || c == '-' then c else '-').take 32)
  let hcrun := ["hc", "run", "--on", mach, "--bg", "--json", "--no-notify", "--name", name, "--label", "swarm-agent=" ++ who,
    "--label", "swarm-job=" ++ jid, "--label", s!"swarm-wt={repo}/{wtname}"] ++
    (match task with | some t => ["--label", "swarm-task=" ++ d t] | none => []) ++ ["sh", "-c", script]
  let o := (← Proc.output hcrun none []).bind fun r => if r.code == 0 then Json.decode r.stdout else none
  let some addr := o.bind (Json.fstr · "address") | do
    Env.err s!"swarm: `hc run --on {mach}` failed; the job never ran."
    Claims.release host on claimId
    throw (Exit.mk 255)
  jobEv who jid "job-start" (obj (rec0 ++ [("dir", some (.str dir)), ("hc", some (.str addr))]))
  let mut w : Option Json := none
  repeat
    let x := (← Proc.output ["hc", "wait", addr, "--json", "--timeout", "600"] none []).bind fun r =>
      if r.code == 0 then Json.decode r.stdout else none
    match x with
    | some x@(.obj _) => if (Json.field x "ended").any (· != .bool false) then w := some x; break
    | _ => break
  let some wj := w | finishJob ctx .lost none (some sync) none [] (some addr)
  let code : Code := match Json.fint wj "exit_code" with
    | some c => .n c
    | none => match Json.fint wj "signal" with | some sg => .n (128 + sg) | none => .lost
  let tb ← Sys.nowF
  let rsync (args : List String) : m Unit := do discard <| Sys.exec (["rsync", "-a", "-e", ssh] ++ args) {}
  rsync [s!"{tgt}:{dir}/jobs/{jid}/", jobs ++ "/"]
  let back := (((← Fs.read (jobs ++ "/files")).getD "").splitOn "\x00").filter (· ≠ "")
  let mut kept := []
  if !back.isEmpty then
    let stage := jobs ++ "/kept"
    rsync ["--from0", "--files-from=" ++ jobs ++ "/files", s!"{tgt}:{src}/", stage ++ "/"]
    let nowH ← hashes top back
    for f in back do
      if (← Sys.kind (stage ++ "/" ++ f) false) != .none then
        let here := (← Sys.kind (joinPath top f) false) != .none
        if nowH.lookup f == before.lookup f && here == (before.lookup f).isSome then  -- untouched here since the sync
          discard <| Sys.mkdirp (dirname (joinPath top f))
          discard <| Sys.exec ["mv", "-f", stage ++ "/" ++ f, joinPath top f] {}
        else kept := kept ++ [f]
  let home := (← Env.var "HOME").getD ""
  for b in Json.items ((Json.field cfg "bring_back").getD .null) do  -- ~/x: the same path on both machines; else under the tree
    let some b := Json.str? b | continue
    if b.startsWith "~/" then rsync [tgt ++ ":" ++ (b.drop 2).toString, home ++ (b.drop 1).toString]
    else rsync [s!"{tgt}:{src}/{b}", joinPath top b]
  let tree := (← Fs.read (jobs ++ "/tree")).map strip
  discard <| Proc.output ["hc", "rm", addr] none []
  finishJob ctx code tree (some sync) (some ((← Sys.nowF) - tb)) kept (some addr)

/-- `swarm run …`. -/
def run (a : Parsed) : m UInt32 := do
  let argv := a.strs "argv"
  if argv.isEmpty then die "usage: swarm run [--detach] [--on <machine>] [--cores N|all] [--mem <G>] [--env NAME[=VAL]]... -- <cmd…>"
  let some top0 ← git ["rev-parse", "--show-toplevel"] | die "not in a git repo"
  if top0 == "" then die "not in a git repo"
  let top := (← Sys.realpath top0).getD top0
  let common := (← git ["rev-parse", "--path-format=absolute", "--git-common-dir"]).getD ""
  let repo := sanitize (if common.endsWith "/.git" then basename (dirname common) else basename top)
  let wtname := sanitize (basename top)
  let cwd ← Env.cwd
  let cwd := (← Sys.realpath cwd).getD cwd
  let rel := if cwd == top then "." else if cwd.startsWith (top ++ "/") then (cwd.drop (top.length + 1)).toString else "."
  let cfg ← readCfg top
  let who := (← env "SWARM_NAME").getD "human"
  let line := if argv.length == 1 then argv.head! else shjoin argv
  let jenv0 ← jobEnv cfg top (a.strs "env")
  -- the claim (sw-compute.md §3): sized from the flags, else the history, else the default
  let coresArg ← match a.str "cores" with
    | none => pure none
    | some "all" => pure (some "all")
    | some c => match parseInt c with
      | some n => if n ≥ 1 then pure (some (d n)) else die s!"--cores: not a count: {c}"
      | none => die s!"--cores: not a count: {c}"
  let memFlag ← match a.str "mem" with
    | none => pure none
    | some g => match parseFloat g with
      | some x => if x > 0 then pure (some (Int.ofNat (x * 1048576).floor.toUInt64.toNat)) else die s!"--mem: not a size in G: {g}"
      | none => die s!"--mem: not a size in G: {g}"
  if coresArg == some "all" && memFlag.isSome then die "--mem: not with --cores all (the whole machine's available memory is claimed)"
  let parent ← env "SWARM_JOB_ID"
  let hn ← Sys.hostname
  -- inside a local job's claim (SWARM_JOB_ID, same machine, no --on): no claim of its own, the parent's cores
  let nested := parent.isSome && (← env "SWARM_JOB_MACHINE") == some hn && (a.str "on").isNone
  let resume : Option Json := (← env "SWARM_RUN_RESUME").bind Json.decode
  let detached := resume.isSome
  let (chosen, gotCores, gotMem, claimId, waitS, estF) : Option String × Int × Int × String × Int × Option Int ← if let some rj := resume then
    pure ((Json.fstr rj "machine"), (Json.fint rj "cores").getD DEFAULT_CORES, (Json.fint rj "mem").getD DEFAULT_MEM_KB,
      (Json.fstr rj "claim").getD "", (Json.fint rj "wait").getD 0, none)
  else if nested then do
    let c := ((← env "SWARM_CORES").bind parseInt).getD DEFAULT_CORES
    let mk := ((← env "SWARM_MEM_KB").bind parseInt).getD DEFAULT_MEM_KB
    Env.err s!"swarm: inside job j{parent.getD ""}'s claim ({d c} cores); not claiming"
    pure (none, c, mk, "", 0, none)
  else do
    let rows ← history line
    let hist := Compute.size rows
    let est := Compute.estimate rows
    let (wantC, wantM) := (coresArg.getD (match hist with | some h => d h.1 | none => d DEFAULT_CORES),
      if coresArg == some "all" then 0 else memFlag.getD (match hist with | some h => h.2 | none => DEFAULT_MEM_KB))
    let from_ := match hist with | some _ => "from the history" | none => "no history: the default"
    let what : String := if wantC == "all" then "the whole machine" else s!"{wantC} cores, {gi wantM}G"
    let basis : String := if coresArg.isSome && (memFlag.isSome || wantC == "all") then "as asked" else from_
    Env.err s!"swarm: claiming {what}{est.elim "" fun e => s!", ~{span e}"} ({basis})"
    let machines := ((Json.field cfg "machines").map Json.items |>.getD []).filterMap Json.str?
    let cands : List (Option String) := match a.str "on" with | some x => [some x] | none => none :: machines.map some
    let ms0 ← Claims.hcMachines host
    let stateOf (c : Option String) : String := match c with
      | none => "connected"
      | some n => (ms0.lookup n).bind (Json.fstr · "state") |>.getD "not in `hc machine ls`"
    let usable := cands.filter fun c => stateOf c == "connected"
    if let some mach := a.str "on" then
      if !usable.contains (some mach) then
        Env.err s!"swarm: machine {mach} is {stateOf (some mach)}; the job never ran. Pick another (see the machine note)."
        throw (Exit.mk 255)
    let claimId := s!"{sanitize who}-{← Sys.getpid}-{← Clock.now}"
    let tw ← Sys.nowF
    let poll := ((← env "SWARM_COMPUTE_POLL_MS").bind parseInt).getD 5000
    let ask : Claims.Ask := {
      prog := "swarm", capCmd := "swarm compute", cands, usable, stateOf, id := claimId, cores := wantC,
      mem_kb := wantM, est, who, cmd := line, pid := ← Sys.getpid, pollMs := poll.toNat }
    let some (chosen, gotCores, gotMem) ← Claims.acquire host ask | throw (Exit.mk 255)
    let waitS : Int := Int.ofNat ((← Sys.nowF) - tw).floor.toUInt64.toNat
    pure (chosen, gotCores, gotMem, claimId, waitS, est)
  let cs := d gotCores
  let jenv := jenv0 ++ (Claims.jobEnv cs gotMem (← Env.var "NIX_CONFIG")).filter fun (k, _) => !(jenv0.any (·.1 == k))
  let sub (x : String) := x.replace "{cores}" cs
  let full := match Json.fstr cfg "prefix" with
    | some p => sub p ++ " " ++ (if argv.length == 1 then "sh -c " ++ shquote line else line)
    | none => line
  let jid ← match resume.bind (Json.fstr · "jid") with
    | some j => pure j
    | none => Store.txn [.«meta»] fun db =>
      let n := match db.getMeta "jobs" with | some r => ((r.v.bind parseInt).getD 0) + 1 | none => 1
      (db.setMeta "jobs" (some (d n)), d n)
  let jenv := jenv.filter (fun (k, _) => k != "SWARM_JOB_ID" && k != "SWARM_JOB_MACHINE") ++ [("SWARM_JOB_ID", jid), ("SWARM_JOB_MACHINE", chosen.getD hn)]
  -- an explicit --mem is a hard cap, in the job's own scope `swarm-job-<agent>-j<jid>` (a local job's with its pid after, a scope name is per machine); a defaulted one only a reservation
  let unit := "swarm-job-" ++ String.ofList (who.toLower.toList.map fun c => if c.isLower || c.isDigit || c == '_' || c == '-' then c else '-') ++ "-j" ++ jid
  let dbp := match ← env "SWARM_DB" with | some p => p | none => common ++ "/swarm/swarm.db"
  let jobs := joinPath (joinPath (dirname dbp) "jobs") jid
  discard <| Sys.mkdirp jobs
  let logf := jobs ++ "/log"
  let task ← Store.txn [.task] fun db => (db, ((db.tasks.filter fun t => t.owner == some who && (t.state = .claimed || t.state = .blocked)).head?.map (·.id)))
  let dir := s!"{RUN_DIR}/{repo}/{wtname}"
  let on := chosen
  let rec0 : List (String × Option Json) := [("machine", on.map .str), ("wt", some (.str top)), ("task", task.map fun t => Json.int t),
    ("cmd", some (.str full)), ("claim", if claimId.isEmpty then none else some (.str claimId)), ("pid", some (Json.int (← Sys.getpid))), ("cores", some (Json.int gotCores)), ("mem_kb", some (Json.int gotMem)),
    ("parent", (parent.bind parseInt).map Json.int), ("detached", if detached then some (.bool true) else none)]
  if a.flag "detach" && !detached then
    return ← detachStart a argv claimId jid jobs unit cwd chosen gotCores gotMem waitS estF
  if detached && chosen.isNone && !nested then
    -- the claim's holder becomes this process: it drops when this dies
    discard <| Sys.exec ["sh", "-c", "f=\"${SWARM_COMPUTE_DIR:-${XDG_STATE_HOME:-$HOME/.local/state}/swarm-compute}/claims/$2\"; " ++
      "if [ -f \"$f\" ]; then sed \"s/^\\([^ ]* [^ ]* \\)[^ ]* /\\1p$1 /\" \"$f\" > \"${f%/*}/.h$1\" && mv \"${f%/*}/.h$1\" \"$f\"; fi", "sh", toString (← Sys.getpid), claimId] {}
  if detached then discard <| Fs.write (jobs ++ "/ready") "1"
  let t0 ← Sys.nowF
  let ctx : JobCtx := { who, jid, on, nested, claimId, waitS, t0, full, line, repo, jobs, logf, memFlag, detached, task }
  -- the dev shell (devshellScript): the line goes through it unless opted out, a nix line, or no flake.nix
  let devOn := !a.flag "no_devshell" && (Json.field cfg "devshell") != some (.bool false) && !startsNix line &&
    (← Sys.kind (joinPath top "flake.nix") false) == .file
  let some mach := on | do
    jobEv who jid "job-start" (obj rec0)
    let tree ← treeOf top
    discard <| Fs.write (jobs ++ "/cmd") (if devOn then wrapFull cfg cs line (shquote top) (shquote (common ++ "/swarm/devshell")) else full)
    discard <| Fs.write (jobs ++ "/measure.sh") measureScript
    let jobCmd := Claims.lowPrio (measured (unit ++ "-" ++ toString (← Sys.getpid)) memFlag jobs)
    let r ← Sys.exec ["sh", "-c", "exec < /dev/null; " ++ jobCmd] { env := jenv.map fun (k, v) => (k, some v), stdoutFile := some logf }
    finishJob ctx (.n r.code.toNat) tree none none [] none
  runRemote ctx mach top cs unit dir rel wtname cfg jenv devOn rec0

/-- `swarm job record …`'s parser. -/
def jobSpec : Spec :=
  .mk "job" helpJob [] [] [] (cmdTarget := some "act") (cmds := [
    .mk "record" helpJobRecord []
      [{ opt "--who" with minCount := 1 }, opt "--task" none (some int), opt "--parent", opt "--machine", opt "--cores" none (some int),
       opt "--start" none (some int), { opt "--wall" with minCount := 1, conv := some int }, opt "--cpu" none (some int),
       opt "--peak-kb" none (some int), { opt "--exit" with minCount := 1 }, opt "--log"] [] [] none])

/-- The words after `job`: the options, and the command after the first `--`. -/
def splitJob (args : List String) : List String × List String :=
  match args.findIdx? (· == "--") with
  | some i => (args.take i, args.drop (i + 1))
  | none => (args, [])

/-- A job id as typed (`12` or `j12`), its number. -/
def jobNum (s : String) : Option Int := parseInt (if s.startsWith "j" then (s.drop 1).toString else s)

/-- `swarm job record`: a job that ran elsewhere or inside another job's claim as a job of its own: its events, log and history row.
Claims nothing, runs nothing. -/
def jobRecord (a : Parsed) : m UInt32 := do
  let argv := a.strs "argv"
  if argv.isEmpty then die "usage: swarm job record --who <agent> --wall <s> --exit <code|lost> [options] -- <cmd…>"
  let who := (a.str "who").getD "human"
  let some wall := a.int "wall" | die "--wall: needed"
  if wall < 0 then die "--wall: not a count of seconds"
  let code : Code ← match a.str "exit" with
    | some "lost" => pure .lost
    | some c => match parseInt c with
      | some n => pure (.n n)
      | none => die s!"--exit: not a code or lost: {c}"
    | none => die "--exit: needed"
  let parent ← match a.str "parent" with
    | none => pure ((← env "SWARM_JOB_ID").bind jobNum)
    | some p => match jobNum p with
      | some n => pure (some n)
      | none => die s!"--parent: not a job id: {p}"
  let some top0 ← git ["rev-parse", "--show-toplevel"] | die "not in a git repo"
  if top0 == "" then die "not in a git repo"
  let top := (← Sys.realpath top0).getD top0
  let common := (← git ["rev-parse", "--path-format=absolute", "--git-common-dir"]).getD ""
  let repo := sanitize (if common.endsWith "/.git" then basename (dirname common) else basename top)
  let line := if argv.length == 1 then argv.head! else shjoin argv
  let now ← Clock.now
  let t1 := match a.int "start" with | some st => st + wall | none => now
  let t0 := t1 - wall
  let jid ← Store.txn [.«meta»] fun db =>
    let n := match db.getMeta "jobs" with | some r => ((r.v.bind parseInt).getD 0) + 1 | none => 1
    (db.setMeta "jobs" (some (d n)), d n)
  let dbp := match ← env "SWARM_DB" with | some p => p | none => common ++ "/swarm/swarm.db"
  let jobs := joinPath (joinPath (dirname dbp) "jobs") jid
  discard <| Sys.mkdirp jobs
  if let some lf := a.str "log" then discard <| Sys.exec ["cp", lf, jobs ++ "/log"] {}
  let hn ← Sys.hostname
  let mach := a.str "machine"
  let task ← match a.int "task" with
    | some t => pure (some t)
    | none => Store.txn [.task] fun db => (db, ((db.tasks.filter fun t => t.owner == some who && (t.state = .claimed || t.state = .blocked)).head?.map (·.id)))
  let start := obj [("machine", mach.map .str), ("wt", some (.str top)), ("task", task.map fun t => Json.int t), ("cmd", some (.str line)),
    ("pid", some (Json.int (← Sys.getpid))), ("cores", (a.int "cores").map Json.int), ("parent", parent.map Json.int)]
  let end_ := obj [("machine", mach.map .str), ("exit", some (match code with | .n c => Json.int c | .lost => .str "lost")),
    ("s", some (Json.int wall)), ("wait_s", some (Json.int 0))]
  Store.txn [] fun db =>
    ((db.log t0 (some who) "job-start" (some jid) (some (Json.encode start))).log t1 (some who) "job-end" (some jid) (some (Json.encode end_)), ())
  let repoNm := (← Cost.repoName).getD repo
  let cpuS := (a.int "cpu").getD 0
  let peak := (a.int "peak_kb").getD 0
  let row : Cost.Rec := { ts := t1, machine := mach.getD hn, repo := repoNm, agent := who, source := "run", cmd := line, key := some (Cost.key line), wall_s := wall, cpu_s := cpuS, peak_kb := peak }
  discard <| Cost.record row
  Env.out s!"recorded j{jid}"
  return 0

/-- The group: run and job. -/
def group : Group m where
  specs := [("run", spec), ("job", jobSpec)]
  run a := if a.cmd == "job" then jobRecord a else run a

end SwarmLean.Cmd.Run
