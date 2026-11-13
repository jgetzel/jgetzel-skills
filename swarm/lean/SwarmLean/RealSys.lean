import SwarmLean.Sys
import SwarmLean.Real

/-! `Sys` on IO: Lean's IO where it has the call, else c/shim.c. -/

namespace SwarmLean
namespace Shim
@[extern "swarm_alive"] opaque alive (pid : Int64) : IO Bool
@[extern "swarm_getppid"] opaque getppid : IO UInt64
@[extern "swarm_now_f"] opaque nowF : IO Float
@[extern "swarm_strftime"] opaque strftime (fmt : @& String) (t : Int64) : IO String
@[extern "swarm_mktime"] opaque mktime (y mo d h mi s : Int64) : IO UInt64
@[extern "swarm_hostname"] opaque hostname : IO String
@[extern "swarm_environ"] opaque environ : IO (Array String)
@[extern "swarm_setenv"] opaque setenv (k v : @& String) : IO Unit
@[extern "swarm_readlink"] opaque readlink (p : @& String) : IO String
@[extern "swarm_link"] opaque link (a b : @& String) : IO Unit
end Shim

/-- proc.exec on IO: stdin piped when there is input (else inherited), stdout and stderr read to their ends. -/
def execIO' (argv : List String) (o : RunOpts) : IO ProcOut := do
  -- a redirect is the shell's: `sh` opens the file (or dups stderr) and execs argv
  let argv := match o.stdoutFile with
    | some f => ["sh", "-c", "exec >\"$1\" 2>&1 || exit 127; shift; exec \"$@\"", "sh", f] ++ argv
    | none => if o.merge then ["sh", "-c", "exec 2>&1; exec \"$@\"", "sh"] ++ argv else argv
  let some cmd := argv.head? | return { code := 127, stdout := "", stderr := "" }
  let cwd : Option System.FilePath := o.cwd.map System.FilePath.mk
  let finish (stdout stderr : IO.FS.Handle) (wait : IO UInt32) : IO ProcOut := do
    let errT ← IO.asTask stderr.readToEnd
    let out ← stdout.readToEnd
    let err ← IO.ofExcept (← IO.wait errT)
    let code ← wait
    -- Lean's spawn reports an exec that failed in the child as 255 and this text; proc.exec's is 127
    if code == 255 && err.startsWith "could not execute external process" then
      return { code := 127, stdout := out, stderr := "" }
    return { code, stdout := out, stderr := err }
  try
    match o.input with
    | some s =>
      let child ← IO.Process.spawn { cmd, args := argv.tail.toArray, cwd, env := o.env.toArray,
                                     stdin := .piped, stdout := .piped, stderr := .piped }
      let (stdin, child) ← child.takeStdin
      -- written while the child reads, so neither side blocks on a full pipe; a child that closed its stdin gets no more
      let inT ← IO.asTask (do try stdin.putStr s; stdin.flush catch _ => pure ())
      let r ← finish child.stdout child.stderr child.wait
      discard <| IO.wait inT
      return r
    | none =>
      let child ← IO.Process.spawn { cmd, args := argv.tail.toArray, cwd, env := o.env.toArray,
                                     stdin := .inherit, stdout := .piped, stderr := .piped }
      finish child.stdout child.stderr child.wait
  catch _ => return { code := 127, stdout := "", stderr := "" }

/-- Sys.sqlAt on IO. -/
def sqlAtIO (path schema : String) (stmts : List (String × List Sqlite.Val)) (ro : Bool) :
    IO (List (Array (Array Sqlite.Val))) := do
  if ro then
    let c ← Sqlite.Conn.open path true
    return ← stmts.mapM fun (q, ps) => c.query q ps
  if let some d := (path : System.FilePath).parent then if d.toString ≠ "" then IO.FS.createDirAll d
  let c ← Sqlite.Conn.open path false
  c.script schema
  discard <| c.exec "begin immediate"
  try
    let r ← stmts.mapM fun (q, ps) => c.query q ps
    discard <| c.exec "commit"
    return r
  catch e =>
    try discard <| c.exec "rollback" catch _ => pure ()
    throw e

instance : Sys App where
  getpid := return (← IO.Process.getPID).toNat
  getppid := return (← Shim.getppid).toNat
  pidAlive p := Shim.alive (Int64.ofInt p)
  sleep ms := IO.sleep ms.toUInt32
  nowF := Shim.nowF
  date f t := Shim.strftime f (Int64.ofInt t)
  hostname := Shim.hostname
  environ := return (← Shim.environ).toList.map fun e =>
    match e.splitOn "=" with | k :: v => (k, "=".intercalate v) | [] => (e, "")
  setenv k v := Shim.setenv k v
  realpath p := (do try return some (← IO.FS.realPath p).toString catch _ => return none : IO _)
  readlink p := (do try return some (← Shim.readlink p) catch _ => return none : IO _)
  kind p follow := (do
    try
      let md ← if follow then System.FilePath.metadata p else System.FilePath.symlinkMetadata p
      return match md.type with | .file => .file | .dir => .dir | .symlink => .link | _ => .other
    catch _ => return .none : IO _)
  mtime p := (do try return some (← System.FilePath.metadata p).modified.sec catch _ => return none : IO _)
  mkdirp p := (do try IO.FS.createDirAll p; return true catch _ => return false : IO _)
  link a b := (do try Shim.link a b; return true catch _ => return false : IO _)
  remove p := (do try IO.FS.removeFile p; return true catch _ => return false : IO _)
  exec argv o := execIO' argv o
  sqlAt path schema stmts ro := sqlAtIO path schema stmts ro

end SwarmLean
