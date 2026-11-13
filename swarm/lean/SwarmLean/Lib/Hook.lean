import SwarmLean.Db.Tasks
import SwarmLean.World
import Lean.Data.Json

/-! hook.lua's context reading and the communicator's nudge, which board prints. The hooks themselves are board task
#99's. -/

namespace SwarmLean.Hook

variable {m : Type → Type}
open Agents

/-- The context in tokens of the last assistant turn in a transcript's last 300 KB (hook.ctx_from). -/
def ctxFrom [Monad m] [Fs m] (path : Option String) : m (Option Int) := do
  let some p := path | return none
  let some s ← Fs.read p | return none
  let b := s.toUTF8
  let tail := if b.size > 300000 then String.fromUTF8? (b.extract (b.size - 300000) b.size) else some s
  -- shortcut: a cut inside a UTF-8 character drops the whole tail; Lua reads the bytes as they are.
  let lines := (tail.getD "").splitOn "\n"
  for l in lines.reverse do
    let some j := (Lean.Json.parse l).toOption | continue
    let some u := (j.getObjVal? "message").toOption.bind (·.getObjVal? "usage" |>.toOption) | continue
    let .obj kv := u | continue
    let isAsst := match j.getObjVal? "type" with | .ok (.str "assistant") => true | _ => false
    if kv.isEmpty || !isAsst then continue
    let num (k : String) : Int := match u.getObjVal? k with
      | .ok (.num n) => if n.exponent == 0 then n.mantissa else 0
      | .ok (.str t) => (parseInt t).getD 0
      | _ => 0
    return some (num "input_tokens" + num "cache_read_input_tokens" + num "cache_creation_input_tokens")
  return none

/-- tempfile.gettempdir(): $TMPDIR, $TEMP or $TMP, else /tmp. -/
def tmpdir [Monad m] [Env m] : m String := do
  return (← env "TMPDIR").getD <| (← env "TEMP").getD <| (← env "TMP").getD "/tmp"

/-- The context note at each +100k from 350k, once per step per session (hook.handoff_nudge). -/
def handoffNudge [Monad m] [Store m] [Clock m] [Env m] [Fs m] (name : String) (transcript : Option String)
    (sid : Option String) (comms : Bool) : m (Option String) := do
  let some k ← ctxFrom transcript | return none
  if k == 0 then return none
  Store.txn [.agent] fun db => (db.setAgent name ({ · with ctx_tokens := some k }), ())
  let step := fdiv (k - (Tasks.CTX_WARN - 100000)) 100000
  if step < 1 then return none
  let sidS := match sid with | some s => if s != "" then s else "x" | none => "x"
  let dir ← tmpdir
  let mark := if dir.endsWith "/" then dir ++ "claude-ctx-" ++ sidS else dir ++ "/claude-ctx-" ++ sidS
  let last := ((← Fs.read mark).bind parseInt).getD 0
  if step ≤ last then return none
  discard <| Fs.write mark (d step)
  let now ← Clock.now
  let stays ← Store.txn [.agent] fun db => (db.log now (some name) "ctx-note" none (some (d k)), (stayOf db name).isSome)
  return some s!"Context is ~{fdiv k 1000}k tokens: {Tasks.ctxAdvice k (comms || stays)}"

/-- What the communicator is told while the user is away (agents.away_line). -/
def awayLine [Monad m] [Clock m] (aw : Option Int × Option String) : m String := do
  let since ← Clock.hhmm (← match aw.1 with | some s => pure s | none => Clock.now)
  return s!"the user is away since {since}{match aw.2 with | some n => s!" ({n})" | none => ""}: don't ask them; decide what is yours to decide, queue the rest."

/-- The communicator runs no swarm hooks: read/wait/board/who print its away reminder and context note
(hook.comms_nudge); `toErr` for wait. -/
def commsNudge [Monad m] [Store m] [Clock m] [Env m] [Fs m] (toErr : Bool) : m Unit := do
  let some name ← env "SWARM_NAME" | return
  let sid ← env "CLAUDE_CODE_SESSION_ID"
  let envComms ← env "SWARM_COMMS"
  let (isC, aw) ← Store.txn [.meta] fun db => (db, (isComms db envComms (some name), away db))
  if !isC then return
  let n ← match sid with
    | none => pure none
    | some s =>
      let home := (← Env.var "HOME").getD ""
      let dirs := (((← Fs.list (home ++ "/.claude/projects")).getD []).toArray.qsort (· < ·)).toList
      let mut tr : Option String := none
      for dd in dirs do
        if ((← Fs.list s!"{home}/.claude/projects/{dd}").getD []).contains s!"{s}.jsonl" then
          tr := some s!"{home}/.claude/projects/{dd}/{s}.jsonl"; break
      handoffNudge name tr sid true
  let awL ← match aw with
    | some a => pure [← awayLine a]
    | none => pure []
  let say := awL ++ n.toList
  for s in say do if toErr then Env.err s else Env.out s

end SwarmLean.Hook
