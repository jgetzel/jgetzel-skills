import SwarmLean.Lib.Ci

/-! ci_spec.lua's asserts on watchd's CI steps (pr_ci, ci_poll, ci_check, pr_watch), run as the pure steps with what
the spec's fake gh answers; the gh call counts are the gates' answers. -/

open SwarmLean Ci Lean

/-- A JSON list literal. -/
def js (s : String) : List Json := Json.items ((SwarmLean.Json.decode s).getD .null)

/-- The test's clock. -/
def T0 : Int := 1800000000

/-- A db with live agent a and done task 1 for PR #7, and a red then a green run (the spec's pr_ci setup). -/
def prDb : Db :=
  { agents := [{ name := "a", started := some 1 }],
    tasks := [{ id := 1, title := some "t1", state := .done, owner := some "a", evidence := some "PR #7 merged",
                done_at := some T0, first_claimed_at := some 1 }],
    cis := [{ id := 1, sha := some "red", status := some "completed", conclusion := some "failure",
              created := some "2026-11-08T10:00:05Z", updated := some "2026-11-08T10:02:00Z" },
            { id := 2, sha := some "fix", status := some "completed", conclusion := some "success",
              created := some "2026-11-08T10:05:00Z", updated := some "2026-11-08T10:08:00Z" }],
    taskNext := 2 }

-- pr_ci: the PR, its main run's conclusion and the green after it; the PR list at most every 10 minutes
#guard (prCiGate T0 prDb).2 && !(prCiGate (T0 + 60) (prCiGate T0 prDb).1).2
#guard
  let t := ((prCiApply T0 (js "[{\"number\":7,\"mergedAt\":\"2026-11-08T10:00:00Z\",\"mergeCommit\":{\"oid\":\"red\"},\"headRefName\":\"a/x\"}]") prDb).find 1).get!
  t.pr == some 7 && t.ci_conclusion == some "failure" && t.ci_green_at.get! - t.merged_at.get! == 480
-- merged while its main run is still going: filled in once the run completes
def pr8 : List Json := js "[{\"number\":8,\"mergedAt\":\"2026-11-08T11:00:00Z\",\"mergeCommit\":{\"oid\":\"m8\"},\"headRefName\":\"a/y\"}]"
def db8 : Db := { prDb with
  tasks := prDb.tasks ++ [{ id := 2, title := some "t2", state := .done, owner := some "a", evidence := some "PR #8 merged", done_at := some T0, first_claimed_at := some 1 }],
  cis := prDb.cis ++ [{ id := 3, sha := some "m8", status := some "in_progress", created := some "2026-11-08T11:00:05Z", updated := some "2026-11-08T11:00:05Z" }] }
#guard let t := ((prCiApply T0 pr8 db8).find 2).get!; t.pr == some 8 && t.merged_at.isSome && t.ci_conclusion.isNone
#guard
  let db := prCiApply T0 pr8 db8
  let db := { db with cis := db.cis.map fun c => if c.id == 3 then { c with status := some "completed", conclusion := some "success", updated := some "2026-11-08T11:04:00Z" } else c }
  let t := ((prCiApply T0 pr8 db).find 2).get!
  t.ci_conclusion == some "success" && t.ci_green_at.get! - t.merged_at.get! == 240

-- ci_poll: a request for the runs, then the red run's jobs; none within the minute; a refusal keeps the table
def run1 : List Json := js "[{\"databaseId\":1,\"headSha\":\"a1\",\"status\":\"completed\",\"conclusion\":\"failure\",\"url\":\"u1\",\"createdAt\":\"2026-11-08T10:00:00Z\",\"updatedAt\":\"2026-11-08T10:03:00Z\",\"event\":\"push\"}]"
#guard (ciPollGate T0 false 60 {}).2 && !(ciPollGate (T0 + 30) false 60 (ciPollGate T0 false 60 {}).1).2
#guard (ciPollApply T0 (some run1) none {}).2 == [1]
#guard
  let db := (ciPollApply T0 (some run1) none {}).1
  let db := (ciPollApply T0 none none db).1
  db.cis.length == 1 && (db.getMeta "ci_error").isSome && !(ciPollGate (T0 + 100) false 60 db).2

-- ci_check: one red task naming the live suspect, a later red joins it, green closes it and tells the fixer
def RED : String := "0123456789abcdef"
def redRun (id : Nat) (concl : Option String) (at_ : String) (status := "completed") (url := "u") : _root_.SwarmLean.Ci :=
  { id, sha := some RED, status := some status, conclusion := concl, url := some url, created := some at_ }
def chkDb : Db := { agents := [{ name := "a", started := some 1 }], cis := [redRun 9 (some "failure") "2026-11-08T10:05:00Z" (url := "http://ci/9")] }
/-- ci_check as watchd runs it, with the authors git log names. -/
def check (db : Db) (names : List String := ["a", "gone"]) : Db :=
  match ciCheckFirst T0 db with
  | (db, some r) => ciCheckApply T0 (some "comms") r "-20 x" names "" db
  | (db, none) => db
-- F5: the first transaction leaves a new red run's `ci-red` event to the second, which commits it with the task
#guard (ciCheckFirst T0 chkDb).1.events.isEmpty
#guard authors "x\n\nSwarm-Agent: gone\n\x1e\ny\n\nSwarm-Agent: a\n\x1e\n" == ["a", "gone"]
def c1 : Db := check (check chkDb)
#guard (c1.tasks.filter (likePrefix ·.title.get! "main red:")).length == 1
#guard
  let m := c1.msgs.filter (·.kind == some "system")
  m.length == 1 && m.head!.dest == some "a" && hasSub m.head!.body.get! "http://ci/9" && hasSub m.head!.body.get! "swarm task claim 1"
def c2 : Db := check { c1 with cis := c1.cis ++ [redRun 10 (some "failure") "2026-11-08T10:10:00Z"] }
#guard c2.tasks.length == 1 && hasSub (c2.find 1).get!.body.get! "Later red: run 10"
def c3 : Db := check { (c2.set 1 fun t => { t with state := .claimed, owner := some "a" }) with
  cis := c2.cis.map fun c => if c.id == 10 then { c with status := some "in_progress", conclusion := none } else c }
#guard (c3.find 1).get!.state = .claimed
def c4 : Db := check { c3 with cis := c3.cis ++ [redRun 11 (some "success") "2026-11-08T10:20:00Z"] }
#guard let t := (c4.find 1).get!; t.state = .done && t.evidence == some ("green run 11 at " ++ (RED.take 7).toString)
#guard hasSub (c4.msgs.filter (·.dest == some "a")).getLast!.body.get! "is done; stop fixing it"
-- no live suspect: comms hears
def c5 : Db := check { c4 with agents := c4.agents.map ({ · with ended := some 1 }), events := c4.events.filter (·.kind != some "ci-red"), cis := [redRun 9 (some "failure") "2026-11-08T10:05:00Z"] }
#guard (c5.msgs.filter (·.dest == some "comms")).length == 1

-- a scheduled (or other) workflow's green run on the red sha is not main's CI: the red task stays and ci reads red
def wfRun (id : Nat) (concl event wf at_ : String) : String :=
  s!"\{\"databaseId\":{id},\"headSha\":\"{RED}\",\"status\":\"completed\",\"conclusion\":\"{concl}\",\"url\":\"u\",\"createdAt\":\"{at_}\",\"updatedAt\":\"{at_}\",\"event\":\"{event}\",\"workflow\":\"{wf}\",\"path\":\".github/workflows/{wf}.yml\"}"
def wfDb : Db := check (ciPollApply T0 (some (js s!"[{wfRun 22 "success" "push" "deploy" "2026-11-08T11:02:00Z"},{wfRun 21 "success" "schedule" "ci" "2026-11-08T11:01:00Z"},{wfRun 20 "failure" "push" "ci" "2026-11-08T11:00:00Z"}]"))
  (some "ci.yml") { cis := [{ id := 5, sha := some "old", status := some "completed", conclusion := some "success", created := some "2026-11-08T09:00:00Z" }] }).1
#guard wfDb.cis.map (fun c => (c.id, c.workflow)) == [(20, some "ci")]
#guard (wfDb.tasks.filter fun t => (t.title.get!).startsWith "main red: run 20" && t.state = .open).length == 1
instance : Git Id := ⟨fun _ _ => none⟩
#guard (Id.run (ciFor wfDb.cis RED none)).1 == "failure"
-- a sha's own finished run beats a later pending one; a later finished run stands for a cancelled sha
def batch (own : String) : List _root_.SwarmLean.Ci :=
  [{ id := 1, sha := some "a", status := some "completed", conclusion := some own, created := some "2026-11-08T10:00:00Z" },
   { id := 2, sha := some "b", status := some "in_progress", created := some "2026-11-08T10:05:00Z" }]
@[instance_reducible] def allAncestors : Git Id := ⟨fun _ _ => some ""⟩
#guard (letI := allAncestors; Id.run (ciFor (batch "failure") "a" none)) matches ("failure", some { id := 1, .. })
#guard (letI := allAncestors; Id.run (ciFor (batch "cancelled") "a" none)) matches ("pending", some { id := 2, .. })
#guard (letI := allAncestors; Id.run (ciFor ({ (batch "failure")[1]! with status := some "completed", conclusion := some "success" } :: batch "cancelled") "a" none)) matches ("success", some { id := 2, .. })

-- pr_watch: no gh call while no live agent holds a claim; then one a minute, matched by <owner>/<task> into the base
def okRollup : String := "[{\"status\":\"COMPLETED\",\"conclusion\":\"SUCCESS\",\"name\":\"ci\"}]"
def prs3 : List Json := js s!"[\{\"number\":30,\"headRefName\":\"a/9\",\"headRefOid\":\"h9\",\"baseRefName\":\"main\",\"state\":\"OPEN\",\"statusCheckRollup\":{okRollup}},
  \{\"number\":31,\"headRefName\":\"b/9\",\"headRefOid\":\"hb\",\"baseRefName\":\"main\",\"state\":\"OPEN\",\"statusCheckRollup\":{okRollup}},
  \{\"number\":32,\"headRefName\":\"a/9\",\"headRefOid\":\"h0\",\"baseRefName\":\"main\",\"state\":\"MERGED\",\"mergedAt\":\"2000-01-01T00:00:00Z\",\"statusCheckRollup\":{okRollup}}]"
#guard (prWatchGate T0 { agents := [{ name := "a", ended := some 1 }] }).2.isNone
def w0 : Db := { agents := [{ name := "a" }], tasks := [{ id := 9, title := some "t9", state := .claimed, owner := some "a", first_claimed_at := some (T0 - 60) }], taskNext := 10 }
/-- One pr_watch tick on db with gh's PR list, as prWatch runs it (base main). -/
def watch (db : Db) (prs : List Json) (gated : Bool) (now := T0) : Db :=
  match prWatchGate now db with
  | (db, some hs) => hs.foldl (fun db (t, brs) => match pickPr prs brs "main" (t.first_claimed_at.getD 0) with
      | some pr => prWatchApply now gated t pr db
      | none => db) db
  | (db, none) => db
def w1 : Db := watch (watch w0 prs3 true) prs3 true
#guard (prWatchGate T0 w0).2.isSome && (prWatchGate (T0 + 1) (prWatchGate T0 w0).1).2.isNone
#guard
  let m := w1.msgs.filter (·.dest == some "a")
  m.length == 1 && m.head!.urgent == some 1 && hasSub m.head!.body.get! "PR #30's checks are green"
-- told once per head and verdict
def w2 : Db := watch w1 prs3 true (now := T0 + 120)
#guard (w2.msgs.filter (·.dest == some "a")).length == 1 && (w2.find 9).get!.state = .claimed
-- merged: done with the merge sha, in any flow
def w3 : Db := watch w2 (js s!"[\{\"number\":30,\"headRefName\":\"a/9\",\"headRefOid\":\"h9\",\"baseRefName\":\"main\",\"state\":\"MERGED\",\"mergedAt\":\"2030-01-01T00:00:00Z\",\"mergeCommit\":\{\"oid\":\"abcdef123\"},\"statusCheckRollup\":{okRollup}}]") false (now := T0 + 240)
#guard let t := (w3.find 9).get!; t.state = .done && t.evidence == some "PR #30 merged as abcdef1" && t.pr == some 30
#guard (w3.msgs.filter fun m => m.dest == some "a" && m.urgent == some 1).length == 2
-- not pr-gated: green checks wake no one
def w4 : Db := watch { w3 with tasks := w3.tasks ++ [{ id := 10, title := some "t10", state := .claimed, owner := some "a", first_claimed_at := some (T0 - 60) }] }
  (js s!"[\{\"number\":40,\"headRefName\":\"a/10\",\"headRefOid\":\"h10\",\"baseRefName\":\"main\",\"state\":\"OPEN\",\"statusCheckRollup\":{okRollup}}]") false (now := T0 + 360)
#guard (w4.msgs.filter (·.dest == some "a")).length == 2
-- flow none: no CI, so ci_poll asks nothing
#guard !(ciPollGate T0 true 60 {}).2
