import SwarmLean.Lib.Ci

/-! `swarm pr merge-when-green`'s core: a head whose checks were seen green, which only a read of one `gh pr view`
response can make, so a merge can only name the sha that read saw. -/

namespace SwarmLean.Merge
open Lean (Json)

/-- The fields `GreenHead.parse` reads, as `gh pr view --json` takes them. -/
def VIEW_FIELDS : String := "state,mergeable,headRefOid,statusCheckRollup"

/-- A rollup whose every check is COMPLETED with SUCCESS or SKIPPED, and that has one. -/
def checksPass (rollup : Option Json) : Bool :=
  let xs := (rollup.map Json.items).getD []
  !xs.isEmpty && xs.all fun x =>
    Json.fstr x "status" == some "COMPLETED" && (Json.fstr x "conclusion" == some "SUCCESS" || Json.fstr x "conclusion" == some "SKIPPED")

/-- A PR's head whose checks were all green and which was mergeable when one `gh pr view` response showed it; only
`GreenHead.parse` makes one. -/
structure GreenHead where private mk ::
  pr : Nat
  sha : String
  deriving Repr

/-- The green head of PR `pr` in one `gh pr view --json state,mergeable,headRefOid,statusCheckRollup` response: its
full headRefOid when the PR is open and mergeable and its checks pass. -/
def GreenHead.parse (pr : Nat) (resp : String) : Option GreenHead :=
  match Json.decode resp with
  | none => none
  | some j =>
    match Json.fstr j "headRefOid" with
    | none => none
    | some sha =>
      if Json.fstr j "state" == some "OPEN" && Json.fstr j "mergeable" == some "MERGEABLE" &&
          checksPass (Json.field j "statusCheckRollup") && !sha.isEmpty then some ⟨pr, sha⟩ else none

/-- A green head's sha is the headRefOid of the response it was parsed from. -/
theorem GreenHead.sha_of_parse {pr : Nat} {resp : String} {g : GreenHead} (h : GreenHead.parse pr resp = some g) :
    ∃ j, Json.decode resp = some j ∧ Json.fstr j "headRefOid" = some g.sha := by
  unfold GreenHead.parse at h
  split at h
  · cases h
  · rename_i j hj
    split at h
    · cases h
    · rename_i sha hs
      split at h
      · cases h; exact ⟨j, hj, hs⟩
      · cases h

/-- The `gh pr merge` argv for a green head: squash, and only if the head is still the sha that was green. -/
def GreenHead.mergeArgv (g : GreenHead) : List String :=
  ["gh", "pr", "merge", toString g.pr, "--squash", "--match-head-commit", g.sha]

/-- The merge argv names the green head's sha. -/
theorem GreenHead.mergeArgv_sha (g : GreenHead) : g.sha ∈ g.mergeArgv := by simp [mergeArgv]

/-- The PR's state in a `gh pr view` response. -/
def stateOf (resp : String) : Option String := (Json.decode resp).bind (Json.fstr · "state")

/-- The "state mergeable sha7 green|notgreen" line a PR that is not yet merged waits with. -/
def waiting (resp : String) : String :=
  match Json.decode resp with
  | none => "api-error"
  | some j =>
    s!"{(Json.fstr j "state").getD ""} {(Json.fstr j "mergeable").getD ""} {((Json.fstr j "headRefOid").getD "").take 7} " ++
      (if checksPass (Json.field j "statusCheckRollup") then "green" else "notgreen")

private def view (state mergeable sha rollup : String) : String :=
  s!"\{\"state\":\"{state}\",\"mergeable\":\"{mergeable}\",\"headRefOid\":\"{sha}\",\"statusCheckRollup\":{rollup}}"

private def ok := "{\"status\":\"COMPLETED\",\"conclusion\":\"SUCCESS\"}"
private def skip := "{\"status\":\"COMPLETED\",\"conclusion\":\"SKIPPED\"}"

#guard (GreenHead.parse 7 (view "OPEN" "MERGEABLE" "abcdef0123" s!"[{ok},{skip}]")).map (·.sha) == some "abcdef0123"
#guard (GreenHead.parse 7 (view "OPEN" "MERGEABLE" "abcdef0123" s!"[{ok},\{\"status\":\"IN_PROGRESS\",\"conclusion\":\"\"}]")).isNone
#guard (GreenHead.parse 7 (view "OPEN" "MERGEABLE" "abcdef0123" s!"[{ok},\{\"status\":\"COMPLETED\",\"conclusion\":\"FAILURE\"}]")).isNone
#guard (GreenHead.parse 7 (view "OPEN" "MERGEABLE" "abcdef0123" "[]")).isNone
#guard (GreenHead.parse 7 (view "OPEN" "CONFLICTING" "abcdef0123" s!"[{ok}]")).isNone
#guard (GreenHead.parse 7 "not json").isNone

end SwarmLean.Merge
