import SwarmLean.Db.Msgs

/-! msgs_spec.lua's asserts: two deliveries to one inbox (the waiter's and a hook's) show each message once. Each is one
transaction here, so the race is the two run one after the other. -/

namespace SwarmLean.Tests.Msgs
open SwarmLean.Msgs

/-- A delivery's note with every time shown as `00:00`. -/
def note (r : Db × List Msg × Nat) : String := deliverNote (r.2.1.map fun _ => "00:00") r.2.1 r.2.2

/-- n's cursor at 0 and two messages to it from p. -/
def db0 : Db :=
  let db : Db := { cursors := [{ agent := "n", last_msg_id := some 0 }] }
  (post (post db 0 "p" "n" "one").1 0 "p" "n" "two").1

/-- The first delivery (the hook's, run in between). -/
def other := deliverStep "n" CTX_CAP db0
/-- The second (the one the hook raced). -/
def mine := deliverStep "n" CTX_CAP other.1

#guard hasSub (note other) "one" && hasSub (note other) "two"
#guard !hasSub (note mine) "one" && !hasSub (note mine) "two"
#guard cursorOf mine.1 "n" == 2

/-- An uncontested delivery still shows and marks it. -/
def third := deliverStep "n" CTX_CAP (post mine.1 0 "p" "n" "three").1

#guard hasSub (note third) "three" && (unread third.1 "n").isEmpty

/-- A budget too small for one message: none shown, both left unread with a pointer (msgs.deliver). -/
def tight := deliverStep "n" 130 db0

#guard note tight == "2 more unread message(s), too long to show here: run `swarm read`." && cursorOf tight.1 "n" == 0

/-- A notice to n. -/
def notice : Db := (post db0 0 "p" "n" "fyi" false (some "notice")).1

-- notices ride along and never wake; an urgent one does, cold or not (msgs.wakes)
#guard (wakes (m := Id) ((unread notice "n").drop 2) (pure false)).isNone
#guard (wakes (m := Id) (unread notice "n") (pure true)).isNone
#guard (wakes (m := Id) (unread (post db0 0 "p" "n" "!" true (some "notice")).1 "n") (pure true)).map (·.2) == some true
#guard (wakes (m := Id) (unread notice "n") (pure false)).map (·.1.length) == some 2

end SwarmLean.Tests.Msgs
