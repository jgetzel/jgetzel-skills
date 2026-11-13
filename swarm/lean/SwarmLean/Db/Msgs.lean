import SwarmLean.Db

/-! msgs.lua's post, which task commands use; the rest of msgs.lua is board task #98's. -/

namespace SwarmLean.Msgs

/-- Posts a message from `frm` to `dest` (msgs.post): the db and the message's id. -/
def post (db : Db) (now : Int) (frm dest body : String) (urgent : Bool := false) (kind : Option String := none) :
    Db × Nat :=
  let kind := kind.getD (if dest == "@all" then "all" else "dm")
  let id := db.msgNext
  let msg : Msg := { id, ts := some now, frm := some frm, dest := some dest, body := some body,
                     urgent := some (if urgent then 1 else 0), kind := some kind }
  let db := { db with msgs := db.msgs ++ [msg], msgNext := db.msgNext + 1 }
  (db.log now (some frm) "post" (some dest) (some ((if urgent then "[urgent] " else "") ++ cut body 200)), id)

end SwarmLean.Msgs
