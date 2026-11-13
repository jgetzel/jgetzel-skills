import SwarmLean.Db.Msgs
import SwarmLean.World

/-! msgs.lua's formatting and delivery, which need the local time. -/

namespace SwarmLean.Msgs

variable {m : Type → Type} [Monad m] [Clock m]

/-- Messages one per line (msgs.fmt_msgs); a row with no time shows now's, as os.date(nil) does. -/
def fmtMsgs (rows : List Msg) : m String := do
  let now ← Clock.now
  let ls ← rows.mapM fun r => return fmtMsg (← Clock.hhmm (r.ts.getD now)) r
  return "\n".intercalate ls

/-- The unread messages that fit in `budget` chars, marked read; the rest stay unread with a pointer (msgs.deliver). -/
def deliver [Store m] (name : String) (budget : Nat := CTX_CAP) : m String := do
  let (fit, more) ← Store.txn [.msg, .cursor] (deliverStep name budget)
  let now ← Clock.now
  let hh ← fit.mapM fun r => Clock.hhmm (r.ts.getD now)
  return deliverNote hh fit more

end SwarmLean.Msgs
