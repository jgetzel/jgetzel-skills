import SwarmLean.Db.Msgs
import SwarmLean.Db.Sels
import SwarmLean.World

/-! msgs.lua's formatting and delivery, which need the local time, and the inbox's transactions. -/

namespace SwarmLean.Msgs

variable {m : Type → Type} [Monad m] [Clock m]

/-- Messages one per line (msgs.fmt_msgs); a row with no time shows now's, as os.date(nil) does. -/
def fmtMsgs (rows : List Msg) : m String := do
  let now ← Clock.now
  let ls ← rows.mapM fun r => return fmtMsg (← Clock.hhmm (r.ts.getD now)) r
  return "\n".intercalate ls

/-- `name`'s inbox, read: its cursor, then the messages past it to `name` or its swarm (`inbox`). Reads only. -/
def inboxTxn (name : String) (also : List Sel := []) : Txn Db := do
  let c ← Txn.slice [Sels.cursor name]
  Txn.slice ([Sels.cursor name, Sels.inbox name (inbox c name) (cursorOf c name)] ++ also)

/-- `take` on what it reads: `name`'s unread rows and the prefix `pick` chooses, that prefix marked read. -/
def takeTxn (name : String) (pick : List Msg → List Msg := id) : Txn (List Msg × List Msg) := do
  let d ← inboxTxn name
  let (d', rows, fit) := take name pick d
  Txn.exec (slicePlan d d')
  pure (rows, fit)

/-- `deliverStep` on what it reads: the unread rows that fit in `budget` marked read, and how many stay unread. -/
def deliverTxn (name : String) (budget : Nat) : Txn (List Msg × Nat) := do
  let (rows, fit) ← takeTxn name (fits budget)
  pure (fit, rows.length - fit.length)

/-- The unread messages that fit in `budget` chars, marked read; the rest stay unread with a pointer (msgs.deliver). -/
def deliver [Store m] (name : String) (budget : Nat := CTX_CAP) : m String := do
  let (fit, more) ← Store.run (deliverTxn name budget)
  let now ← Clock.now
  let hh ← fit.mapM fun r => Clock.hhmm (r.ts.getD now)
  return deliverNote hh fit more

end SwarmLean.Msgs
