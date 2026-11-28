import LSql.Bytes
import LSql.Record
/-! The pager: a database's pages decoded into b-tree nodes (fileformat2.html §1.3-1.6), the journals that undo a statement
or a transaction, and the database file read whole and written back whole at commit. -/
namespace LSql

abbrev Pgno := UInt32

/-- A cell's payload (a table row's record, or an index key) and the overflow pages holding what does not fit the page. -/
structure Cell where
  payload : ByteArray
  ovfl : Array Pgno := #[]
  /-- the bytes the cell takes on a leaf page, cell pointer excluded (computed when the cell is made) -/
  size : Nat := 0
  deriving Inhabited

inductive TreeKind where
  | table | index
  deriving DecidableEq, Repr, Inhabited

/-- A b-tree page. In an interior node `kids.size = keys.size + 1` (the last kid is the right child). A table tree keys its
rows by rowid; an interior table key is the largest rowid of its left subtree. An index tree's interior keys are entries.
A leaf's `used` is the bytes its cells take on the page, cell pointers included (`leafUsed` of its cells). -/
inductive Node : TreeKind → Type where
  | tleaf (keys : Array Int64) (cells : Array Cell) (used : Nat) : Node .table
  | tinner (keys : Array Int64) (kids : Array Pgno) : Node .table
  | ileaf (cells : Array Cell) (used : Nat) : Node .index
  | iinner (cells : Array Cell) (kids : Array Pgno) : Node .index

instance : Inhabited (Node .table) := ⟨.tleaf #[] #[] 0⟩
instance : Inhabited (Node .index) := ⟨.ileaf #[] 0⟩

inductive Page where
  | table (n : Node .table)
  | index (n : Node .index)
  /-- part of a cell's overflow chain; its bytes are written from the owning cell -/
  | overflow
  /-- on the freelist -/
  | free
  /-- a page lean-sqlite does not interpret, kept as read -/
  | raw (b : ByteArray)
  deriving Inhabited

/-- Page geometry: the page size and the usable size (the page less its reserved bytes). -/
structure Geo where
  pageSize : Nat := 4096
  usable : Nat := 4096
  deriving Inhabited

namespace Geo
def maxLocal (g : Geo) : TreeKind → Nat
  | .table => g.usable - 35
  | .index => (g.usable - 12) * 64 / 255 - 23
def minLocal (g : Geo) : Nat := (g.usable - 12) * 32 / 255 - 23
/-- Bytes of a payload of `p` bytes kept on the b-tree page (btree.c btreeParseCellAdjustSizeForOverflow). -/
def localSize (g : Geo) (k : TreeKind) (p : Nat) : Nat :=
  let mx := g.maxLocal k
  if p ≤ mx then p else
  let mn := g.minLocal
  let kk := mn + (p - mn) % (g.usable - 4)
  if kk ≤ mx then kk else mn
/-- Overflow pages a payload of `p` bytes needs. -/
def ovflPages (g : Geo) (k : TreeKind) (p : Nat) : Nat :=
  let l := g.localSize k p
  if p ≤ l then 0 else (p - l + g.usable - 5) / (g.usable - 4)
/-- Bytes of cell content available on page `pg` for a node with `hdr` header bytes. -/
def room (g : Geo) (pg : Pgno) (leaf : Bool) : Nat :=
  g.usable - (if pg == 1 then 100 else 0) - (if leaf then 8 else 12)
end Geo

/-- On-page bytes of a payload cell part (size varint, local bytes, overflow pointer). -/
@[inline] def payloadCellSize (g : Geo) (k : TreeKind) (p : Nat) : Nat :=
  let l := g.localSize k p
  varintLen p.toUInt64 + l + (if p > l then 4 else 0)

/-- Bytes a cell takes on its page, cell pointer included (cells under 4 bytes are padded to 4, as sqlite allocates them). -/
@[inline] def tleafCellSize (_g : Geo) (_rowid : Int64) (c : Cell) : Nat := c.size + 2
@[inline] def tinnerCellSize (key : Int64) : Nat := 4 + varintLen key.toUInt64 + 2
@[inline] def ileafCellSize (_g : Geo) (c : Cell) : Nat := c.size + 2
/-- The bytes leaf cells take on their page, cell pointers included. -/
def leafUsed (cells : Array Cell) : Nat := cells.foldl (fun n c => n + c.size + 2) 0
/-- (an over-estimate by at most 3 bytes for a cell under 4 bytes: it only leaves room unused) -/
@[inline] def iinnerCellSize (_g : Geo) (c : Cell) : Nat := 4 + c.size + 2

/-- A leaf cell's on-page bytes: a table cell's rowid varint (`extra`) and payload part, at least 4. -/
@[inline] def leafCellBytes (g : Geo) (k : TreeKind) (payloadSize extra : Nat) : Nat :=
  max 4 (payloadCellSize g k payloadSize + extra)

/-- Journal flags of a page: bit 0 saved in the transaction journal, bit 1 in the statement journal. -/
abbrev Flags := UInt8

/-- What a journal restores besides pages: the page counts and freelists. `journal`: whether pages changed below
`npages` are saved (off for a statement that cannot fail once it writes, and for autocommit's transaction). -/
structure Mark where
  npages : Nat
  free : Array Pgno
  journal : Bool := true
  tnpages : Nat := 0
  tfree : Array Pgno := #[]
  deriving Inhabited

/-- TEMP objects' pages: a second page space, in memory only, page numbers with the high bit set. -/
def tempBit : Pgno := 0x80000000
@[inline] def isTempPg (n : Pgno) : Bool := n ≥ tempBit
/-- A page's index in its space. -/
@[inline] def slotOf (n : Pgno) : Nat := (if isTempPg n then n - tempBit else n).toNat - 1
/-- The temp schema's root (sqlite_temp_schema). -/
def tempRoot : Pgno := tempBit + 1

structure Pager where
  geo : Geo := {}
  /-- page `n` at index `n - 1` -/
  pages : Array Page := #[.table (.tleaf #[] #[] 0)]
  free : Array Pgno := #[]
  /-- the 100-byte database header as last written (fields set at commit) -/
  hdr : ByteArray := ByteArray.empty
  flags : Array Flags := #[0]
  /-- the temp space: pages, freelist, journal flags (never written to the file) -/
  tpages : Array Page := #[]
  tfree : Array Pgno := #[]
  tflags : Array Flags := #[]
  /-- pages before their first change in the open transaction / statement -/
  txnLog : Array (Pgno × Page) := #[]
  stmtLog : Array (Pgno × Page) := #[]
  txnMark : Mark := ⟨1, #[], true, 0, #[]⟩
  stmtMark : Mark := ⟨1, #[], true, 0, #[]⟩
  /-- the encoded bytes of each page as last written (empty: not written yet) and whether it changed since -/
  enc : Array ByteArray := #[]
  dirty : Array Bool := #[true]
  /-- the schema cookie (header offset 40), the user version (60) -/
  schemaCookie : UInt32 := 0
  userVersion : UInt32 := 0
  changeCounter : UInt32 := 0
  deriving Inhabited

/-- A pager value with nothing in it, left in a field while the real one is out being changed (a closed constant). -/
def Pager.placeholder : Pager := {}

namespace Pager

@[inline] def get (p : Pager) (n : Pgno) : Page :=
  if isTempPg n then p.tpages.getD (slotOf n) .free else p.pages.getD (n.toNat - 1) .free

def npages (p : Pager) : Nat := p.pages.size
/-- Both spaces' pages: a bound for loops over the trees. -/
def totalPages (p : Pager) : Nat := p.pages.size + p.tpages.size

def mark (p : Pager) (journal : Bool) : Mark :=
  { npages := p.pages.size, free := p.free, journal, tnpages := p.tpages.size, tfree := p.tfree }

@[inline] def flagOf (p : Pager) (n : Pgno) : Flags :=
  if isTempPg n then p.tflags.getD (slotOf n) 0 else p.flags.getD (slotOf n) 0
@[inline] def setFlag (p : Pager) (n : Pgno) (f : Flags) : Pager :=
  if isTempPg n then { p with tflags := p.tflags.setIfInBounds (slotOf n) f }
  else { p with flags := p.flags.setIfInBounds (slotOf n) f }

/-- Saves page `n` in the journals that do not have it yet (its first change in the transaction / statement). -/
def journal (p : Pager) (n : Pgno) (old : Page) : Pager :=
  let i := slotOf n
  let f := p.flagOf n
  let below (m : Mark) : Bool := if isTempPg n then i < m.tnpages else i < m.npages
  -- a page past a journal's mark is new since it began: the journal's rollback cuts it off, so it is not saved
  let toTxn := f &&& 1 == 0 && p.txnMark.journal && below p.txnMark
  let toStmt := f &&& 2 == 0 && p.stmtMark.journal && below p.stmtMark
  let p := if toTxn then { p with txnLog := p.txnLog.push (n, old) } else p
  let p := if toStmt then { p with stmtLog := p.stmtLog.push (n, old) } else p
  -- the flags mark exactly the pages the journals hold, so clearing a journal's pages clears them all
  let p := if toTxn || toStmt then p.setFlag n (f ||| (if toTxn then 1 else 0) ||| (if toStmt then 2 else 0)) else p
  if isTempPg n || p.dirty.getD i false then p else { p with dirty := p.dirty.setIfInBounds i true }

/-- Takes page `n` out for a change (a placeholder stays until `put`), journaling it first. Taking it out leaves the
node with one reference, so its arrays update in place. -/
def take (p : Pager) (n : Pgno) : Page × Pager :=
  let old := p.get n
  let p := p.journal n old
  if isTempPg n then (old, { p with tpages := p.tpages.setIfInBounds (slotOf n) .free })
  else (old, { p with pages := p.pages.setIfInBounds (slotOf n) .free })

@[inline] def put (p : Pager) (n : Pgno) (pg : Page) : Pager :=
  if isTempPg n then { p with tpages := p.tpages.setIfInBounds (slotOf n) pg }
  else { p with pages := p.pages.setIfInBounds (n.toNat - 1) pg }

/-- A page for new content, in the space of page `near` (the tree being changed): the last freelist page, else a new
page at the end. -/
def alloc (p : Pager) (near : Pgno := 0) : Pgno × Pager :=
  if isTempPg near then
    match p.tfree.back? with
    | some n =>
      let (_, p) := p.take n
      (n, { p with tfree := p.tfree.pop })
    | none =>
      let n := tempBit + (p.tpages.size + 1).toUInt32
      (n, { p with tpages := p.tpages.push .free, tflags := p.tflags.push 0 })
  else
  match p.free.back? with
  | some n =>
    let (_, p) := p.take n
    (n, { p with free := p.free.pop })
  | none =>
    let n := (p.pages.size + 1).toUInt32
    (n, { p with pages := p.pages.push .free, flags := p.flags.push 0, dirty := p.dirty.push true })

/-- Puts page `n` on its space's freelist. -/
def release (p : Pager) (n : Pgno) : Pager :=
  if n == 0 then p else
  if isTempPg n then
    if slotOf n ≥ p.tpages.size then p else
    let (_, p) := p.take n
    { (p.put n .free) with tfree := p.tfree.push n }
  else
  if n.toNat > p.pages.size then p else
  let (_, p) := p.take n
  { (p.put n .free) with free := p.free.push n }

/-- Allocates the overflow pages of a payload of `size` bytes (in the space of page `near`). -/
def allocOvfl (p : Pager) (k : TreeKind) (payload : ByteArray) (extra : Nat := 0) (near : Pgno := 0) : Cell × Pager :=
  let n := p.geo.ovflPages k payload.size
  let (ps, p) := n.fold (fun _ _ (acc : Array Pgno × Pager) =>
    let (pg, p') := acc.2.alloc near
    (acc.1.push pg, p'.put pg .overflow)) (#[], p)
  ({ payload, ovfl := ps, size := leafCellBytes p.geo k payload.size extra }, p)

def releaseOvfl (p : Pager) (c : Cell) : Pager := c.ovfl.foldl release p

/-- The temp space, made on first use: its page 1 is sqlite_temp_schema's root. -/
def ensureTemp (p : Pager) : Pager :=
  if p.tpages.isEmpty then { p with tpages := #[.table (.tleaf #[] #[] 0)], tflags := #[0] } else p

/-! ## Journals -/

/-- Starts a statement: an empty statement journal. -/
def beginStmt (p : Pager) : Pager :=
  let p := p.stmtLog.foldl (fun p e => p.setFlag e.1 (p.flagOf e.1 &&& 1)) p
  { p with stmtLog := #[], stmtMark := p.mark true }

/-- The statement can no longer fail: the pages it changes from here on are not saved. -/
def noStmtJournal (p : Pager) : Pager := { p with stmtMark := { p.stmtMark with journal := false } }

def restore1 (p : Pager) (n : Pgno) (pg : Page) : Pager :=
  if isTempPg n then { p with tpages := p.tpages.setIfInBounds (slotOf n) pg }
  else { p with pages := p.pages.setIfInBounds (n.toNat - 1) pg, dirty := p.dirty.setIfInBounds (n.toNat - 1) true }

/-- Restores the pages a journal saved and the page counts and freelists of its mark. -/
def restore (p : Pager) (log : Array (Pgno × Page)) (m : Mark) : Pager :=
  let p := log.foldl (fun (p : Pager) (e : Pgno × Page) => p.restore1 e.1 e.2) p
  { p with pages := p.pages.extract 0 m.npages, flags := p.flags.extract 0 m.npages, dirty := p.dirty.extract 0 m.npages,
           free := m.free, tpages := p.tpages.extract 0 m.tnpages, tflags := p.tflags.extract 0 m.tnpages, tfree := m.tfree }

/-- Undoes the open statement's changes. -/
def rollbackStmt (p : Pager) : Pager :=
  let log := p.stmtLog
  let p := p.restore log p.stmtMark
  -- the transaction journal keeps its entries (a page first changed by this statement holds its start-of-transaction
  -- content there, which is what it is back to)
  let p := log.foldl (fun p e => p.setFlag e.1 (p.flagOf e.1 &&& 1)) p
  { p with stmtLog := #[] }

/-- Clears the journal flags of the pages a journal saved. -/
def clearFlags (p : Pager) (log : Array (Pgno × Page)) : Pager :=
  log.foldl (fun p e => p.setFlag e.1 0) p

/-- Starts a transaction. -/
def beginTxn (p : Pager) : Pager :=
  let p := p.clearFlags p.stmtLog
  let p := p.clearFlags p.txnLog
  { p with txnLog := #[], stmtLog := #[], txnMark := p.mark true, stmtMark := p.mark true }

/-- A statement outside a transaction: its statement journal is all it needs. -/
def beginAutocommit (p : Pager) : Pager :=
  let p := p.clearFlags p.stmtLog
  let p := p.clearFlags p.txnLog
  { p with txnLog := #[], stmtLog := #[], txnMark := p.mark false, stmtMark := p.mark true }

/-- Ends a transaction that is kept: its journals are dropped. -/
def endTxn (p : Pager) : Pager :=
  let p := p.clearFlags p.stmtLog
  let p := p.clearFlags p.txnLog
  { p with txnLog := #[], stmtLog := #[], txnMark := p.mark true, stmtMark := p.mark true }

/-- Undoes the open transaction's changes. -/
def rollbackTxn (p : Pager) : Pager :=
  let log := p.txnLog
  let p := p.restore log p.txnMark
  let p := p.clearFlags log
  let p := p.clearFlags p.stmtLog
  { p with txnLog := #[], stmtLog := #[] }

/-! ## Encoding pages -/

/-- The cell part for a payload: its size varint is the caller's; the local bytes, then the first overflow page. -/
def pushPayload (g : Geo) (k : TreeKind) (b : ByteArray) (c : Cell) : ByteArray :=
  let l := g.localSize k c.payload.size
  let b := b ++ c.payload.extract 0 l
  if c.payload.size > l then push32 b (c.ovfl.getD 0 0) else b

/-- The overflow pages of a cell: each the next page's number (0 on the last), then up to usable-4 payload bytes. -/
def ovflBytes (g : Geo) (k : TreeKind) (c : Cell) : Array (Pgno × ByteArray) :=
  let l := g.localSize k c.payload.size
  let per := g.usable - 4
  (c.ovfl.mapIdx fun i pg =>
    let start := l + i * per
    let chunk := c.payload.extract start (start + per)
    let b := push32 (ByteArray.emptyWithCapacity g.pageSize) (c.ovfl.getD (i+1) 0) ++ chunk
    (pg, pushZeros b (g.pageSize - b.size)))

/-- The bytes of a b-tree page: header, cell pointers, free gap, then the cells packed at the end of the usable area. -/
def encodeCells (g : Geo) (pg : Pgno) (flag : UInt8) (right : Option Pgno) (cells : Array ByteArray) : ByteArray :=
  let h0 := if pg == 1 then 100 else 0
  let hdrLen := if right.isSome then 12 else 8
  let padded := cells.map fun c => if c.size < 4 then pushZeros c (4 - c.size) else c
  let total := padded.foldl (fun n c => n + c.size) 0
  let start := g.usable - total
  let b := pushZeros (ByteArray.emptyWithCapacity g.pageSize) h0
  let b := b.push flag
  let b := push16 b 0
  let b := push16 b padded.size
  let b := push16 b (if start == 65536 then 0 else start)
  let b := b.push 0
  let b := match right with | some r => push32 b r | none => b
  -- cell i at the end of the area: cell 0 last
  let (b, _) := padded.foldl (fun (b, off) c => (push16 b (off - c.size), off - c.size)) (b, g.usable)
  let b := pushZeros b (start - (h0 + hdrLen + 2 * padded.size))
  let b := padded.foldr (fun c b => b ++ c) b
  pushZeros b (g.pageSize - b.size)

/-- A page's bytes and the overflow pages its cells own. -/
def encodePage (g : Geo) (pg : Pgno) : Page → ByteArray × Array (Pgno × ByteArray)
  | .table (.tleaf keys cells _) =>
    let cs := cells.mapIdx fun i c =>
      let b := putVarint ByteArray.empty c.payload.size.toUInt64
      let b := putVarint b (keys.getD i 0).toUInt64
      pushPayload g .table b c
    (encodeCells g pg 13 none cs, cells.foldl (fun a c => a ++ ovflBytes g .table c) #[])
  | .table (.tinner keys kids) =>
    let cs := keys.mapIdx fun i k => putVarint (push32 ByteArray.empty (kids.getD i 0)) k.toUInt64
    (encodeCells g pg 5 (some (kids.back?.getD 0)) cs, #[])
  | .index (.ileaf cells _) =>
    let cs := cells.map fun c => pushPayload g .index (putVarint ByteArray.empty c.payload.size.toUInt64) c
    (encodeCells g pg 10 none cs, cells.foldl (fun a c => a ++ ovflBytes g .index c) #[])
  | .index (.iinner cells kids) =>
    let cs := cells.mapIdx fun i c =>
      pushPayload g .index (putVarint (push32 ByteArray.empty (kids.getD i 0)) c.payload.size.toUInt64) c
    (encodeCells g pg 2 (some (kids.back?.getD 0)) cs, cells.foldl (fun a c => a ++ ovflBytes g .index c) #[])
  | .raw b => (b, #[])
  | .overflow | .free => (pushZeros (ByteArray.emptyWithCapacity g.pageSize) g.pageSize, #[])

/-- The freelist as trunk pages: each the next trunk's number, a count, then that many leaf page numbers. -/
def freelistPages (g : Geo) (free : Array Pgno) : Array (Pgno × ByteArray) :=
  let per := g.usable / 4 - 2
  let groups := (List.range ((free.size + per) / (per + 1))).toArray.map fun t =>
    free.extract (t * (per + 1)) ((t + 1) * (per + 1))
  groups.mapIdx fun t grp =>
    let next := (groups.getD (t+1) #[]).getD 0 0
    let leaves := grp.extract 1 grp.size
    let b := push32 (push32 (ByteArray.emptyWithCapacity g.pageSize) next) leaves.size.toUInt32
    let b := leaves.foldl push32 b
    (grp.getD 0 0, pushZeros b (g.pageSize - b.size))

def sqliteVersionNumber : UInt32 := 3054000

/-- The 100-byte header (fileformat2.html §1.3) for the pager's state. -/
def header (p : Pager) (trunk : Pgno) : ByteArray :=
  let g := p.geo
  let b := "SQLite format 3".toUTF8.push 0
  let b := push16 b (if g.pageSize == 65536 then 1 else g.pageSize)
  let b := (((((b.push 1).push 1).push (g.pageSize - g.usable).toUInt8).push 64).push 32).push 32
  let b := push32 b p.changeCounter
  let b := push32 b p.pages.size.toUInt32
  let b := push32 b trunk
  let b := push32 b p.free.size.toUInt32
  let b := push32 b p.schemaCookie
  let b := push32 b 4            -- schema format
  let b := push32 b 0            -- default cache size
  let b := push32 b 0            -- largest root page (no autovacuum)
  let b := push32 b 1            -- UTF-8
  let b := push32 b p.userVersion
  let b := push32 b 0            -- incremental vacuum
  let b := push32 b (rd32 p.hdr 68) -- application id, as read
  let b := pushZeros b 20
  let b := push32 b p.changeCounter -- version-valid-for
  push32 b sqliteVersionNumber

/-- The whole database file after a commit, and the pager with its encoded pages cached. -/
def encodeFile (p : Pager) : ByteArray × Pager :=
  let g := p.geo
  let p := { p with changeCounter := p.changeCounter + 1 }
  let enc0 := if p.enc.size < p.pages.size then p.enc ++ Array.replicate (p.pages.size - p.enc.size) ByteArray.empty
    else p.enc.extract 0 p.pages.size
  -- re-encode changed b-tree pages (and their overflow pages)
  let enc := (List.range p.pages.size).foldl (fun enc i =>
    if p.dirty.getD i true || (enc.getD i ByteArray.empty).size != g.pageSize then
      match p.pages.getD i .free with
      | pg@(.table _) | pg@(.index _) | pg@(.raw _) =>
        let (b, ov) := encodePage g (i + 1).toUInt32 pg
        let enc := enc.setIfInBounds i b
        ov.foldl (fun enc (n, ob) => enc.setIfInBounds (n.toNat - 1) ob) enc
      | .overflow => enc
      | .free => enc.setIfInBounds i (pushZeros (ByteArray.emptyWithCapacity g.pageSize) g.pageSize)
    else enc) enc0
  let fl := freelistPages g p.free
  let enc := fl.foldl (fun enc (n, b) => enc.setIfInBounds (n.toNat - 1) b) enc
  let hdr := p.header ((fl.getD 0 (0, ByteArray.empty)).1)
  let page1 := enc.getD 0 ByteArray.empty
  let enc := enc.setIfInBounds 0 (hdr ++ page1.extract 100 page1.size)
  let file := enc.foldl (· ++ ·) (ByteArray.emptyWithCapacity (g.pageSize * enc.size))
  (file, { p with enc, hdr, dirty := p.dirty.map fun _ => false })

/-! ## Decoding a file -/

/-- The cells of a b-tree page: for each, its left child (interior), payload size, rowid, and the offset of its payload. -/
structure RawCell where
  child : Pgno
  key : Int64
  payload : Cell

/-- Reads a payload of `size` bytes whose local part starts at `o`: its overflow chain followed for the rest. -/
def readPayload (g : Geo) (file : ByteArray) (pageOff : Nat) (k : TreeKind) (o size : Nat) (extra : Nat := 0) : Cell :=
  let l := g.localSize k size
  let loc := file.extract (pageOff + o) (pageOff + o + l)
  let cs := leafCellBytes g k size extra
  if size ≤ l then { payload := loc, size := cs } else
  let first := rd32 file (pageOff + o + l)
  chain cs loc first #[] (g.ovflPages k size + 1)
where
  chain (cs : Nat) (acc : ByteArray) (pg : Pgno) (ps : Array Pgno) : Nat → Cell
    | 0 => { payload := acc, ovfl := ps, size := cs }
    | fuel+1 =>
      if pg == 0 || acc.size ≥ size then { payload := acc.extract 0 size, ovfl := ps, size := cs } else
      let off := (pg.toNat - 1) * g.pageSize
      let take := min (g.usable - 4) (size - acc.size)
      chain cs (acc ++ file.extract (off + 4) (off + 4 + take)) (rd32 file off) (ps.push pg) fuel

/-- Decodes the b-tree page `pg` of `file`. -/
def decodePage (g : Geo) (file : ByteArray) (pg : Pgno) : Option Page :=
  let off := (pg.toNat - 1) * g.pageSize
  let h := off + (if pg == 1 then 100 else 0)
  let flag := rd file h
  let n := rd16 file (h + 3)
  let leaf := flag == 13 || flag == 10
  let ptrs := h + (if leaf then 8 else 12)
  let right := rd32 file (h + 8)
  let cellOff (i : Nat) : Nat := rd16 file (ptrs + 2 * i)
  match flag with
  | 13 =>
    let (keys, cells) := (List.range n).foldl (fun (ks, cs) i =>
      let o := cellOff i
      let (size, a) := getVarint file (off + o)
      let (rowid, b) := getVarint file (off + o + a)
      (ks.push rowid.toInt64, cs.push (readPayload g file off .table (o + a + b) size.toNat b))) (#[], #[])
    some (.table (.tleaf keys cells (leafUsed cells)))
  | 5 =>
    let (keys, kids) := (List.range n).foldl (fun (ks, kd) i =>
      let o := cellOff i
      let child := rd32 file (off + o)
      let (key, _) := getVarint file (off + o + 4)
      (ks.push key.toInt64, kd.push child)) (#[], #[])
    some (.table (.tinner keys (kids.push right)))
  | 10 =>
    let cells := (List.range n).toArray.map fun i =>
      let o := cellOff i
      let (size, a) := getVarint file (off + o)
      readPayload g file off .index (o + a) size.toNat
    some (.index (.ileaf cells (leafUsed cells)))
  | 2 =>
    let (cells, kids) := (List.range n).foldl (fun (cs, kd) i =>
      let o := cellOff i
      let child := rd32 file (off + o)
      let (size, a) := getVarint file (off + o + 4)
      (cs.push (readPayload g file off .index (o + 4 + a) size.toNat), kd.push child)) (#[], #[])
    some (.index (.iinner cells (kids.push right)))
  | _ => none

/-- The child pages of a decoded page, and the overflow pages of its cells. -/
def links : Page → Array Pgno × Array Pgno
  | .table (.tleaf _ cells _) => (#[], cells.foldl (fun a c => a ++ c.ovfl) #[])
  | .table (.tinner _ kids) => (kids, #[])
  | .index (.ileaf cells _) => (#[], cells.foldl (fun a c => a ++ c.ovfl) #[])
  | .index (.iinner cells kids) => (kids, cells.foldl (fun a c => a ++ c.ovfl) #[])
  | _ => (#[], #[])

/-- Decodes the tree at `root` into `pages`. -/
def loadTree (g : Geo) (file : ByteArray) (pages : Array Page) (root : Pgno) (fuel : Nat) : Array Page :=
  match fuel with
  | 0 => pages
  | fuel+1 =>
    match decodePage g file root with
    | none => pages
    | some pg =>
      let pages := pages.setIfInBounds (root.toNat - 1) pg
      let (kids, ovfl) := links pg
      let pages := ovfl.foldl (fun ps n => ps.setIfInBounds (n.toNat - 1) .overflow) pages
      kids.foldl (fun ps k => loadTree g file ps k fuel) pages

/-- The freelist's pages (trunks and leaves), from the header's first trunk. -/
def readFreelist (g : Geo) (file : ByteArray) (trunk : Pgno) (fuel : Nat) : Array Pgno :=
  match fuel with
  | 0 => #[]
  | fuel+1 =>
    if trunk == 0 then #[] else
    let off := (trunk.toNat - 1) * g.pageSize
    let n := (rd32 file (off + 4)).toNat
    let leaves := (List.range n).toArray.map fun i => rd32 file (off + 8 + 4 * i)
    #[trunk] ++ leaves ++ readFreelist g file (rd32 file off) fuel

/-- A pager over an existing file's bytes; `roots` are read from sqlite_schema afterwards by `loadRoots`. -/
def ofFile (file : ByteArray) : Except String Pager :=
  if file.size == 0 then .ok {} else
  if file.size < 100 || file.extract 0 16 != "SQLite format 3".toUTF8.push 0 then .error "file is not a database" else
  let ps := rd16 file 16
  let pageSize := if ps == 1 then 65536 else ps
  if pageSize < 512 || pageSize > 65536 then .error "file is not a database" else
  if (rd32 file 52) != 0 then .error "lean-sqlite: auto-vacuum databases are not supported" else
  if (rd32 file 56) > 1 then .error "lean-sqlite: only UTF-8 databases are supported" else
  let g : Geo := { pageSize, usable := pageSize - (rd file 20).toNat }
  let n := file.size / pageSize
  let pages := Array.replicate n (Page.raw ByteArray.empty) |>.mapIdx fun i _ =>
    Page.raw (file.extract (i * pageSize) ((i + 1) * pageSize))
  let pages := loadTree g file pages 1 (n + 1)
  let free := readFreelist g file (rd32 file 32) (n + 1)
  let pages := free.foldl (fun ps f => ps.setIfInBounds (f.toNat - 1) .free) pages
  .ok { geo := g, pages, free, hdr := file.extract 0 100, flags := Array.replicate n 0,
        txnMark := ⟨n, free, true, 0, #[]⟩, stmtMark := ⟨n, free, true, 0, #[]⟩,
        enc := (List.range n).toArray.map (fun i => file.extract (i * pageSize) ((i + 1) * pageSize)),
        dirty := Array.replicate n false,
        schemaCookie := rd32 file 40, userVersion := rd32 file 60, changeCounter := rd32 file 24 }

/-- Decodes the trees rooted at `roots` (read from sqlite_schema), leaving the pages already decoded as they are. -/
def loadRoots (p : Pager) (roots : Array Pgno) : Pager :=
  let file := p.enc.foldl (· ++ ·) ByteArray.empty
  let pages := roots.foldl (fun ps r => loadTree p.geo file ps r (p.pages.size + 1)) p.pages
  { p with pages }

end Pager
end LSql
