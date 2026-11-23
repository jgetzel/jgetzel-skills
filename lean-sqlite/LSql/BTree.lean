import LSql.Pager
import LSql.Compare
/-! B-trees over the pager (btree.c's role): insert with page splits, delete, clear, and cursors. Every recursion is bounded
by `maxDepth` (a tree deeper than any valid one, 64, reads as corrupt) or by the page count. -/
namespace LSql
namespace BTree

def maxDepth : Nat := 64

/-! ## Searching a node -/

/-- The first `i` with `keys[i] ≥ k` (keys sorted). -/
def lowerBound (keys : Array Int64) (k : Int64) : Nat := go 0 keys.size 64
where
  go (lo hi : Nat) : Nat → Nat
    | 0 => lo
    | f+1 =>
      if lo ≥ hi then lo else
      let mid := (lo + hi) / 2
      if keys.getD mid 0 < k then go (mid+1) hi f else go lo mid f

/-- The first `i` with `cells[i] ≥ key` under the index's order. -/
def lowerBoundRec (ki : KeyInfo) (cells : Array Cell) (key : ByteArray) : Nat := go 0 cells.size 64
where
  go (lo hi : Nat) : Nat → Nat
    | 0 => lo
    | f+1 =>
      if lo ≥ hi then lo else
      let mid := (lo + hi) / 2
      if cmpRecords ki (cells.getD mid default).payload key == .lt then go (mid+1) hi f else go lo mid f

/-! ## Splitting an over-full node

`sizes` are the cells' on-page sizes (pointer included); `cap0` is the room on the page that keeps the first group (page 1
has less), `cap` the room on a new page. -/

def prefixSums (sizes : Array Nat) : Array Nat := sizes.foldl (fun ps s => ps.push (ps.back?.getD 0 + s)) #[0]

/-- Group starts for a leaf split (all cells stay in leaves): the new last cell alone when appending (sqlite's
balance_quick), else the most even two-way split that fits, else greedy packing. -/
def leafSplit (sizes : Array Nat) (cap0 cap : Nat) (append : Bool) : Array Nat :=
  let n := sizes.size
  let ps := prefixSums sizes
  let seg (a b : Nat) : Nat := ps.getD b 0 - ps.getD a 0
  if append && n ≥ 2 && seg 0 (n-1) ≤ cap0 && seg (n-1) n ≤ cap then #[0, n-1] else
  let best := (List.range n).foldl (fun (best : Option (Nat × Nat)) m =>
    if m == 0 then best else
    let l := seg 0 m
    let r := seg m n
    if l ≤ cap0 && r ≤ cap then
      let w := max l r
      match best with
      | some (_, bw) => if w < bw then some (m, w) else best
      | none => some (m, w)
    else best) none
  match best with
  | some (m, _) => #[0, m]
  | none =>
    let (starts, _) := (List.range n).foldl (fun (starts, acc) i =>
      let s := sizes.getD i 0
      let c := if starts.size == 1 then cap0 else cap
      if acc + s > c && acc > 0 then (starts.push i, s) else (starts, acc + s)) (#[0], 0)
    starts

/-- Separators for a split whose separator cells move up to the parent (interior nodes, index leaves): groups
`[0, s₁)`, `(s₁, s₂)`, ...; the most even single separator that fits, else greedy. -/
def upSplit (sizes : Array Nat) (cap0 cap : Nat) : Array Nat :=
  let n := sizes.size
  let ps := prefixSums sizes
  let seg (a b : Nat) : Nat := ps.getD b 0 - ps.getD a 0
  let best := (List.range n).foldl (fun (best : Option (Nat × Nat)) m =>
    let l := seg 0 m
    let r := seg (m+1) n
    if l ≤ cap0 && r ≤ cap then
      let w := max l r
      match best with
      | some (_, bw) => if w < bw then some (m, w) else best
      | none => some (m, w)
    else best) none
  match best with
  | some (m, _) => #[m]
  | none =>
    let (seps, _, _) := (List.range n).foldl (fun (seps, acc, skip) i =>
      if skip then (seps, 0, false) else
      let s := sizes.getD i 0
      let c := if seps.isEmpty then cap0 else cap
      if acc + s > c then (seps.push i, 0, false) else (seps, acc + s, false)) (#[], 0, false)
    seps

/-- `xs[a, b)` -/
@[inline] def slice (xs : Array α) (a b : Nat) : Array α := xs.extract a b

/-- Inserts `ys` into `xs` at `i` (in place for one element). -/
def insertMany (xs : Array α) (i : Nat) (ys : Array α) : Array α :=
  if h : ys.size = 1 then xs.insertIdxIfInBounds i ys[0] else xs.extract 0 i ++ ys ++ xs.extract i xs.size

/-! ## Fitting nodes back onto pages

Each returns the pager with the node written to `pg` (and its split-off siblings to new pages) and, for the parent, the
separator and page of each new sibling, in order. -/

abbrev TSplits := Array (Int64 × Pgno)
abbrev ISplits := Array (Cell × Pgno)

def fitTableLeaf (p : Pager) (pg : Pgno) (keys : Array Int64) (cells : Array Cell) (append : Bool) : Pager × TSplits :=
  let g := p.geo
  let total := cells.foldl (fun n c => n + c.size + 2) 0
  if total ≤ g.room pg true then (p.put pg (.table (.tleaf keys cells)), #[]) else
  let sizes := (List.range keys.size).toArray.map fun i => tleafCellSize g (keys.getD i 0) (cells.getD i default)
  let starts := leafSplit sizes (g.room pg true) (g.room 0 true) append
  let ends := (starts.extract 1 starts.size).push keys.size
  let p := p.put pg (.table (.tleaf (slice keys 0 (ends.getD 0 0)) (slice cells 0 (ends.getD 0 0))))
  (List.range (starts.size - 1)).foldl (fun (p, sp) j =>
    let a := starts.getD (j+1) 0
    let b := ends.getD (j+1) 0
    let (np, p) := p.alloc pg
    (p.put np (.table (.tleaf (slice keys a b) (slice cells a b))), sp.push (keys.getD (a - 1) 0, np))) (p, #[])

def fitTableInner (p : Pager) (pg : Pgno) (keys : Array Int64) (kids : Array Pgno) : Pager × TSplits :=
  let g := p.geo
  let total := keys.foldl (fun n k => n + tinnerCellSize k) 0
  if total ≤ g.room pg false then (p.put pg (.table (.tinner keys kids)), #[]) else
  let seps := upSplit (keys.map tinnerCellSize) (g.room pg false) (g.room 0 false)
  let s0 := seps.getD 0 keys.size
  let p := p.put pg (.table (.tinner (slice keys 0 s0) (slice kids 0 (s0 + 1))))
  (List.range seps.size).foldl (fun (p, sp) j =>
    let s := seps.getD j 0
    let e := seps.getD (j+1) keys.size
    let (np, p) := p.alloc pg
    (p.put np (.table (.tinner (slice keys (s+1) e) (slice kids (s+1) (e+1)))), sp.push (keys.getD s 0, np))) (p, #[])

def fitIndexLeaf (p : Pager) (pg : Pgno) (cells : Array Cell) : Pager × ISplits :=
  let g := p.geo
  let total := cells.foldl (fun n c => n + ileafCellSize g c) 0
  if total ≤ g.room pg true then (p.put pg (.index (.ileaf cells)), #[]) else
  let seps := upSplit (cells.map (ileafCellSize g)) (g.room pg true) (g.room 0 true)
  let s0 := seps.getD 0 cells.size
  let p := p.put pg (.index (.ileaf (slice cells 0 s0)))
  (List.range seps.size).foldl (fun (p, sp) j =>
    let s := seps.getD j 0
    let e := seps.getD (j+1) cells.size
    let (np, p) := p.alloc pg
    (p.put np (.index (.ileaf (slice cells (s+1) e))), sp.push (cells.getD s default, np))) (p, #[])

def fitIndexInner (p : Pager) (pg : Pgno) (cells : Array Cell) (kids : Array Pgno) : Pager × ISplits :=
  let g := p.geo
  let total := cells.foldl (fun n c => n + iinnerCellSize g c) 0
  if total ≤ g.room pg false then (p.put pg (.index (.iinner cells kids)), #[]) else
  let seps := upSplit (cells.map (iinnerCellSize g)) (g.room pg false) (g.room 0 false)
  let s0 := seps.getD 0 cells.size
  let p := p.put pg (.index (.iinner (slice cells 0 s0) (slice kids 0 (s0 + 1))))
  (List.range seps.size).foldl (fun (p, sp) j =>
    let s := seps.getD j 0
    let e := seps.getD (j+1) cells.size
    let (np, p) := p.alloc pg
    (p.put np (.index (.iinner (slice cells (s+1) e) (slice kids (s+1) (e+1)))), sp.push (cells.getD s default, np))) (p, #[])

/-- A root that split: its content moves to a new page and the root becomes the interior node over it and its siblings
(the root keeps its page number, which sqlite_schema records). -/
def growTableRoot (p : Pager) (root : Pgno) (sp : TSplits) : Pager :=
  if sp.isEmpty then p else
  let (old, p) := p.take root
  let (l, p) := p.alloc root
  let p := p.put l old
  (fitTableInner p root (sp.map (·.1)) (#[l] ++ sp.map (·.2))).1

def growIndexRoot (p : Pager) (root : Pgno) (sp : ISplits) : Pager :=
  if sp.isEmpty then p else
  let (old, p) := p.take root
  let (l, p) := p.alloc root
  let p := p.put l old
  (fitIndexInner p root (sp.map (·.1)) (#[l] ++ sp.map (·.2))).1

/-! ## Table trees -/

def tInsert (pg : Pgno) (rowid : Int64) (payload : ByteArray) : Nat → Pager → Pager × TSplits
  | 0, p => (p, #[])
  | fuel+1, p =>
    let (page, p) := p.take pg
    match page with
    | .table (.tleaf keys cells) =>
      let i := lowerBound keys rowid
      let (cell, p) := p.allocOvfl .table payload (varintLen rowid.toUInt64) pg
      if i < keys.size && keys.getD i 0 == rowid then
        let p := p.releaseOvfl (cells.getD i default)
        fitTableLeaf p pg keys (cells.setIfInBounds i cell) false
      else
        fitTableLeaf p pg (keys.insertIdxIfInBounds i rowid) (cells.insertIdxIfInBounds i cell) (i == keys.size)
    | .table (.tinner keys kids) =>
      let i := lowerBound keys rowid
      let (p, sp) := tInsert (kids.getD i 0) rowid payload fuel p
      if sp.isEmpty then (p.put pg (.table (.tinner keys kids)), #[])
      else fitTableInner p pg (insertMany keys i (sp.map (·.1))) (insertMany kids (i+1) (sp.map (·.2)))
    | other => (p.put pg other, #[])

/-- Inserts (or replaces) the row `rowid` in the table tree at `root`. -/
def tableInsert (p : Pager) (root : Pgno) (rowid : Int64) (payload : ByteArray) : Pager :=
  let (p, sp) := tInsert root rowid payload maxDepth p
  growTableRoot p root sp

/-- The row `rowid` of the table tree at `root`. -/
def tableFind (p : Pager) (root : Pgno) (rowid : Int64) : Option Cell := go root maxDepth
where
  go (pg : Pgno) : Nat → Option Cell
    | 0 => none
    | fuel+1 =>
      match p.get pg with
      | .table (.tleaf keys cells) =>
        let i := lowerBound keys rowid
        if i < keys.size && keys.getD i 0 == rowid then cells[i]? else none
      | .table (.tinner keys kids) => go (kids.getD (lowerBound keys rowid) 0) fuel
      | _ => none

/-- Whether the page holds no cells (an empty leaf, or an interior page with only its right child). -/
def isUnderfull : Page → Bool
  | .table (.tleaf keys _) => keys.isEmpty
  | .table (.tinner keys _) => keys.isEmpty
  | .index (.ileaf cells) => cells.isEmpty
  | .index (.iinner cells _) => cells.isEmpty
  | _ => false

/-- An interior table node's child `i` has no cells (sqlite reads an empty non-root page as corrupt): merges it with a
sibling, through their separator, onto the left page; the merged node splits again if it does not fit. Returns the node's
keys and kids. -/
def fixTableChild (p : Pager) (keys : Array Int64) (kids : Array Pgno) (i : Nat) : Pager × Array Int64 × Array Pgno :=
  if kids.size < 2 || !isUnderfull (p.get (kids.getD i 0)) then (p, keys, kids) else
  let l := if i > 0 then i - 1 else 0
  let lp := kids.getD l 0
  let rp := kids.getD (l+1) 0
  let sep := keys.getD l 0
  let (lpage, p) := p.take lp
  let (rpage, p) := p.take rp
  let keys := keys.eraseIdxIfInBounds l
  let kids := kids.eraseIdxIfInBounds (l+1)
  match lpage, rpage with
  | .table (.tleaf k1 c1), .table (.tleaf k2 c2) =>
    let p := p.release rp
    let (p, sp) := fitTableLeaf p lp (k1 ++ k2) (c1 ++ c2) false
    (p, insertMany keys l (sp.map (·.1)), insertMany kids (l+1) (sp.map (·.2)))
  | .table (.tinner k1 d1), .table (.tinner k2 d2) =>
    let p := p.release rp
    let (p, sp) := fitTableInner p lp (k1.push sep ++ k2) (d1 ++ d2)
    (p, insertMany keys l (sp.map (·.1)), insertMany kids (l+1) (sp.map (·.2)))
  | a, b => (p.put lp a |>.put rp b, keys.insertIdxIfInBounds l sep, kids.insertIdxIfInBounds (l+1) rp)

def tDelete (pg : Pgno) (rowid : Int64) : Nat → Pager → Pager × TSplits × Bool
  | 0, p => (p, #[], false)
  | fuel+1, p =>
    match p.get pg with
    | .table (.tleaf keys _) =>
      let i := lowerBound keys rowid
      if i < keys.size && keys.getD i 0 == rowid then
        let (page, p) := p.take pg
        match page with
        | .table (.tleaf keys cells) =>
          let p := p.releaseOvfl (cells.getD i default)
          let keys := keys.eraseIdxIfInBounds i
          (p.put pg (.table (.tleaf keys (cells.eraseIdxIfInBounds i))), #[], keys.isEmpty)
        | other => (p.put pg other, #[], false)
      else (p, #[], false)
    | .table (.tinner keys _) =>
      let i := lowerBound keys rowid
      match p.get pg with
      | .table (.tinner _ kids) =>
        let (p, sp, uf) := tDelete (kids.getD i 0) rowid fuel p
        if sp.isEmpty && !uf then (p, #[], false) else
        let (_, p) := p.take pg
        let keys := insertMany keys i (sp.map (·.1))
        let kids := insertMany kids (i+1) (sp.map (·.2))
        let (p, keys, kids) := if uf then fixTableChild p keys kids i else (p, keys, kids)
        let (p, sp) := fitTableInner p pg keys kids
        (p, sp, keys.isEmpty && sp.isEmpty)
      | _ => (p, #[], false)
    | _ => (p, #[], false)

/-- Whether a node fits on page `pg`. -/
def fits (g : Geo) (pg : Pgno) : Page → Bool
  | .table (.tleaf keys cells) =>
    cells.foldl (fun n c => n + c.size + 2) 0 ≤ g.room pg true
  | .table (.tinner keys _) => keys.foldl (fun n k => n + tinnerCellSize k) 0 ≤ g.room pg false
  | .index (.ileaf cells) => cells.foldl (fun n c => n + ileafCellSize g c) 0 ≤ g.room pg true
  | .index (.iinner cells _) => cells.foldl (fun n c => n + iinnerCellSize g c) 0 ≤ g.room pg false
  | _ => true

/-- A root with no cells over a single child takes the child's content (sqlite's balance_shallower), when it fits (page 1
has less room: it may stay an empty interior page, which sqlite allows for page 1 only). -/
def collapseRoot (p : Pager) (root : Pgno) : Nat → Pager
  | 0 => p
  | fuel+1 =>
    match p.get root with
    | .table (.tinner keys kids) | .index (.iinner keys kids) =>
      if keys.isEmpty then
        let k := kids.getD 0 0
        let child := p.get k
        if k == 0 || !fits p.geo root child then p else
        let (_, p) := p.take root
        let (_, p) := p.take k
        let p := p.put root child
        collapseRoot (p.release k) root fuel
      else p
    | _ => p

/-- Deletes the row `rowid` (nothing if there is none). -/
def tableDelete (p : Pager) (root : Pgno) (rowid : Int64) : Pager :=
  let (p, sp, _) := tDelete root rowid maxDepth p
  collapseRoot (growTableRoot p root sp) root maxDepth
/-- The largest rowid in the tree. -/
def tableMaxKey (p : Pager) (root : Pgno) : Option Int64 := go root maxDepth
where
  go (pg : Pgno) : Nat → Option Int64
    | 0 => none
    | fuel+1 =>
      match p.get pg with
      | .table (.tleaf keys _) => keys.back?
      | .table (.tinner _ kids) => fromRight kids kids.size fuel
      | _ => none
  /-- the last child (from index `i` down) whose subtree has a row -/
  fromRight (kids : Array Pgno) : Nat → Nat → Option Int64
    | 0, _ => none
    | i+1, fuel => match go (kids.getD i 0) fuel with
      | some k => some k
      | none => fromRight kids i fuel

/-! ## Index trees -/

def iInsert (ki : KeyInfo) (pg : Pgno) (key : ByteArray) : Nat → Pager → Pager × ISplits
  | 0, p => (p, #[])
  | fuel+1, p =>
    let (page, p) := p.take pg
    match page with
    | .index (.ileaf cells) =>
      let i := lowerBoundRec ki cells key
      if i < cells.size && cmpRecords ki (cells.getD i default).payload key == .eq then
        (p.put pg (.index (.ileaf cells)), #[])
      else
        let (cell, p) := p.allocOvfl .index key 0 pg
        fitIndexLeaf p pg (cells.insertIdxIfInBounds i cell)
    | .index (.iinner cells kids) =>
      let i := lowerBoundRec ki cells key
      if i < cells.size && cmpRecords ki (cells.getD i default).payload key == .eq then
        (p.put pg (.index (.iinner cells kids)), #[])
      else
      let (p, sp) := iInsert ki (kids.getD i 0) key fuel p
      if sp.isEmpty then (p.put pg (.index (.iinner cells kids)), #[])
      else fitIndexInner p pg (insertMany cells i (sp.map (·.1))) (insertMany kids (i+1) (sp.map (·.2)))
    | other => (p.put pg other, #[])

/-- Inserts the entry `key` (a record ending with the rowid) in the index tree at `root` (nothing if present). -/
def indexInsert (p : Pager) (ki : KeyInfo) (root : Pgno) (key : ByteArray) : Pager :=
  let (p, sp) := iInsert ki root key maxDepth p
  growIndexRoot p root sp

/-- Puts every page of the subtree at `pg` on the freelist (overflow pages too). -/
def freeTree (pg : Pgno) : Nat → Pager → Pager
  | 0, p => p
  | fuel+1, p =>
    let (kids, ovfl) := Pager.links (p.get pg)
    let p := ovfl.foldl Pager.release p
    let p := kids.foldl (fun p k => freeTree k fuel p) p
    p.release pg

/-- Like `fixTableChild` for an index node: the separator, an entry, moves down into the merged node. -/
def fixIndexChild (p : Pager) (cells : Array Cell) (kids : Array Pgno) (i : Nat) : Pager × Array Cell × Array Pgno :=
  if kids.size < 2 || !isUnderfull (p.get (kids.getD i 0)) then (p, cells, kids) else
  let l := if i > 0 then i - 1 else 0
  let lp := kids.getD l 0
  let rp := kids.getD (l+1) 0
  let sep := cells.getD l default
  let (lpage, p) := p.take lp
  let (rpage, p) := p.take rp
  let cells := cells.eraseIdxIfInBounds l
  let kids := kids.eraseIdxIfInBounds (l+1)
  match lpage, rpage with
  | .index (.ileaf c1), .index (.ileaf c2) =>
    let p := p.release rp
    let (p, sp) := fitIndexLeaf p lp (c1.push sep ++ c2)
    (p, insertMany cells l (sp.map (·.1)), insertMany kids (l+1) (sp.map (·.2)))
  | .index (.iinner c1 d1), .index (.iinner c2 d2) =>
    let p := p.release rp
    let (p, sp) := fitIndexInner p lp (c1.push sep ++ c2) (d1 ++ d2)
    (p, insertMany cells l (sp.map (·.1)), insertMany kids (l+1) (sp.map (·.2)))
  | a, b => (p.put lp a |>.put rp b, cells.insertIdxIfInBounds l sep, kids.insertIdxIfInBounds (l+1) rp)

/-- Removes the subtree's largest entry and returns it, with whether the subtree's root is left with no cells. -/
def removeMax (pg : Pgno) : Nat → Pager → Pager × Option Cell × Bool
  | 0, p => (p, none, false)
  | fuel+1, p =>
    match p.get pg with
    | .index (.ileaf cells) =>
      match cells.back? with
      | none => (p, none, true)
      | some c =>
        let (_, p) := p.take pg
        (p.put pg (.index (.ileaf cells.pop)), some c, cells.size == 1)
    | .index (.iinner cells kids) =>
      let last := kids.size - 1
      let (p, m, uf) := removeMax (kids.getD last 0) fuel p
      if !uf then (p, m, false) else
      let (_, p) := p.take pg
      let (p, cells, kids) := fixIndexChild p cells kids last
      let (p, sp) := fitIndexInner p pg cells kids
      -- a merge that split again leaves this node's cells as they were (its sibling took the rest): not underfull
      (p, m, cells.isEmpty && sp.isEmpty)
    | _ => (p, none, false)

def iDelete (ki : KeyInfo) (pg : Pgno) (key : ByteArray) : Nat → Pager → Pager × ISplits × Bool
  | 0, p => (p, #[], false)
  | fuel+1, p =>
    match p.get pg with
    | .index (.ileaf cells) =>
      let i := lowerBoundRec ki cells key
      if i < cells.size && cmpRecords ki (cells.getD i default).payload key == .eq then
        let (_, p) := p.take pg
        let p := p.releaseOvfl (cells.getD i default)
        let cells := cells.eraseIdxIfInBounds i
        (p.put pg (.index (.ileaf cells)), #[], cells.isEmpty)
      else (p, #[], false)
    | .index (.iinner cells kids) =>
      let i := lowerBoundRec ki cells key
      if i < cells.size && cmpRecords ki (cells.getD i default).payload key == .eq then
        -- an interior entry: its predecessor (the largest entry of its left subtree) takes its place
        let old := cells.getD i default
        let (p, m, uf) := removeMax (kids.getD i 0) maxDepth p
        let (_, p) := p.take pg
        let p := p.releaseOvfl old
        let cells := match m with | some c => cells.setIfInBounds i c | none => cells.eraseIdxIfInBounds i
        let kids := match m with | some _ => kids | none => kids.eraseIdxIfInBounds i
        let (p, cells, kids) := if uf && m.isSome then fixIndexChild p cells kids i else (p, cells, kids)
        let (p, sp) := fitIndexInner p pg cells kids
        (p, sp, cells.isEmpty && sp.isEmpty)
      else
        let (p, sp, uf) := iDelete ki (kids.getD i 0) key fuel p
        if sp.isEmpty && !uf then (p, #[], false) else
        let (_, p) := p.take pg
        let cells := insertMany cells i (sp.map (·.1))
        let kids := insertMany kids (i+1) (sp.map (·.2))
        let (p, cells, kids) := if uf then fixIndexChild p cells kids i else (p, cells, kids)
        let (p, sp) := fitIndexInner p pg cells kids
        (p, sp, cells.isEmpty && sp.isEmpty)
    | _ => (p, #[], false)

/-- Deletes the entry `key` from the index tree at `root`. -/
def indexDelete (p : Pager) (ki : KeyInfo) (root : Pgno) (key : ByteArray) : Pager :=
  let (p, sp, _) := iDelete ki root key maxDepth p
  collapseRoot (growIndexRoot p root sp) root maxDepth

/-! ## Whole trees -/

/-- A new empty tree on a fresh page. -/
def create (p : Pager) (k : TreeKind) (temp : Bool := false) : Pgno × Pager :=
  let (pg, p) := p.alloc (if temp then tempRoot else 0)
  (pg, p.put pg (match k with | .table => .table (.tleaf #[] #[]) | .index => .index (.ileaf #[])))

/-- Deletes every entry: the root becomes an empty leaf, the other pages go on the freelist. -/
def clear (p : Pager) (root : Pgno) : Pager :=
  let (kids, ovfl) := Pager.links (p.get root)
  let p := ovfl.foldl Pager.release p
  let p := kids.foldl (fun p k => freeTree k maxDepth p) p
  let (old, p) := p.take root
  p.put root (match old with | .index _ => .index (.ileaf #[]) | _ => .table (.tleaf #[] #[]))

/-- Frees the whole tree, root included. -/
def drop (p : Pager) (root : Pgno) : Pager := freeTree root maxDepth p

/-! ## Cursors

A cursor is the path from the root to an entry: `(page, index)` frames. On a leaf frame the index is the entry's; on an
interior frame it is the child the path goes through, or (index trees, `atInner`) the interior entry itself. An empty
path is past the end. -/

structure Cursor where
  stack : Array (Pgno × Nat) := #[]
  atInner : Bool := false
  deriving Inhabited

namespace Cursor

def atEnd (c : Cursor) : Bool := c.stack.isEmpty

/-- The path down the leftmost children from `pg`. -/
def descendFirst (p : Pager) (stack : Array (Pgno × Nat)) (pg : Pgno) : Nat → Array (Pgno × Nat)
  | 0 => stack
  | fuel+1 =>
    match p.get pg with
    | .table (.tinner _ kids) | .index (.iinner _ kids) => descendFirst p (stack.push (pg, 0)) (kids.getD 0 0) fuel
    | _ => stack.push (pg, 0)

/-- Moves the path to the next entry at or after it: from a leaf position past its last cell, up to the next interior
entry (index trees) or down the next subtree (table trees, and index trees after an interior entry). -/
def settle (p : Pager) (stack : Array (Pgno × Nat)) : Nat → Cursor
  | 0 => {}
  | fuel+1 =>
    match stack.back? with
    | none => {}
    | some (pg, i) =>
      match p.get pg with
      | .table (.tleaf keys _) => if i < keys.size then { stack } else settle p stack.pop fuel
      | .index (.ileaf cells) => if i < cells.size then { stack } else settle p stack.pop fuel
      | .table (.tinner _ kids) =>
        if i + 1 < kids.size then
          settle p (descendFirst p (stack.pop.push (pg, i+1)) (kids.getD (i+1) 0) maxDepth) fuel
        else settle p stack.pop fuel
      | .index (.iinner cells _) => if i < cells.size then { stack, atInner := true } else settle p stack.pop fuel
      | _ => {}

/-- Steps to the next entry. -/
def next (p : Pager) (c : Cursor) : Cursor :=
  match c.stack.back? with
  | none => c
  | some (pg, i) =>
    let fuel := p.totalPages + maxDepth
    if c.atInner then
      match p.get pg with
      | .index (.iinner _ kids) =>
        settle p (descendFirst p (c.stack.pop.push (pg, i+1)) (kids.getD (i+1) 0) maxDepth) fuel
      | _ => {}
    else settle p (c.stack.pop.push (pg, i+1)) fuel

/-- The first entry of the tree. -/
def first (p : Pager) (root : Pgno) : Cursor :=
  settle p (descendFirst p #[] root maxDepth) (p.totalPages + maxDepth)

/-- The first row whose rowid is at least `rowid`. -/
def seekRowid (p : Pager) (root : Pgno) (rowid : Int64) : Cursor :=
  settle p (go root #[] maxDepth) (p.totalPages + maxDepth)
where
  go (pg : Pgno) (stack : Array (Pgno × Nat)) : Nat → Array (Pgno × Nat)
    | 0 => stack
    | fuel+1 =>
      match p.get pg with
      | .table (.tleaf keys _) => stack.push (pg, lowerBound keys rowid)
      | .table (.tinner keys kids) =>
        let i := lowerBound keys rowid
        go (kids.getD i 0) (stack.push (pg, i)) fuel
      | _ => stack

/-- The first index entry at or after `probe` (a record; a shorter probe matches the entries it is a prefix of). -/
def seekKey (p : Pager) (ki : KeyInfo) (root : Pgno) (probe : ByteArray) : Cursor :=
  settle p (go root #[] maxDepth) (p.totalPages + maxDepth)
where
  go (pg : Pgno) (stack : Array (Pgno × Nat)) : Nat → Array (Pgno × Nat)
    | 0 => stack
    | fuel+1 =>
      match p.get pg with
      | .index (.ileaf cells) => stack.push (pg, lowerBoundRec ki cells probe)
      | .index (.iinner cells kids) =>
        let i := lowerBoundRec ki cells probe
        go (kids.getD i 0) (stack.push (pg, i)) fuel
      | _ => stack

/-- The current row of a table cursor: rowid and record. -/
def row (p : Pager) (c : Cursor) : Option (Int64 × ByteArray) :=
  match c.stack.back? with
  | none => none
  | some (pg, i) =>
    match p.get pg with
    | .table (.tleaf keys cells) => some (keys.getD i 0, (cells.getD i default).payload)
    | _ => none

/-- The current entry of an index cursor. -/
def key (p : Pager) (c : Cursor) : Option ByteArray :=
  match c.stack.back? with
  | none => none
  | some (pg, i) =>
    match p.get pg with
    | .index (.ileaf cells) | .index (.iinner cells _) => cells[i]?.map (·.payload)
    | _ => none

end Cursor

/-- An upper bound on the number of entries in the database (each cell takes at least 4 bytes of a page): fuel for a
loop over a cursor. -/
def entryBound (p : Pager) : Nat := p.totalPages * (p.geo.usable / 4 + 1) + 1

/-- Folds `f` over the rows of a table tree in rowid order. -/
def foldTable (p : Pager) (root : Pgno) (init : β) (f : β → Int64 → ByteArray → β) : β :=
  go (Cursor.first p root) init (entryBound p)
where
  go (c : Cursor) (acc : β) : Nat → β
    | 0 => acc
    | fuel+1 =>
      match c.row p with
      | none => acc
      | some (k, r) => go (c.next p) (f acc k r) fuel

/-- Folds `f` over the entries of an index tree in order. -/
def foldIndex (p : Pager) (root : Pgno) (init : β) (f : β → ByteArray → β) : β :=
  go (Cursor.first p root) init (entryBound p)
where
  go (c : Cursor) (acc : β) : Nat → β
    | 0 => acc
    | fuel+1 =>
      match c.key p with
      | none => acc
      | some k => go (c.next p) (f acc k) fuel

end BTree
end LSql
