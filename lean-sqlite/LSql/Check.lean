import LSql.Exec
/-! PRAGMA integrity_check (btree.c sqlite3BtreeIntegrityCheck, pragma.c's index checks): every tree's order and shape,
every page owned once, and every index holding exactly its table's rows. -/
namespace LSql.Check

structure St where
  /-- the owner of each page: 0 none, 1 a tree, 2 overflow, 3 the freelist -/
  owner : Array UInt8
  errs : Array String := #[]

def own (st : St) (pg : Pgno) (what : UInt8) : St :=
  let i := pg.toNat - 1
  if pg == 0 || i ≥ st.owner.size then { st with errs := st.errs.push s!"invalid page number {pg}" }
  else if st.owner.getD i 0 != 0 then { st with errs := st.errs.push s!"2nd reference to page {pg}" }
  else { st with owner := st.owner.setIfInBounds i what }

/-- Walks a table tree: the depth of its leaves, after checking rowids lie in `(lo, hi]` in order. -/
def walkTable (p : Pager) (root : Pgno) (pg : Pgno) (lo hi : Option Int64) (st : St) : Nat → St × Nat
  | 0 => ({ st with errs := st.errs.push s!"Tree {root}: btree depth exceeds 64" }, 0)
  | fuel+1 =>
    let st := own st pg 1
    match p.get pg with
    | .table (.tleaf keys cells used) =>
      let inRange (k : Int64) : Bool := (lo.all (· < k)) && (hi.all (k ≤ ·))
      let sorted := (List.range (keys.size - 1)).all fun i => keys.getD i 0 < keys.getD (i+1) 0
      let st := if sorted && keys.all inRange then st else { st with errs := st.errs.push s!"Tree {root} page {pg}: rowid out of order" }
      let st := if keys.isEmpty && pg != root then { st with errs := st.errs.push s!"Tree {root} page {pg}: empty page" } else st
      let st := if used == leafUsed cells then st else { st with errs := st.errs.push s!"Tree {root} page {pg}: used size wrong" }
      let st := cells.foldl (fun st c =>
        let st := if c.ovfl.size != p.geo.ovflPages .table c.payload.size then
          { st with errs := st.errs.push s!"Tree {root} page {pg}: overflow list length wrong" } else st
        c.ovfl.foldl (fun st o => own st o 2) st) st
      (st, 0)
    | .table (.tinner keys kids) =>
      let st := if kids.size != keys.size + 1 then { st with errs := st.errs.push s!"Tree {root} page {pg}: bad child count" } else st
      let st := if keys.isEmpty && pg != root && pg != 1 then { st with errs := st.errs.push s!"Tree {root} page {pg}: empty page" } else st
      let (st, depths) := (List.range kids.size).foldl (fun (st, ds) i =>
        let l := if i == 0 then lo else keys[i-1]?
        let h := if i < keys.size then keys[i]? else hi
        let (st, d) := walkTable p root (kids.getD i 0) l h st fuel
        (st, ds.push d)) (st, #[])
      let d := depths.getD 0 0
      let st := if depths.all (· == d) then st else { st with errs := st.errs.push s!"Tree {root} page {pg}: Child page depth differs" }
      (st, d + 1)
    | _ => ({ st with errs := st.errs.push s!"Tree {root} page {pg}: not a table b-tree page" }, 0)

/-- Walks an index tree's entries in order, checking each follows the last. -/
def walkIndex (p : Pager) (ki : KeyInfo) (root : Pgno) (pg : Pgno) (st : St × Option ByteArray) : Nat → (St × Option ByteArray) × Nat
  | 0 => (({ st.1 with errs := st.1.errs.push s!"Tree {root}: btree depth exceeds 64" }, st.2), 0)
  | fuel+1 =>
    let entry (acc : St × Option ByteArray) (c : Cell) : St × Option ByteArray :=
      let (s, prev) := acc
      let s := match prev with
        | some q => if cmpRecords ki q c.payload == .lt then s else { s with errs := s.errs.push s!"Tree {root} page {pg}: index out of order" }
        | none => s
      let s := c.ovfl.foldl (fun s o => own s o 2) s
      (s, some c.payload)
    let st := (own st.1 pg 1, st.2)
    match p.get pg with
    | .index (.ileaf cells used) =>
      let st := if cells.isEmpty && pg != root then ({ st.1 with errs := st.1.errs.push s!"Tree {root} page {pg}: empty page" }, st.2) else st
      let st := if used == leafUsed cells then st else ({ st.1 with errs := st.1.errs.push s!"Tree {root} page {pg}: used size wrong" }, st.2)
      (cells.foldl entry st, 0)
    | .index (.iinner cells kids) =>
      let (st, depths) := (List.range kids.size).foldl (fun (st, ds) i =>
        let (st, d) := walkIndex p ki root (kids.getD i 0) st fuel
        let st := match cells[i]? with | some c => entry st c | none => st
        (st, ds.push d)) (st, #[])
      let d := depths.getD 0 0
      let st := if depths.all (· == d) then st else ({ st.1 with errs := st.1.errs.push s!"Tree {root} page {pg}: Child page depth differs" }, st.2)
      (st, d + 1)
    | _ => (({ st.1 with errs := st.1.errs.push s!"Tree {root} page {pg}: not an index b-tree page" }, st.2), 0)

/-- The integrity check's messages (none: ok). -/
def run (db : DB) : Array String :=
  let p := db.pager
  let st : St := { owner := Array.replicate p.pages.size 0 }
  let st := p.free.foldl (fun st f => own st f 3) st
  let st := (walkTable p 1 1 none none st 64).1
  -- the temp schema's objects live outside the file
  let db := { db with schema := { db.schema with tables := db.schema.tables.filter (!·.temp),
                                                 indexes := db.schema.indexes.filter (!·.temp) } }
  let st := db.schema.tables.foldl (fun st t =>
    if t.withoutRowid then (walkIndex p t.pkKeyInfo t.root t.root (st, none) 64).1.1
    else (walkTable p t.root t.root none none st 64).1) st
  let st := db.schema.indexes.foldl (fun st ix => (walkIndex p ix.keyInfo ix.root ix.root (st, none) 64).1.1) st
  let st := (List.range p.pages.size).foldl (fun st i =>
    if st.owner.getD i 0 == 0 then { st with errs := st.errs.push s!"Page {i + 1}: never used" } else st) st
  -- every index holds its table's rows, and nothing else
  let errs := db.schema.indexes.foldl (fun errs ix =>
    match db.schema.table? ix.table with
    | none => errs
    | some t =>
      let rows := if t.withoutRowid then BTree.foldIndex p t.root #[] fun acc r => acc.push (worRowOf t r, (0 : Int64))
        else BTree.foldTable p t.root #[] fun acc k r => acc.push (tableRow t k r, k)
      let px := PIdx.of db.schema t ix
      let rows := rows.filter fun (r, _) => inIndex px db.env r
      let n := BTree.foldIndex p ix.root 0 fun n _ => n + 1
      let errs := if n != rows.size then errs.push s!"wrong # of entries in index {ix.name}" else errs
      rows.foldl (fun errs (r, k) =>
        let key := idxEntry px r k
        let c := BTree.Cursor.seekKey p ix.keyInfo ix.root key
        if (c.key p).any (cmpRecords ix.keyInfo · key == .eq) then errs else errs.push s!"row {k} missing from index {ix.name}") errs) st.errs
  errs

end LSql.Check
