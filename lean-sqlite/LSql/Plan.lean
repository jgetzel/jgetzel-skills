import LSql.Schema
/-! Compiled statements: expressions with their column references resolved to frame slots and their affinities and
collations decided, and SELECTs with an access path chosen for each table (sqlite's where.c in miniature). -/
namespace LSql

/-- How a table's rows are found: all of them, by rowid, by a rowid range, through an index (an equality prefix, then an
optional range on the next column; each probe value converted with the comparison's affinity), or through a transient
index. `E`: the probes' expressions (`CExpr` in a plan, compiled closures when it runs). -/
inductive Access (E : Type) where
  | full
  | rowidEq (e : E)
  | rowidIn (items : Array E)
  | rowidRange (lo hi : Option (E × Bool))
  | index (root : Pgno) (ki : KeyInfo) (eqs : Array (E × Aff)) (lo hi : Option (E × Bool × Aff))
  /-- sqlite's automatic index: built once per run of the SELECT on the columns at slots `keys`, then searched for the rows
  whose columns equal the probes (both sides with the comparison's affinity, under its collation) -/
  | auto (keys : Array (Nat × E × Aff × Collation))

/-- The same access path with each probe expression mapped. -/
def Access.map (f : α → β) : Access α → Access β
  | .full => .full
  | .rowidEq e => .rowidEq (f e)
  | .rowidIn items => .rowidIn (items.map f)
  | .rowidRange lo hi => .rowidRange (lo.map fun (e, i) => (f e, i)) (hi.map fun (e, i) => (f e, i))
  | .index root ki eqs lo hi =>
    .index root ki (eqs.map fun (e, a) => (f e, a)) (lo.map fun (e, i, a) => (f e, i, a)) (hi.map fun (e, i, a) => (f e, i, a))
  | .auto keys => .auto (keys.map fun (s, e, a, c) => (s, f e, a, c))

mutual
/-- A compiled expression. A column is `(depth, slot)`: the row frame `depth` levels out from the current one. -/
inductive CExpr where
  | lit (v : Value)
  | col (depth slot : Nat)
  /-- + - * / % || & | << >> -/
  | arith (op : BinOp) (a b : CExpr)
  /-- = != < <= > >= IS IS NOT, after applying the comparison affinity to both sides, under a collation -/
  | cmp (op : BinOp) (a b : CExpr) (aff : Aff) (coll : Collation)
  | and (a b : CExpr)
  | or (a b : CExpr)
  | not (a : CExpr)
  | neg (a : CExpr)
  | bitNot (a : CExpr)
  | fn (name : String) (args : Array CExpr)
  /-- the current group's value of aggregate `i` -/
  | agg (i : Nat)
  | case (base : Option CExpr) (whens : Array (CExpr × CExpr)) (els : Option CExpr) (aff : Aff) (coll : Collation)
  | cast (e : CExpr) (aff : Aff)
  | inList (e : CExpr) (items : Array CExpr) (neg : Bool) (aff : Aff) (coll : Collation)
  /-- an IN whose subquery ran already: its values sorted under `coll`, and whether one was NULL -/
  | inVals (e : CExpr) (vals : Array Value) (hasNull : Bool) (neg : Bool) (aff : Aff) (coll : Collation)
  /-- `corr`: the subquery refers to the enclosing query's rows, so it runs again for each -/
  | inSel (e : CExpr) (q : CSel) (neg : Bool) (aff : Aff) (coll : Collation) (corr : Bool)
  | «exists» (q : CSel) (neg : Bool) (corr : Bool)
  | scalar (q : CSel) (corr : Bool)
  | matchE (op : MatchOp) (e pat : CExpr) (esc : Option CExpr) (neg : Bool)
  | isNull (e : CExpr) (neg : Bool)
  /-- `(a, b) [NOT] IN (SELECT x, y ...)`: each item against its column, with its affinity and collation -/
  | inSelRow (es : Array CExpr) (q : CSel) (neg : Bool) (affs : Array Aff) (colls : Array Collation)
  /-- the current row's value of window function `i` -/
  | win (i : Nat)
  /-- RAISE(kind, message) in a trigger body -/
  | raise (kind : RaiseKind) (msg : String)

/-- A frame bound with its offset expression. -/
inductive CBound where
  | unboundedPreceding
  | preceding (e : CExpr)
  | currentRow
  | following (e : CExpr)
  | unboundedFollowing

/-- A window function call: its arguments and FILTER, PARTITION BY keys (with collations), ORDER BY keys (with
directions), and frame. -/
inductive CWin where
  | mk (name : String) (distinct : Bool) (star : Bool) (args : Array CExpr) (filter : Option CExpr)
      (partition : Array CExpr) (pcolls : Array Collation) (order : Array CExpr) (dirs : Array (Bool × Bool × Collation))
      (units : FrameUnits) (start finish : CBound) (exclude : FrameExclude)

/-- A FROM item: its first slot in the row frame; for an outer join the ON conditions that decide whether a row matched;
`left`: a row of the earlier items with no match gets NULLs here (LEFT, FULL); `right`: a row of this item no earlier
row matched gets NULLs for the earlier items (RIGHT, FULL). A table's slots are its columns, then its rowid; `layout`
(WITHOUT ROWID tables) is the table column of each record field, whose tree is then the index-format table. -/
inductive CSource where
  | table (root : Pgno) (ncols : Nat) (ipk : Option Nat) (realCols : Array Bool) (defaults : Array Value) (base : Nat)
      (access : Access CExpr) (left : Bool) (right : Bool) (layout : Array Nat) (on : Array CExpr)
  /-- `auto`: the keys of its transient index, as in `Access.auto` (none when empty) -/
  | sub (q : CSel) (ncols : Nat) (base : Nat) (left : Bool) (right : Bool) (on : Array CExpr)
      (auto : Array (Nat × CExpr × Aff × Collation))
  | cte (id : Nat) (ncols : Nat) (base : Nat) (left : Bool) (right : Bool) (on : Array CExpr)
      (auto : Array (Nat × CExpr × Aff × Collation))
  /-- a table-valued function (json_each, json_tree, pragma_*) over its arguments, evaluated for each row of the earlier
  items -/
  | tvf (fn : String) (args : Array CExpr) (ncols : Nat) (base : Nat) (left : Bool) (right : Bool) (on : Array CExpr)

/-- An aggregate call; `coll`: the collation min() and max() compare under (their argument's). -/
inductive CAgg where
  | mk (name : String) (distinct : Bool) (star : Bool) (args : Array CExpr) (coll : Collation) (filter : Option CExpr)

inductive CCore where
  /-- `filters[i]`: the conditions checked once sources `0..i` are bound; `pre`: those that need no source.
  `gcolls`, `rcolls`: the collations GROUP BY keys and (for DISTINCT) result columns compare under.
  `order`: the ORDER BY keys, computed beside each result row. -/
  | select (srcs : Array CSource) (pre : Array CExpr) (filters : Array (Array CExpr)) (groupBy : Array CExpr)
      (gcolls : Array Collation) (having : Option CExpr) (cols : Array CExpr) (rcolls : Array Collation)
      (order : Array CExpr) (aggs : Array CAgg) (isAgg : Bool) (distinct : Bool) (width : Nat)
      (wins : Array CWin)
  | values (rows : Array (Array CExpr)) (order : Array Nat)

/-- A WITH table, materialized when its SELECT runs. A recursive one's query has two cores: the initial one, then the
recursive one reading the queue's current row. -/
inductive CCte where
  | mk (id : Nat) (q : CSel) (recursive : Bool)

/-- A compiled SELECT: its WITH tables, cores and compound operators, ORDER BY directions (desc, nulls first,
collation), LIMIT and OFFSET, and its column count. -/
inductive CSel where
  | mk (ctes : Array CCte) (cores : Array CCore) (ops : Array CompoundOp) (dirs : Array (Bool × Bool × Collation))
      (limit offset : Option CExpr) (ncols : Nat)
end

instance : Inhabited CExpr := ⟨.lit .null⟩
def CSel.ncols : CSel → Nat
  | .mk _ _ _ _ _ _ n => n

instance : Inhabited CSource := ⟨.cte 0 0 0 false false #[] #[]⟩
instance : Inhabited CSel := ⟨.mk #[] #[] #[] #[] none none 0⟩

end LSql
