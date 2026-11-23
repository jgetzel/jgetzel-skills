import LSql.Schema
/-! The schema pragmas' rows (pragma.c): table_info, table_xinfo, index_list, index_info, index_xinfo; used by PRAGMA and
by the table-valued functions pragma_table_info(...) and the like. -/
namespace LSql

/-- A DEFAULT as pragma table_info shows it: the expression's SQL. -/
def defaultText : Option Expr → Value
  | none => .null
  | some (.lit .null) => .text "NULL"
  | some (.lit (.int i)) => .text (Num.int64ToText i)
  | some (.lit (.real f)) => .text (Num.fmtReal f)
  | some (.lit (.text s)) => .text ("'" ++ s.replace "'" "''" ++ "'")
  | some (.lit (.blob b)) => .text ("X'" ++ hexOf b ++ "'")
  | some (.un .neg (.lit (.int i))) => .text ("-" ++ Num.int64ToText i)
  | some (.un .neg (.lit (.real f))) => .text ("-" ++ Num.fmtReal f)
  | some _ => .text "?"

def isPkIndex (s : Schema) (ix : Index) : Bool :=
  match s.table? ix.table with
  | some t => ix.cols.all (fun c => (t.cols.getD c default).pk) && ix.cols.size == (t.cols.filter (·.pk)).size
  | none => false

/-- A schema pragma's column names and rows for its argument; none for another pragma. -/
def schemaPragma (s : Schema) (name : String) (arg : String) : Option (Array String × Array (Array Value)) :=
  match lowerAscii name with
  | "table_info" | "table_xinfo" =>
    let xinfo := lowerAscii name == "table_xinfo"
    let names := #["cid", "name", "type", "notnull", "dflt_value", "pk"] ++ (if xinfo then #["hidden"] else #[])
    match s.table? arg with
    | none => some (names, #[])
    | some t =>
      let pkCols := if t.withoutRowid then t.pkCols.toList else t.cols.toList.zipIdx.filter (·.1.pk) |>.map (·.2)
      let rows := t.cols.mapIdx fun i c =>
        -- sqlite keeps its standard type names (sqlite3StdType) in upper case
        let ty := if ["ANY", "BLOB", "INT", "INTEGER", "REAL", "TEXT"].contains (upperAscii c.type) then upperAscii c.type else c.type
        #[.int i.toInt64, .text c.name, .text ty, .int (if c.notNull then 1 else 0), defaultText c.default,
          .int (match pkCols.idxOf? i with | some k => (k + 1).toInt64 | none => 0)] ++ (if xinfo then #[.int 0] else #[])
      some (names, rows)
  | "index_list" =>
    let idxs := (s.indexesOf arg).reverse
    some (#["seq", "name", "unique", "origin", "partial"], idxs.mapIdx fun i ix =>
      #[.int i.toInt64, .text ix.name, .int (if ix.unique then 1 else 0),
        .text (if ix.sql.isSome then "c" else if isPkIndex s ix then "pk" else "u"), .int (if ix.pred.isSome then 1 else 0)])
  | "index_info" | "index_xinfo" =>
    let names := if lowerAscii name == "index_xinfo" then #["seqno", "cid", "name", "desc", "coll", "key"] else #["seqno", "cid", "name"]
    match s.index? arg with
    | none => some (names, #[])
    | some ix =>
      let t := s.table? ix.table
      let collName : Collation → String | .binary => "BINARY" | .nocase => "NOCASE" | .rtrim => "RTRIM"
      some (names, ix.cols.mapIdx fun i c =>
        let isExpr := (ix.exprs.getD i none).isSome
        let base : Array Value := #[.int i.toInt64, .int (if isExpr then -2 else c.toInt64),
          if isExpr then .null else .text ((t.map fun t => (t.cols.getD c default).name).getD "")]
        if names.size == 3 then base else
        base ++ #[.int (if ix.desc.getD i false then 1 else 0), .text (collName (ix.colls.getD i .binary)), .int 1])
  | _ => none

end LSql
