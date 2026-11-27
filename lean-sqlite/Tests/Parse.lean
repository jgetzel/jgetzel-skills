import LSql.Parse
/-! Tests of the SQL parser: #guard checks against the AST shape (printed by a small S-expression printer) and sqlite's error texts. -/
namespace TestParse
open LSql LSql.Parse

def seg (r : Std.Format) : String := ((toString r).splitOn ".").getLast?.getD ""
def sOp (o : BinOp) : String := seg (repr o)

def sVal : Value → String
  | .null => "NULL"
  | .int i => toString i
  | .real f => "r" ++ toString f
  | .text s => "'" ++ s ++ "'"
  | .blob b => "x" ++ toString b.size

def sOpt {α : Type} (f : α → String) : Option α → String
  | none => "-"
  | some a => f a

def join (xs : List String) : String := " ".intercalate xs

mutual
def sE : Nat → Expr → String
  | 0, _ => "..."
  | f + 1, e => match e with
    | .lit v => sVal v
    | .col none n dq => if dq then "\"" ++ n ++ "\"" else n
    | .col (some t) n _ => t ++ "." ++ n
    | .bin op a b => "(" ++ sOp op ++ " " ++ sE f a ++ " " ++ sE f b ++ ")"
    | .un op a => "(" ++ seg (repr op) ++ " " ++ sE f a ++ ")"
    | .fn n d s args => "(" ++ n ++ (if d then "!distinct" else "") ++ (if s then "*" else "") ++ (if args.isEmpty then "" else " " ++ join (args.map (sE f))) ++ ")"
    | .cast e t => "(cast " ++ sE f e ++ " " ++ t ++ ")"
    | .collate e c => "(collate " ++ sE f e ++ " " ++ c ++ ")"
    | .case b ws el => "(case " ++ sOpt (sE f) b ++ " " ++ join (ws.map fun (w, t) => "[" ++ sE f w ++ " " ++ sE f t ++ "]") ++ " " ++ sOpt (sE f) el ++ ")"
    | .between e lo hi n => "(" ++ (if n then "not-" else "") ++ "between " ++ sE f e ++ " " ++ sE f lo ++ " " ++ sE f hi ++ ")"
    | .inList e xs n => "(" ++ (if n then "not-" else "") ++ "in " ++ sE f e ++ " [" ++ join (xs.map (sE f)) ++ "])"
    | .inSelect e q n => "(" ++ (if n then "not-" else "") ++ "in " ++ sE f e ++ " " ++ sSel f q ++ ")"
    | .matches op e p esc n => "(" ++ (if n then "not-" else "") ++ seg (repr op) ++ " " ++ sE f e ++ " " ++ sE f p ++ (match esc with | none => "" | some x => " esc " ++ sE f x) ++ ")"
    | .isNull e n => "(" ++ (if n then "notnull " else "isnull ") ++ sE f e ++ ")"
    | .«exists» q n => "(" ++ (if n then "not-" else "") ++ "exists " ++ sSel f q ++ ")"
    | .subquery q => "(" ++ sSel f q ++ ")"
    | .param t => "param:" ++ t
    | .row xs => "(row " ++ join (xs.map (sE f)) ++ ")"
    | .window n d s args flt w => "(" ++ n ++ (if d then "!distinct" else "") ++ (if s then "*" else "") ++ (if args.isEmpty then "" else " " ++ join (args.map (sE f)))
        ++ (match flt with | none => "" | some e => " filter " ++ sE f e) ++ " over " ++ sW f w ++ ")"
    | .raise k m => "(raise " ++ seg (repr k) ++ (if m == "" then "" else " '" ++ m ++ "'") ++ ")"

def sW : Nat → Window → String
  | 0, _ => "..."
  | f + 1, .mk part ob fr =>
    "[" ++ (if part.isEmpty then "" else "part " ++ join (part.map (sE f)) ++ " ")
    ++ (if ob.isEmpty then "" else "order " ++ join (ob.map fun (.mk e d nf) => sE f e ++ (if d then " desc" else "") ++ (match nf with | none => "" | some b => if b then " nf" else " nl")) ++ " ")
    ++ (match fr with | none => "-" | some (.mk u s e x) => seg (repr u) ++ " " ++ sFB f s ++ ".." ++ sFB f e ++ " " ++ seg (repr x)) ++ "]"

def sFB : Nat → FrameBound → String
  | _, .unboundedPreceding => "unb-prec"
  | f, .preceding e => sE f e ++ "-prec"
  | _, .currentRow => "cur"
  | f, .following e => sE f e ++ "-foll"
  | _, .unboundedFollowing => "unb-foll"

def sSel : Nat → Select → String
  | 0, _ => "..."
  | f + 1, .mk rec ctes first rest ob lim off =>
    "{" ++ (if rec then "rec " else "") ++ join (ctes.map fun (.mk n cs q) => "with " ++ n ++ "(" ++ ",".intercalate cs ++ ")=" ++ sSel f q)
    ++ " " ++ sCore f first ++ join (rest.map fun (op, c) => " " ++ seg (repr op) ++ " " ++ sCore f c)
    ++ (if ob.isEmpty then "" else " order " ++ join (ob.map fun (.mk e d nf) => sE f e ++ (if d then " desc" else "") ++ (match nf with | none => "" | some b => if b then " nf" else " nl")))
    ++ (match lim with | none => "" | some l => " limit " ++ sE f l) ++ (match off with | none => "" | some l => " offset " ++ sE f l) ++ "}"

def sCore : Nat → Core → String
  | 0, _ => "..."
  | f + 1, .select d cols frm joins whr gb hv =>
    "select" ++ (if d then " distinct" else "") ++ " " ++ join (cols.map (sCol f))
    ++ (match frm with | none => "" | some i => " from " ++ sFrom f i)
    ++ join (joins.map fun (.mk k i on us) => " " ++ seg (repr k) ++ "-join " ++ sFrom f i ++ (match on with | none => "" | some e => " on " ++ sE f e) ++ (if us.isEmpty then "" else " using(" ++ ",".intercalate us ++ ")"))
    ++ (match whr with | none => "" | some e => " where " ++ sE f e)
    ++ (if gb.isEmpty then "" else " group " ++ join (gb.map (sE f)))
    ++ (match hv with | none => "" | some e => " having " ++ sE f e)
  | f + 1, .values rows => "values " ++ join (rows.map fun r => "(" ++ join (r.map (sE f)) ++ ")")

def sCol : Nat → ResultCol → String
  | _, .star => "*"
  | _, .tableStar t => t ++ ".*"
  | f, .expr e a sp => sE f e ++ (match a with | none => "" | some a => " as " ++ a) ++ " <" ++ sp ++ ">"

def sFrom : Nat → FromItem → String
  | _, .table n a => n ++ (match a with | none => "" | some a => " as " ++ a)
  | f, .subquery q a => sSel f q ++ (match a with | none => "" | some a => " as " ++ a)
  | f, .call n args a => n ++ "(" ++ join (args.map (sE f)) ++ ")" ++ (match a with | none => "" | some a => " as " ++ a)
end

def sExpr (e : Expr) : String := sE 100 e
def sSelect (q : Select) : String := sSel 100 q

def sIC (c : IndexedCol) : String := c.name ++ (match c.expr with | none => "" | some e => "{" ++ sExpr e ++ "}") ++ (match c.collate with | none => "" | some x => " collate " ++ x) ++ (if c.desc then " desc" else "")
def sCD (c : ColumnDef) : String :=
  c.name ++ ":" ++ c.type ++ (if c.primaryKey then " pk" else "") ++ (if c.pkDesc then " desc" else "") ++ (if c.autoincrement then " ai" else "")
  ++ (if c.notNull then " nn" else "") ++ (if c.unique then " uniq" else "")
  ++ (match c.default with | none => "" | some e => " default " ++ sExpr e) ++ (match c.collate with | none => "" | some x => " collate " ++ x)
  ++ join (c.check.map fun e => " check " ++ sExpr e)
def sTC : TableConstraint → String
  | .primaryKey cs ai => "pk(" ++ ",".intercalate (cs.map sIC) ++ ")" ++ (if ai then " ai" else "")
  | .unique cs => "unique(" ++ ",".intercalate (cs.map sIC) ++ ")"
  | .check e => "check " ++ sExpr e
  | .foreignKey => "fk"
  | .strict => "strict"
def sB (b : Bool) (s : String) : String := if b then " " ++ s else ""

def sUps (u : Upsert) : String :=
  " on-conflict(" ++ ",".intercalate (u.target.map sIC) ++ ")" ++ (match u.targetWhere with | none => "" | some e => " where " ++ sExpr e)
  ++ (match u.update with
    | none => " do-nothing"
    | some (sets, w) => " do-update " ++ join (sets.map fun (n, e) => n ++ "=" ++ sExpr e) ++ (match w with | none => "" | some e => " where " ++ sExpr e))

def sCol' : ResultCol → String := sCol 100

def sStmtF : Nat → Stmt → String
  | 0, _ => "..."
  | f + 1, st =>
    match st with
    | .createTable n ine cols cons wr sql => "create-table " ++ n ++ sB ine "ine" ++ " [" ++ "; ".intercalate (cols.map sCD) ++ "] [" ++ "; ".intercalate (cons.map sTC) ++ "]" ++ sB wr "without-rowid" ++ " sql=" ++ sql
    | .createTableAs n ine q => "create-table-as " ++ n ++ sB ine "ine" ++ " " ++ sSelect q
    | .createIndex n t cols u ine w sql => "create-index " ++ n ++ " on " ++ t ++ " (" ++ ",".intercalate (cols.map sIC) ++ ")" ++ sB u "unique" ++ sB ine "ine" ++ (match w with | none => "" | some e => " where " ++ sExpr e) ++ " sql=" ++ sql
    | .createView n ine cs q sql => "create-view " ++ n ++ sB ine "ine" ++ "(" ++ ",".intercalate cs ++ ") " ++ sSelect q ++ " sql=" ++ sql
    | .dropTable n ie => "drop-table " ++ n ++ sB ie "ie"
    | .dropIndex n ie => "drop-index " ++ n ++ sB ie "ie"
    | .dropView n ie => "drop-view " ++ n ++ sB ie "ie"
    | .insert c t cols src ups => "insert-" ++ seg (repr c) ++ " " ++ t ++ " (" ++ ",".intercalate cols ++ ") " ++ (match src with
        | .values rows => "values " ++ join (rows.map fun r => "(" ++ join (r.map sExpr) ++ ")")
        | .select q => sSelect q
        | .defaults => "defaults") ++ join (ups.map sUps)
    | .update c t sets w => "update-" ++ seg (repr c) ++ " " ++ t ++ " set " ++ join (sets.map fun (n, e) => n ++ "=" ++ sExpr e) ++ (match w with | none => "" | some e => " where " ++ sExpr e)
    | .delete t w => "delete " ++ t ++ (match w with | none => "" | some e => " where " ++ sExpr e)
    | .select q => sSelect q
    | .begin => "begin"
    | .commit => "commit"
    | .rollback => "rollback"
    | .pragma n v => "pragma " ++ n ++ (match v with | none => "" | some v => "=" ++ v)
    | .alterRename t n => "rename " ++ t ++ " " ++ n
    | .alterAddColumn t c txt => "add-column " ++ t ++ " " ++ sCD c ++ " text=" ++ txt
    | .vacuum => "vacuum"
    | .reindex => "reindex"
    | .savepoint n => "savepoint " ++ n
    | .release n => "release " ++ n
    | .rollbackTo n => "rollback-to " ++ n
    | .createTrigger n ine tm ev t w body sql =>
      "create-trigger " ++ n ++ sB ine "ine" ++ " " ++ seg (repr tm) ++ " "
      ++ (match ev with | .insert => "insert" | .delete => "delete" | .update cs => "update(" ++ ",".intercalate cs ++ ")")
      ++ " on " ++ t ++ (match w with | none => "" | some e => " when " ++ sExpr e)
      ++ " body=[" ++ "; ".intercalate (body.map (sStmtF f)) ++ "] sql=" ++ sql
    | .dropTrigger n ie => "drop-trigger " ++ n ++ sB ie "ie"
    | .returning s cols => sStmtF f s ++ " returning " ++ join (cols.map sCol')
    | .alterRenameColumn t o n => "rename-column " ++ t ++ " " ++ o ++ " " ++ n
    | .alterDropColumn t c => "drop-column " ++ t ++ " " ++ c
    | .temp s => "temp(" ++ sStmtF f s ++ ")"

def sStmt (s : Stmt) : String := sStmtF 20 s

/-- The statement printed, or the error as "ERR pos msg". -/
def p1 (src : String) : String :=
  match parseNext src 0 with
  | .ok none => "none"
  | .ok (some (s, _)) => sStmt s
  | .error e => "ERR " ++ toString e.pos ++ " " ++ e.msg

def ex1 (src : String) : String := p1 ("select " ++ src)
/-- Just the first result column's expression. -/
def pe (src : String) : String :=
  match parseNext ("select " ++ src) 0 with
  | .ok (some (.select (.mk _ _ (.select _ [.expr e _ _] ..) ..), _)) => sExpr e
  | .ok (some (s, _)) => "?" ++ sStmt s
  | .ok none => "none"
  | .error e => "ERR " ++ toString e.pos ++ " " ++ e.msg

def endPos (src : String) (pos : Nat) : String :=
  match parseNext src pos with
  | .ok none => "none"
  | .ok (some (s, n)) => sStmt s ++ " @" ++ toString n
  | .error e => "ERR " ++ toString e.pos ++ " " ++ e.msg

/-! ## Generated from verified runs; error texts agree with sqlite3 3.54. -/
#guard p1 "select 1+2*3, a.b, main.t.c, -9223372036854775808, 9223372036854775808, 9223372036854775807, 1e5, .5, 1., 0x1F, 1_000, 'it''s', x'4142', true, false, null, ?, ?3, :a, @b, $c, 0xFFFFFFFFFFFFFFFF, 1.5E-3, 123456789012345678901234567890, 0.1, 1e400, 1e-400, 17976931348623157e292, -.5, +3, 0x0000000000000000001 from t" == "{ select (add 1 (mul 2 3)) <1+2*3> a.b <a.b> t.c <main.t.c> -9223372036854775808 <-9223372036854775808> r9223372036854775808.000000 <9223372036854775808> 9223372036854775807 <9223372036854775807> r100000.000000 <1e5> r0.500000 <.5> r1.000000 <1.> 31 <0x1F> 1000 <1_000> 'it's' <'it''s'> x2 <x'4142'> 1 <true> 0 <false> NULL <null> param:? <?> param:?3 <?3> param::a <:a> param:@b <@b> param:$c <$c> -1 <0xFFFFFFFFFFFFFFFF> r0.001500 <1.5E-3> r123456789012345677877719597056.000000 <123456789012345678901234567890> r0.100000 <0.1> rinf <1e400> r0.000000 <1e-400> r179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.000000 <17976931348623157e292> (neg r0.500000) <-.5> (pos 3) <+3> 1 <0x0000000000000000001> from t}"
#guard p1 "select a from t where a=1 and b<>2 or not c is null" == "{ select a <a> from t where (or (and (eq a 1) (ne b 2)) (not (is c NULL)))}"
#guard p1 "select * from t1 left outer join t2 on t1.a=t2.a join t3 using(a,b), t4 cross join t5 where x between 1 and 2 order by a desc nulls last, b collate nocase limit 5,10" == "{ select * from t1 left-join t2 on (eq t1.a t2.a)  inner-join t3 using(a,b)  cross-join t4  cross-join t5 where (between x 1 2) order a desc nl (collate b nocase) limit 10 offset 5}"
#guard p1 "select count(*), count(distinct a), sum(b) from t" == "{ select (count*) <count(*)> (count!distinct a) <count(distinct a)> (sum b) <sum(b)> from t}"
#guard p1 "select distinct a, b as c, d e, 'f' g, t.* from t" == "{ select distinct a <a> b as c <b> d as e <d> 'f' as g <'f'> t.* from t}"
#guard p1 "with recursive c(x) as (select 1 union all select x+1 from c) select x from c limit 3 offset 1" == "{rec with c(x)={ select 1 <1> unionAll select (add x 1) <x+1> from c} select x <x> from c limit 3 offset 1}"
#guard p1 "select 1 union select 2 intersect select 3 except values (4),(5)" == "{ select 1 <1> union select 2 <2>  intersect select 3 <3>  except values (4) (5)}"
#guard p1 "select a in (1,2), a not in (select 1), a in tbl, a in (), a not between 1 and 2, a like 'x%' escape '!', a not glob 'b', a isnull, a notnull, a not null, a is not distinct from b, a is distinct from b, a is not b" == "{ select (in a [1 2]) <a in (1,2)> (not-in a { select 1 <1>}) <a not in (select 1)> (in a { select * from tbl}) <a in tbl> (in a []) <a in ()> (not-between a 1 2) <a not between 1 and 2> (like a 'x%' esc '!') <a like 'x%' escape '!'> (not-glob a 'b') <a not glob 'b'> (isnull a) <a isnull> (notnull a) <a notnull> (notnull a) <a not null> (is a b) <a is not distinct from b> (isNot a b) <a is distinct from b> (isNot a b) <a is not b>}"
#guard p1 "select cast(a as varchar(10)), cast(b as unsigned big int), case a when 1 then 2 else 3 end, case when x then y end, exists(select 1), not exists (select 2), (select 3)" == "{ select (cast a varchar(10)) <cast(a as varchar(10))> (cast b unsigned big int) <cast(b as unsigned big int)> (case a [1 2] 3) <case a when 1 then 2 else 3 end> (case - [x y] -) <case when x then y end> (exists { select 1 <1>}) <exists(select 1)> (not-exists { select 2 <2>}) <not exists (select 2)> ({ select 3 <3>}) <(select 3)>}"
#guard p1 "select a||b->c->>d, -a collate nocase, a << 2 & 3 | 4, not a = b, 1 = 2 = 3, a - -b" == "{ select (->> (-> (concat a b) c) d) <a||b->c->>d> (collate (neg a) nocase) <-a collate nocase> (bitOr (bitAnd (shl a 2) 3) 4) <a << 2 & 3 | 4> (not (eq a b)) <not a = b> (eq (eq 1 2) 3) <1 = 2 = 3> (sub a (neg b)) <a - -b>}"
#guard p1 "select current_time, current_date, current_timestamp, replace(a,b,c), key, action" == "{ select (current_time) <current_time> (current_date) <current_date> (current_timestamp) <current_timestamp> (replace a b c) <replace(a,b,c)> key <key> action <action>}"
#guard p1 "select 1 between 2 and 3 and 4" == "{ select (and (between 1 2 3) 4) <1 between 2 and 3 and 4>}"
#guard p1 "select 1 + 2 between 3 and 4 or 5" == "{ select (or (between (add 1 2) 3 4) 5) <1 + 2 between 3 and 4 or 5>}"
#guard p1 "select a not like b, a regexp b, a match b, a like b like c" == "{ select (not-like a b) <a not like b> (regexp a b) <a regexp b> (match a b) <a match b> (like (like a b) c) <a like b like c>}"
#guard p1 "select a is null, a is not null, a isnull from t" == "{ select (is a NULL) <a is null> (isNot a NULL) <a is not null> (isnull a) <a isnull> from t}"
#guard p1 "select - - 9223372036854775808" == "{ select (neg -9223372036854775808) <- - 9223372036854775808>}"
#guard p1 "select 1 -9223372036854775808" == "{ select (sub 1 r9223372036854775808.000000) <1 -9223372036854775808>}"
#guard p1 "select 0x7FFFFFFFFFFFFFFF, 0x8000000000000000" == "{ select 9223372036854775807 <0x7FFFFFFFFFFFFFFF> -9223372036854775808 <0x8000000000000000>}"
#guard p1 "select a or b and c = d" == "{ select (or a (and b (eq c d))) <a or b and c = d>}"
#guard p1 "select a || b * c + d << e < f = g and h" == "{ select (and (eq (lt (shl (add (mul (concat a b) c) d) e) f) g) h) <a || b * c + d << e < f = g and h>}"
#guard p1 "select -a || b" == "{ select (concat (neg a) b) <-a || b>}"
#guard p1 "select not a and b" == "{ select (and (not a) b) <not a and b>}"
#guard p1 "select a = not b" == "{ select (eq a (not b)) <a = not b>}"
#guard p1 "select - not 1" == "{ select (neg (not 1)) <- not 1>}"
#guard p1 "select left, right from t" == "{ select left <left> right <right> from t}"
#guard p1 "select left(1,2)" == "{ select (left 1 2) <left(1,2)>}"
#guard p1 "select key, action, replace, temp, \"x\", [y z], `w`, t.\"q\", 'str' from t where \"x\" = 'y'" == "{ select key <key> action <action> replace <replace> temp <temp> \"x\" <\"x\"> y z <[y z]> w <`w`> t.q <t.\"q\"> 'str' <'str'> from t where (eq \"x\" 'y')}"
#guard p1 "select count(all a)" == "{ select (count a) <count(all a)>}"
#guard p1 "select 1 end" == "{ select 1 as end <1>}"
#guard p1 "select 1 e, 2 as 'q', 3 'r'" == "{ select 1 as e <1> 2 as q <2> 3 as r <3>}"
#guard p1 "select a from \"order\"" == "{ select a <a> from order}"
#guard p1 "select * from (select 1) as s, (select 2) t2" == "{ select * from { select 1 <1>} as s cross-join { select 2 <2>} as t2}"
#guard p1 "select a.* from a" == "{ select a.* from a}"
#guard p1 "select 1 from t as x where x.a in (1)" == "{ select 1 <1> from t as x where (in x.a [1])}"
#guard p1 "select e'x'" == "{ select e as x <e>}"
#guard p1 "select cast(1 as)" == "{ select (cast 1 ) <cast(1 as)>}"
#guard p1 "select -x'41'" == "{ select (neg x1) <-x'41'>}"
#guard p1 "select 1 from t join u on 1 left join v using (a) inner join w on 2" == "{ select 1 <1> from t inner-join u on 1  left-join v using(a)  inner-join w on 2}"
#guard p1 "select 1 order by 1 desc, 2 asc nulls first limit 1" == "{ select 1 <1> order 1 desc 2 nf limit 1}"
#guard p1 "select a from t group by a, b having sum(c) > 1 order by a, b desc limit 10 offset 5" == "{ select a <a> from t group a b having (gt (sum c) 1) order a b desc limit 10 offset 5}"
#guard p1 "select 1 where x like y escape z" == "{ select 1 <1> where (like x y esc z)}"
#guard p1 "select a - -1, a--c\n+1" == "{ select (sub a (neg 1)) <a - -1> (add a 1) <a--c\n+1>}"
#guard p1 "select 1 /* a */ + /* b */ 2" == "{ select (add 1 2) <1 /* a */ + /* b */ 2>}"
#guard p1 "select a -> 'x' -> 'y'" == "{ select (-> (-> a 'x') 'y') <a -> 'x' -> 'y'>}"
#guard p1 "select 1 <> 2, 1 != 2, 1 == 2" == "{ select (ne 1 2) <1 <> 2> (ne 1 2) <1 != 2> (eq 1 2) <1 == 2>}"
#guard p1 "select 0x1_F, 1.5_0, 1e1_0, 1_000" == "{ select 31 <0x1_F> r1.500000 <1.5_0> r10000000000.000000 <1e1_0> 1000 <1_000>}"
#guard p1 "select 1.e3" == "{ select r1000.000000 <1.e3>}"
#guard p1 "select a.b.c" == "{ select b.c <a.b.c>}"
#guard p1 "select ~1, ~~1" == "{ select (bitNot 1) <~1> (bitNot (bitNot 1)) <~~1>}"
#guard p1 "create   table  if not exists  \"T 1\" ( a  int ,b); " == "create-table T 1 ine [a:int; b:] [] sql=CREATE TABLE \"T 1\" ( a  int ,b)"
#guard p1 "create table t(a integer primary key autoincrement, b varchar(10) not null default 'x', c unsigned big int unique default -5, d default (1+2) collate nocase check (d>0), e references u(x) on delete cascade, f text default abc, g int default current_timestamp, h, constraint pk primary key (a desc, b collate nocase), unique(a,b), check(a>0), foreign key (a) references u(b)) without rowid, strict /*x*/ ;" == "create-table t [a:integer pk ai; b:varchar(10) nn default 'x'; c:unsigned big int uniq default (neg 5); d: default (add 1 2) collate nocase check (gt d 0); e:; f:text default 'abc'; g:int default (current_timestamp); h:] [pk(a desc,b collate nocase); unique(a,b); check (gt a 0); fk; strict] without-rowid sql=CREATE TABLE t(a integer primary key autoincrement, b varchar(10) not null default 'x', c unsigned big int unique default -5, d default (1+2) collate nocase check (d>0), e references u(x) on delete cascade, f text default abc, g int default current_timestamp, h, constraint pk primary key (a desc, b collate nocase), unique(a,b), check(a>0), foreign key (a) references u(b)) without rowid, strict /*x*/ "
#guard p1 "create table t(a) /*x*/ ; " == "create-table t [a:] [] sql=CREATE TABLE t(a)"
#guard p1 "create table x as select 1" == "create-table-as x { select 1 <1>}"
#guard p1 "create unique index if not exists i1 on t(a desc, b collate nocase) where a>1 --c\n;" == "create-index i1 on t (a desc,b collate nocase) unique ine where (gt a 1) sql=CREATE UNIQUE INDEX i1 on t(a desc, b collate nocase) where a>1 --c\n"
#guard p1 "create index i on t(a)\n\n  ;" == "create-index i on t (a) sql=CREATE INDEX i on t(a)\n\n  "
#guard p1 "create view v(x,y) as select 1,2 /*c*/ ;" == "create-view v(x,y) { select 1 <1> 2 <2>} sql=CREATE VIEW v(x,y) as select 1,2 /*c*/"
#guard p1 "create view v as select 1\n\n  ;" == "create-view v() { select 1 <1>} sql=CREATE VIEW v as select 1"
#guard p1 "create temp table t(a)" == "temp(create-table t [a:] [] sql=CREATE TABLE t(a))"
#guard p1 "create table main.t3(a)" == "create-table t3 [a:] [] sql=CREATE TABLE t3(a)"
#guard p1 "create table t(key, action int, replace text, temp, \"quoted ident\" int, [br] int, `bt` int, rowid2, \"a\"\"b\")" == "create-table t [key:; action:int; replace:text; temp:; quoted ident:int; br:int; bt:int; rowid2:; a\"b:] [] sql=CREATE TABLE t(key, action int, replace text, temp, \"quoted ident\" int, [br] int, `bt` int, rowid2, \"a\"\"b\")"
#guard p1 "create table left(a)" == "create-table left [a:] [] sql=CREATE TABLE left(a)"
#guard p1 "create table t(a int not null on conflict replace primary key desc on conflict abort)" == "create-table t [a:int pk desc nn] [] sql=CREATE TABLE t(a int not null on conflict replace primary key desc on conflict abort)"
#guard p1 "create table t(a, b, primary key(a autoincrement))" == "create-table t [a:; b:] [pk(a) ai] sql=CREATE TABLE t(a, b, primary key(a autoincrement))"
#guard p1 "create table t(a int generated always as (1))" == "ERR 21 lean-sqlite: unsupported: generated columns"
#guard p1 "create table t(a int, primary key(a), b int)" == "ERR 38 near \"b\": syntax error"
#guard p1 "create table t()" == "ERR 15 near \")\": syntax error"
#guard p1 "create table t(a int default +'x', b int default - 5, c int default -9223372036854775808, d not deferrable)" == "create-table t [a:int default 'x'; b:int default (neg 5); c:int default -9223372036854775808; d:] [] sql=CREATE TABLE t(a int default +'x', b int default - 5, c int default -9223372036854775808, d not deferrable)"
#guard p1 "create table t(a int references u(b,c) on delete set null on update cascade match full deferrable initially deferred)" == "create-table t [a:int] [] sql=CREATE TABLE t(a int references u(b,c) on delete set null on update cascade match full deferrable initially deferred)"
#guard p1 "create table t(a) without rowid, strict" == "create-table t [a:] [strict] without-rowid sql=CREATE TABLE t(a) without rowid, strict"
#guard p1 "create table t(a) strict strict" == "ERR 25 near \"strict\": syntax error"
#guard p1 "drop table if exists t" == "drop-table t ie"
#guard p1 "drop index i" == "drop-index i"
#guard p1 "drop view if exists v" == "drop-view v ie"
#guard p1 "insert or replace into t(a,b) values (1,'x'),(2,'y')" == "insert-replace t (a,b) values (1 'x') (2 'y')"
#guard p1 "insert into t select * from u" == "insert-abort t () { select * from u}"
#guard p1 "insert into t default values" == "insert-abort t () defaults"
#guard p1 "replace into t values(1)" == "insert-replace t () values (1)"
#guard p1 "insert into t values (1+1, -3, 'a'||'b', null, x'', (select 5))" == "insert-abort t () values ((add 1 1) (neg 3) (concat 'a' 'b') NULL x0 ({ select 5 <5>}))"
#guard p1 "insert into t(a) select 1 union select 2" == "insert-abort t (a) { select 1 <1> union select 2 <2>}"
#guard p1 "update or ignore t set a=1, b=b+1 where c" == "update-ignore t set a=1 b=(add b 1) where c"
#guard p1 "delete from t where a=1" == "delete t where (eq a 1)"
#guard p1 "delete from main.t as x" == "delete \x00main\x00t"
#guard p1 "begin immediate transaction" == "begin"
#guard p1 "begin" == "begin"
#guard p1 "commit" == "commit"
#guard p1 "end transaction" == "commit"
#guard p1 "rollback" == "rollback"
#guard p1 "pragma journal_mode=wal" == "pragma journal_mode=wal"
#guard p1 "pragma table_info(t)" == "pragma table_info=t"
#guard p1 "pragma cache_size = -2000" == "pragma cache_size=-2000"
#guard p1 "pragma foo = on" == "pragma foo=on"
#guard p1 "pragma main.synchronous = off" == "pragma synchronous=off"
#guard p1 "pragma foo = 'x'" == "pragma foo=x"
#guard p1 "pragma foo" == "pragma foo"
#guard p1 "alter table t rename to u" == "rename t u"
#guard p1 "alter table t add column c int default 5 ;" == "add-column t c:int default 5 text=c int default 5"
#guard p1 "alter table t add d" == "add-column t d: text=d"
#guard p1 "alter table t add column  c  text   default 1  /*z*/ ;" == "add-column t c:text default 1 text=c  text   default 1  /*z*/"
#guard p1 "vacuum" == "vacuum"
#guard p1 "insert into t values(1) returning a" == "insert-abort t () values (1) returning a <a>"
#guard p1 "selec 1" == "ERR 0 near \"selec\": syntax error"
#guard p1 "select 1 +" == "ERR 10 incomplete input"
#guard p1 "select 1 + ;" == "ERR 11 near \";\": syntax error"
#guard p1 "select 'abc" == "ERR 7 unrecognized token: \"'abc\""
#guard p1 "select \"abc" == "ERR 7 unrecognized token: \"\"abc\""
#guard p1 "select [abc" == "ERR 7 unrecognized token: \"[abc\""
#guard p1 "select 0x;" == "ERR 7 unrecognized token: \"0x\""
#guard p1 "select 0xFFFFFFFFFFFFFFFFF" == "ERR 7 hex literal too big: 0xFFFFFFFFFFFFFFFFF"
#guard p1 "select * from" == "ERR 13 incomplete input"
#guard p1 "select from t" == "ERR 7 near \"from\": syntax error"
#guard p1 "create table t(" == "ERR 15 incomplete input"
#guard p1 "create table t(a,)" == "ERR 17 near \")\": syntax error"
#guard p1 "insert into t values(1," == "ERR 23 incomplete input"
#guard p1 "select 1 2" == "ERR 9 near \"2\": syntax error"
#guard p1 "select #" == "ERR 7 unrecognized token: \"#\""
#guard p1 "select 1 from t where" == "ERR 21 incomplete input"
#guard p1 "create tabl t(a)" == "ERR 7 near \"tabl\": syntax error"
#guard p1 "select (1" == "ERR 9 incomplete input"
#guard p1 "select 1)" == "ERR 8 near \")\": syntax error"
#guard p1 "drop table" == "ERR 10 incomplete input"
#guard p1 "select x'0g'" == "ERR 7 unrecognized token: \"x'0g'\""
#guard p1 "select 1 !" == "ERR 9 unrecognized token: \"!\""
#guard p1 "select a b c from t" == "ERR 11 near \"c\": syntax error"
#guard p1 "select 1 limit" == "ERR 14 incomplete input"
#guard p1 "update t set" == "ERR 12 incomplete input"
#guard p1 "delete t" == "ERR 7 near \"t\": syntax error"
#guard p1 "select case when 1 end" == "ERR 19 near \"end\": syntax error"
#guard p1 "pragma" == "ERR 6 incomplete input"
#guard p1 "begin begin" == "ERR 6 near \"begin\": syntax error"
#guard p1 "select 1__0" == "ERR 7 unrecognized token: \"1__0\""
#guard p1 "select 1_" == "ERR 7 unrecognized token: \"1_\""
#guard p1 "select 1abc" == "ERR 7 unrecognized token: \"1abc\""
#guard p1 "select x'abc'" == "ERR 7 unrecognized token: \"x'abc'\""
#guard p1 "select 1_000a" == "ERR 7 unrecognized token: \"1_000a\""
#guard p1 "select 1e" == "ERR 7 unrecognized token: \"1e\""
#guard p1 "select 1.e" == "ERR 7 unrecognized token: \"1.e\""
#guard p1 "select 0x_1" == "ERR 7 unrecognized token: \"0x_1\""
#guard p1 "create table t(a int, unique (a,))" == "ERR 32 near \")\": syntax error"
#guard p1 "create index i on t()" == "ERR 20 near \")\": syntax error"
#guard p1 "select 1 from t where a in (select 1 union select 2) x y" == "ERR 53 near \"x\": syntax error"
#guard p1 "" == "none"
#guard p1 "  -- c\n /* x */ " == "none"
#guard p1 ";;" == "none"
#guard p1 " ; ; " == "none"

/-! ## Statement ends and scripts -/
#guard endPos "select 1; select 2" 0 == "{ select 1 <1>} @9"
#guard endPos "select 1; select 2" 9 == "{ select 2 <2>} @18"
#guard endPos "select 1; select 2" 18 == "none"
#guard endPos ";;; select 1 ;; select 2;" 0 == "{ select 1 <1>} @14"
#guard endPos "select 1;select" 9 == "ERR 15 incomplete input"
#guard endPos "select 'é'; select 2" 0 == "{ select 'é' <'é'>} @12"
#guard endPos "select 1 /* c */ ; -- x\n select 2" 0 == "{ select 1 <1>} @18"
#guard endPos "begin; insert into t values(1); commit;" 6 == "insert-abort t () values (1) @31"
#guard endPos "begin; insert into t values(1); commit;" 0 == "begin @6"
#guard endPos "select 1; select 2" 3 == "ERR 3 near \"ect\": syntax error"

/-! ## isComplete -/
#guard isComplete "select 1;"
#guard isComplete "select 1; -- c"
#guard isComplete "select 1; /* c */  \n"
#guard !isComplete "select 1"
#guard !isComplete ""
#guard !isComplete "select 1; select 2"
#guard !isComplete "select ';"
#guard !isComplete "select 1; /* open"
#guard isComplete ";"

/-! ## Literals -/
#guard pe "9223372036854775807" == "9223372036854775807"
#guard pe "-9223372036854775808" == "-9223372036854775808"
#guard pe "9223372036854775808" == "r9223372036854775808.000000"
#guard pe "1e5" == "r100000.000000"
#guard pe "'a''b'" == "'a'b'"
#guard pe "\"a\"" == "\"a\""
#guard pe "t.\"a\"" == "t.a"
#guard pe "x'00ff'" == "x2"
#guard pe "NULL" == "NULL"
#guard pe "TRUE" == "1"
#guard pe "a is not distinct from b" == "(is a b)"

-- NATURAL JOIN, multi-column SET, WITH ... INSERT, savepoints, INDEXED BY (added after the first version of this file)
#guard p1 "select 1 from t natural join u" == "{ select 1 <1> from t inner-join u using(*)}"
#guard p1 "update t set (a,b)=(1,2)" == "update-abort t set a=1 b=2"
#guard p1 "with t as (select 1) insert into x select * from t" == "insert-abort x () {with t()={ select 1 <1>} select * from t}"
#guard p1 "savepoint s1; release s1" == "savepoint s1"
#guard p1 "release savepoint s1" == "release s1"
#guard p1 "rollback to savepoint s1" == "rollback-to s1"
#guard p1 "select * from t indexed by i where a = 1" == "{ select * from t where (eq a 1)}"
#guard p1 "reindex t" == "reindex"
#guard p1 "select * from json_each('[1,2]') j" == "{ select * from json_each('[1,2]') as j}"
#guard p1 "select * from pragma_table_info(t.name)" == "{ select * from pragma_table_info(t.name)}"

/-! ## Joins, row values, windows, RAISE, upserts, triggers (error texts and shapes checked against sqlite3 3.54) -/
#guard p1 "select (1,2), (a,b)=(1,2), (a,b) < (c,d), (a,b) in (select x,y from t), (a,b) in ((1,2),(3,4)), (a,b) between (1,2) and (3,4), (select 1), (3), ((1,2),3)" == "{ select (row 1 2) <(1,2)> (eq (row a b) (row 1 2)) <(a,b)=(1,2)> (lt (row a b) (row c d)) <(a,b) < (c,d)> (in (row a b) { select x <x> y <y> from t}) <(a,b) in (select x,y from t)> (in (row a b) [(row 1 2) (row 3 4)]) <(a,b) in ((1,2),(3,4))> (between (row a b) (row 1 2) (row 3 4)) <(a,b) between (1,2) and (3,4)> ({ select 1 <1>}) <(select 1)> 3 <(3)> (row (row 1 2) 3) <((1,2),3)>}"
#guard p1 "select (1,)" == "ERR 10 near \")\": syntax error"
#guard p1 "select (,1)" == "ERR 8 near \",\": syntax error"
#guard p1 "select (1,2" == "ERR 11 incomplete input"
#guard p1 "select * from a right join b on 1 right outer join c on 2 full join d using(x) full outer join e on 3" == "{ select * from a right-join b on 1  right-join c on 2  full-join d using(x)  full-join e on 3}"
#guard p1 "select * from a natural right join b natural full outer join c natural left outer join d natural cross join e natural inner join f" == "{ select * from a right-join b using(*)  full-join c using(*)  left-join d using(*)  inner-join e using(*)  inner-join f using(*)}"
#guard p1 "select * from a natural right join b on 1" == "ERR 37 a NATURAL join may not have an ON or USING clause"
#guard p1 "select * from a outer join b" == "ERR 16 unknown join type: outer"
#guard p1 "select * from a left cross join b" == "ERR 16 unknown join type: left cross"
#guard p1 "select * from a natural left foo join b" == "ERR 16 unknown join type: natural left foo"
#guard p1 "select * from a right outer b" == "ERR 29 incomplete input"
#guard p1 "select 1 from t on 1" == "ERR 16 a JOIN clause is required before ON"
#guard p1 "select 1 from t using (a)" == "ERR 16 a JOIN clause is required before USING"
#guard p1 "select * from a natural left left join b" == "{ select * from a left-join b using(*)}"
#guard p1 "select sum(a) over () from t" == "{ select (sum a over [-]) <sum(a) over ()> from t}"
#guard p1 "select sum(a) over (partition by b, c order by d desc nulls first, e rows between unbounded preceding and current row exclude ties) from t" == "{ select (sum a over [part b c order d desc nf e rows unb-prec..cur ties]) <sum(a) over (partition by b, c order by d desc nulls first, e rows between unbounded preceding and current row exclude ties)> from t}"
#guard p1 "select count(*) over (range 2 preceding), sum(distinct a) from t" == "ERR 39 RANGE with offset PRECEDING/FOLLOWING requires one ORDER BY expression"
#guard p1 "select sum(a) filter (where b > 1) over (groups between 1 preceding and 2 following exclude no others), row_number() over w from t window w as (order by a)" == "{ select (sum a filter (gt b 1) over [groups 1-prec..2-foll noOthers]) <sum(a) filter (where b > 1) over (groups between 1 preceding and 2 following exclude no others)> (row_number over [order a -]) <row_number() over w> from t}"
#guard p1 "select sum(a) over w2, sum(a) over (w1 rows 1 preceding) from t window w1 as (partition by x order by y), w2 as (w1 range current row)" == "{ select (sum a over [part x order y range cur..cur noOthers]) <sum(a) over w2> (sum a over [part x order y rows 1-prec..cur noOthers]) <sum(a) over (w1 rows 1 preceding)> from t}"
#guard p1 "select sum(a) over w from t" == "ERR 19 no such window: w"
#guard p1 "select sum(a) over (w) from t window w as (order by a rows 1 preceding)" == "ERR 20 cannot override frame specification of window: w"
#guard p1 "select sum(a) over (w order by b) from t window w as (order by a)" == "ERR 20 cannot override ORDER BY clause of window: w"
#guard p1 "select sum(a) over (w partition by b) from t window w as (order by a)" == "ERR 20 cannot override PARTITION clause of window: w"
#guard p1 "select sum(a) over (x) from t window w as (order by a)" == "ERR 20 no such window: x"
#guard p1 "select sum(a) over x from t window w as (x)" == "ERR 41 no such window: x"
#guard p1 "select 1 from t window w as (order by a), v as (w order by b)" == "ERR 48 cannot override ORDER BY clause of window: w"
#guard p1 "select sum(a) over (rows between current row and 1 preceding) from t" == "ERR 20 unsupported frame specification"
#guard p1 "select sum(a) over (rows 1 following) from t" == "ERR 20 unsupported frame specification"
#guard p1 "select sum(a) over (rows between unbounded following and current row) from t" == "ERR 43 near \"following\": syntax error"
#guard p1 "select sum(a) over (range between 1 preceding and current row) from t" == "ERR 61 RANGE with offset PRECEDING/FOLLOWING requires one ORDER BY expression"
#guard p1 "select sum(a) over (order by a, b range between 1 preceding and current row) from t" == "ERR 75 RANGE with offset PRECEDING/FOLLOWING requires one ORDER BY expression"
#guard p1 "select sum(a) over (order by a range between 1 preceding and current row) from t" == "{ select (sum a over [order a range 1-prec..cur noOthers]) <sum(a) over (order by a range between 1 preceding and current row)> from t}"
#guard p1 "select sum(distinct a) over () from t" == "ERR 23 DISTINCT is not supported for window functions"
#guard p1 "select row_number() filter (where 1) over () from t" == "ERR 20 FILTER clause may only be used with aggregate window functions"
#guard !(p1 "select sum(a) filter (where 1) from t").startsWith "ERR"
#guard p1 "select sum(a) over (partition by) from t" == "ERR 32 near \")\": syntax error"
#guard p1 "select sum(a) over (exclude ties) from t" == "ERR 28 near \"ties\": syntax error"
#guard p1 "select sum(a) over (rows 1 preceding exclude no) from t" == "ERR 47 near \")\": syntax error"
#guard p1 "select sum(a) over x from t window x" == "ERR 19 no such window: x"
#guard p1 "select 1 window w as (order by a) window v as ()" == "ERR 34 near \"window\": syntax error"
#guard p1 "select sum(a) over w, (select max(b) over w from u) from t window w as (order by x)" == "ERR 42 no such window: w"
#guard p1 "select (select max(b) over w from u window w as (order by y)) from t" == "{ select ({ select (max b over [order y -]) <max(b) over w> from u}) <(select max(b) over w from u window w as (order by y))> from t}"
#guard p1 "select a from t window w as (partition by 1) union select sum(b) over w from u window w as (order by 2)" == "{ select a <a> from t union select (sum b over [order 2 -]) <sum(b) over w> from u}"
#guard p1 "select sum(a) over \"w\" from t window [w] as (order by a)" == "{ select (sum a over [order a -]) <sum(a) over \"w\"> from t}"
#guard p1 "select sum(a) over W from t window w as (order by a)" == "{ select (sum a over [order a -]) <sum(a) over W> from t}"
#guard p1 "select sum(a) over (unbounded) from t" == "ERR 20 no such window: unbounded"
#guard p1 "select sum(a) over (rows unbounded preceding) from t" == "{ select (sum a over [rows unb-prec..cur noOthers]) <sum(a) over (rows unbounded preceding)> from t}"
#guard p1 "select raise(ignore), raise(rollback,'a'), raise(abort,'b'), raise(fail,'c')" == "{ select (raise ignore) <raise(ignore)> (raise rollback 'a') <raise(rollback,'a')> (raise abort 'b') <raise(abort,'b')> (raise fail 'c') <raise(fail,'c')>}"
#guard p1 "select raise(abort)" == "ERR 18 near \")\": syntax error"
#guard p1 "select raise(foo,'x')" == "ERR 13 near \"foo\": syntax error"
#guard p1 "select raise(abort, 1)" == "ERR 20 lean-sqlite: unsupported: RAISE with a message that is not a string literal"
#guard p1 "select raise from t" == "{ select raise <raise> from t}"
#guard p1 "insert into t values(1,2) on conflict do nothing" == "insert-abort t () values (1 2) on-conflict() do-nothing"
#guard p1 "insert into t values(1,2) on conflict(a) do nothing on conflict (b collate nocase desc) where b>1 do update set a=excluded.a, (b,c)=(1,2) where a=1 on conflict do update set x=1" == "insert-abort t () values (1 2) on-conflict(a) do-nothing  on-conflict(b collate nocase desc) where (gt b 1) do-update a=excluded.a b=1 c=2 where (eq a 1)  on-conflict() do-update x=1"
#guard p1 "insert into t values(1) on conflict do update set a=1 where b on conflict do nothing" == "ERR 62 near \"on\": syntax error"
#guard p1 "insert into t select 1,2 on conflict do nothing" == "insert-abort t () { select 1 <1> 2 <2>} on-conflict() do-nothing"
#guard p1 "insert into t select 1,2 where true on conflict(a) do update set b=1" == "insert-abort t () { select 1 <1> 2 <2> where 1} on-conflict(a) do-update b=1"
#guard p1 "insert into t select 1,2 from u on conflict do nothing" == "ERR 44 near \"do\": syntax error"
#guard p1 "insert into t select 1,2 from u join v on 1 on conflict do nothing" == "insert-abort t () { select 1 <1> 2 <2> from u inner-join v on 1} on-conflict() do-nothing"
#guard p1 "insert into t select 1,2 from u join v where 1 on conflict do nothing" == "insert-abort t () { select 1 <1> 2 <2> from u inner-join v where 1} on-conflict() do-nothing"
#guard p1 "insert into t default values on conflict do nothing" == "ERR 29 near \"on\": syntax error"
#guard p1 "insert into t values(1,2) on conflict" == "ERR 37 incomplete input"
#guard p1 "insert into t values(1,2) on conflict do" == "ERR 40 incomplete input"
#guard p1 "insert into t values(1,2) on conflict do update" == "ERR 47 incomplete input"
#guard p1 "insert into t values(1,2) on conflict do update set" == "ERR 51 incomplete input"
#guard p1 "insert into t values(1,2) on conflict (a)" == "ERR 41 incomplete input"
#guard p1 "insert into t values(1,2) on conflict do nothing returning a, a+1 as z" == "insert-abort t () values (1 2) on-conflict() do-nothing returning a <a> (add a 1) as z <a+1>"
#guard p1 "insert or replace into t values(1) on conflict (a) do nothing" == "insert-replace t () values (1) on-conflict(a) do-nothing"
#guard p1 "with c as (select 1) insert into t select * from c on conflict do nothing" == "ERR 63 near \"do\": syntax error"
#guard p1 "with c as (select 1) insert into t values (1) on conflict do nothing" == "insert-abort t () {with c()={ select 1 <1>} values (1)} on-conflict() do-nothing"
#guard p1 "update t set a=1 on conflict do nothing" == "ERR 17 near \"on\": syntax error"
#guard p1 "delete from t on conflict" == "ERR 14 near \"on\": syntax error"
#guard p1 "insert into t values(1) on conflict do update set (a,b)=(select 1,2)" == "ERR 57 lean-sqlite: unsupported: SET (columns) = (SELECT ...)"
#guard p1 "create trigger  tr after insert on t for each row when new.a>1 begin select 1; update t set a=2 where b=1;  end" == "create-trigger tr after insert on t when (gt new.a 1) body=[{ select 1 <1>}; update-abort t set a=2 where (eq b 1)] sql=CREATE TRIGGER tr after insert on t for each row when new.a>1 begin select 1; update t set a=2 where b=1;  end"
#guard p1 "create temp trigger if not exists tr instead of update of a, b on v begin select raise(ignore); end -- c\n" == "temp(create-trigger tr ine insteadOf update(a,b) on v body=[{ select (raise ignore) <raise(ignore)>}] sql=CREATE TRIGGER tr instead of update of a, b on v begin select raise(ignore); end)"
#guard p1 "create trigger main.tr delete on t begin delete from t; insert into u values(1,2) on conflict do nothing; replace into u values(1); with c as (select 1) select * from c; values(1); end;" == "create-trigger tr before delete on t body=[delete t; insert-abort u () values (1 2) on-conflict() do-nothing; insert-replace u () values (1); {with c()={ select 1 <1>} select * from c}; { values (1)}] sql=CREATE TRIGGER tr delete on t begin delete from t; insert into u values(1,2) on conflict do nothing; replace into u values(1); with c as (select 1) select * from c; values(1); end"
#guard p1 "create trigger tr before insert on t begin end" == "ERR 43 near \"end\": syntax error"
#guard p1 "create trigger tr before insert on t begin select 1 end" == "ERR 55 incomplete input"
#guard p1 "create trigger tr before insert on t begin select 1; select 2 end" == "ERR 65 incomplete input"
#guard p1 "create trigger tr before insert on t begin select 1; create table x(a); end" == "ERR 53 near \"create\": syntax error"
#guard p1 "create trigger tr before insert on t begin select 1;; end" == "ERR 52 near \";\": syntax error"
#guard p1 "create trigger tr before insert on t begin select 1; end end" == "ERR 57 near \"end\": syntax error"
#guard p1 "create trigger tr before select on t begin select 1; end" == "ERR 25 near \"select\": syntax error"
#guard p1 "create trigger tr update of on t begin select 1; end" == "ERR 28 near \"on\": syntax error"
#guard p1 "create trigger tr after update on t for each statement begin select 1; end" == "ERR 45 near \"statement\": syntax error"
#guard p1 "create trigger tr after update on t when begin select 1; end" == "ERR 47 near \"select\": syntax error"
#guard p1 "create trigger tr update on t begin select 1;" == "ERR 45 incomplete input"
#guard p1 "create trigger tr update on t begin select 1; end;select 2" == "create-trigger tr before update() on t body=[{ select 1 <1>}] sql=CREATE TRIGGER tr update on t begin select 1; end"
#guard p1 "create trigger if not exists tr1 after delete on main.t begin select 1; END ;" == "create-trigger tr1 ine after delete on t body=[{ select 1 <1>}] sql=CREATE TRIGGER tr1 after delete on main.t begin select 1; END"
#guard p1 "drop trigger if exists tr" == "drop-trigger tr ie"
#guard p1 "drop trigger x.tr" == "drop-trigger tr"
#guard p1 "drop trigger" == "ERR 12 incomplete input"
#guard p1 "drop trigger x.y.z" == "ERR 16 near \".\": syntax error"
#guard p1 "select count(*) filter from t" == "{ select (count*) as filter <count(*)> from t}"
#guard p1 "select 1 window from t" == "{ select 1 as window <1> from t}"
#guard p1 "select 1 over" == "{ select 1 as over <1>}"
#guard p1 "select count(*) over from t" == "{ select (count*) as over <count(*)> from t}"
#guard p1 "create table filter(over, window)" == "create-table filter [over:; window:] [] sql=CREATE TABLE filter(over, window)"
#guard p1 "select * from (select 1) on conflict" == "ERR 25 a JOIN clause is required before ON"
#guard p1 "select 1 from t window w as (order by a) order by 1" == "{ select 1 <1> from t order 1}"
#guard p1 "select first_value(a) filter (where 1) over () from t" == "ERR 22 FILTER clause may only be used with aggregate window functions"
#guard p1 "select sum(a) over (order by a) = 1, sum(a) over (rows 1 preceding) + 1 from t" == "{ select (eq (sum a over [order a -]) 1) <sum(a) over (order by a) = 1> (add (sum a over [rows 1-prec..cur noOthers]) 1) <sum(a) over (rows 1 preceding) + 1> from t}"
#guard p1 "select sum(a) over \"w\" from t window w as (partition by 1)" == "{ select (sum a over [part 1 -]) <sum(a) over \"w\"> from t}"

/-! ## isComplete with CREATE TRIGGER (sqlite3_complete) -/
#guard !isComplete "create trigger t after insert on x begin select 1;"
#guard !isComplete "create trigger t after insert on x begin select 1; end"
#guard isComplete "create trigger t after insert on x begin select 1; end;"
#guard isComplete "create trigger t after insert on x begin select 1; end; -- c"
#guard !isComplete "create trigger t after insert on x begin select 1; end; select 2"
#guard p1 "insert into t select 1 returning *" == "insert-abort t () { select 1 <1>} returning *"
#guard p1 "update t set a=1 where b returning t.*, a x" == "update-abort t set a=1 where b returning t.* a as x <a>"
#guard p1 "delete from t returning a" == "delete t returning a <a>"
#guard p1 "with c as (select 9) insert into t select * from c returning a" == "insert-abort t () {with c()={ select 9 <9>} select * from c} returning a <a>"
#guard p1 "insert into t values(1) returning" == "ERR 33 incomplete input"
#guard p1 "insert into t values(1) returning a," == "ERR 36 incomplete input"
#guard p1 "update t set a=1 returning a returning a" == "ERR 29 near \"returning\": syntax error"
#guard p1 "create trigger tr after insert on m begin insert into t values(1) returning a; end" == "ERR 66 cannot use RETURNING in a trigger"
#guard p1 "alter table t rename column a to b" == "rename-column t a b"
#guard p1 "alter table t rename a to b" == "rename-column t a b"
#guard p1 "alter table t drop column c" == "drop-column t c"
#guard p1 "alter table t drop c;" == "drop-column t c"
#guard p1 "alter table t rename column to b" == "ERR 28 near \"to\": syntax error"
#guard p1 "alter table t rename column a;" == "ERR 29 near \";\": syntax error"
#guard p1 "alter table t drop;" == "ERR 18 near \";\": syntax error"
#guard p1 "alter table t drop column a b;" == "ERR 28 near \"b\": syntax error"
#guard p1 "create index i on t(a collate nocase asc, (a+1) desc, abs(a) collate binary, a||b)" == "create-index i on t (a collate nocase,(a+1){(add a 1)} desc,abs(a) collate binary{(abs a)} collate binary,a||b{(concat a b)}) sql=CREATE INDEX i on t(a collate nocase asc, (a+1) desc, abs(a) collate binary, a||b)"
#guard p1 "create index i on t(abs(a)) where a>1" == "create-index i on t (abs(a){(abs a)}) where (gt a 1) sql=CREATE INDEX i on t(abs(a)) where a>1"
#guard p1 "create index i on t(a+1, )" == "ERR 25 near \")\": syntax error"
#guard p1 "create index i on t(a+1 b)" == "ERR 24 near \"b\": syntax error"
#guard p1 "create table u(a, primary key(a+1))" == "ERR 30 expressions prohibited in PRIMARY KEY and UNIQUE constraints"
#guard p1 "create table u(a, unique(a collate nocase, abs(a)))" == "ERR 43 expressions prohibited in PRIMARY KEY and UNIQUE constraints"
#guard p1 "insert into t values(1) on conflict(a+1) do nothing" == "insert-abort t () values (1) on-conflict(a+1{(add a 1)}) do-nothing"
#guard p1 "create temporary table t(a)" == "temp(create-table t [a:] [] sql=CREATE TABLE t(a))"
#guard p1 "create table temp.x(a)" == "temp(create-table x [a:] [] sql=CREATE TABLE x(a))"
#guard p1 "create temp table temp.x(a)" == "temp(create-table x [a:] [] sql=CREATE TABLE x(a))"
#guard p1 "create temp table if not exists temp.x as select 1" == "temp(create-table-as x ine { select 1 <1>})"
#guard p1 "create temp view v as select 1" == "temp(create-view v() { select 1 <1>} sql=CREATE VIEW v as select 1)"
#guard p1 "create view temp.v as select 1" == "temp(create-view v() { select 1 <1>} sql=CREATE VIEW v as select 1)"
#guard p1 "create temp trigger tr after insert on m begin select 1; end" == "temp(create-trigger tr after insert on m body=[{ select 1 <1>}] sql=CREATE TRIGGER tr after insert on m begin select 1; end)"
#guard p1 "create trigger temp.tr after insert on m begin select 1; end" == "temp(create-trigger tr after insert on m body=[{ select 1 <1>}] sql=CREATE TRIGGER tr after insert on m begin select 1; end)"
#guard p1 "create temp table main.x(a)" == "ERR 18 temporary table name must be unqualified"
#guard p1 "create temp view main.x as select 1" == "ERR 17 temporary table name must be unqualified"
#guard p1 "create temp trigger main.tr after insert on m begin select 1; end" == "ERR 20 temporary trigger may not have qualified name"
#guard p1 "create temp index i on t(a)" == "ERR 12 near \"index\": syntax error"
#guard isComplete "create temp trigger t after
 insert on x begin select 1; select 2; end;"
#guard isComplete "create temporary trigger t after insert on x begin select 1; end;"
#guard isComplete "explain create trigger t after insert on x begin select 1; select 2; end;"
#guard !isComplete "explain create trigger t after insert on x begin select 1; select 2;"
#guard isComplete "create trigger t after insert on x begin select 1; end; select 2;"
#guard !isComplete "create trigger t after insert on x begin select 1; select 'end;"
#guard isComplete "create table t(a); create index i on t(a);"
#guard isComplete "create table trigger(a);"
#guard !isComplete "create view v as select 1; create trigger t after insert on x begin select 1;"
-- quoted names, blobs, numbers and parameters are one token each: a `;` inside, or a keyword glued to them, does not count
#guard isComplete "select x'ab';" && !isComplete "select x'ab" && isComplete "select [a;b];" && !isComplete "select [a;"
#guard isComplete "select 'a''b;';" && !isComplete "select `a;" && isComplete "select :a, ?1, $b, 1e5, .5, 0x1f;"
#guard !isComplete "create trigger t after insert on x begin select 1; 1end;" && isComplete "create trigger t after insert on x begin select 1; end;"
#guard isComplete "select 1 end;"
#guard !isComplete "select 1; end"
#guard isComplete "create trigger t after insert on x begin select 1; /* c */ end /* d */ ; -- e"
#guard !isComplete "create trigger t after insert on x begin select 1; \"end\";"

/-! ## Triggers across statements -/
#guard endPos "create trigger t after insert on x begin select 1; select 2; end; select 3" 0 == "create-trigger t after insert on x body=[{ select 1 <1>}; { select 2 <2>}] sql=CREATE TRIGGER t after insert on x begin select 1; select 2; end @65"
#guard endPos "create trigger t after insert on x begin select 1; select 2; end; select 3" 65 == "{ select 3 <3>} @74"
#guard endPos "create trigger t after insert on x begin select 1; end end" 0 == "ERR 55 near \"end\": syntax error"

end TestParse

