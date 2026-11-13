import SwarmLean.Proofs.Store

/-! The migrations (board #134): `connect` runs each of `migs` the db needs, in order (Real.lean). Each takes a db at
schema version n (`AtVersion`) to version n+1, keeps every cell the db had (but a NULL task.deps the after migration
fills), and is idempotent; all of them take any db at version 0 to the last version, where they change nothing. -/

namespace SwarmLean
open Sqlite (Val)

/-- Migration `m` as `connect` runs it: when the columns `pragma table_info` reads say the db needs it. -/
def Sql.migrate (S : Sql) (m : Stmt) (db : SDb) : Option SDb :=
  if m.needed (S.tableInfo db) then S.exec m db else some db

/-- `connect`'s migrations: each of `ms` in turn. -/
def Sql.migrateAll (S : Sql) : List Stmt → SDb → Option SDb
  | [], db => some db
  | m :: ms, db => (S.migrate m db).bind (S.migrateAll ms)

/-- The columns of each table. -/
def SDb.cols (db : SDb) : String → List String := fun t => (db t).cols

/-- The tables the migrations touch each have a column other than after, and none twice. -/
def Tidy (db : SDb) : Prop := ∀ t ∈ migTables, (∃ c ∈ (db t).cols, c ≠ "after") ∧ (db t).cols.Nodup

/-- `db` is at schema version `n`: tidy, and needing none of the first `n` migrations. -/
def AtVersion (db : SDb) (n : Nat) : Prop := Tidy db ∧ ∀ m ∈ migs.take n, m.needed db.cols = false

/-- No task.after cell holds a float (the after migration copies it into deps). -/
def AfterOk (db : SDb) : Prop := ∀ r ∈ (db "task").rows, (r "after").cls ≠ 2

/-- Every cell in a column `db` had stays in `db'` (rows mapped one to one), but a NULL task.deps. -/
def Keeps (db db' : SDb) : Prop := ∀ u, ∃ f, (db' u).rows = (db u).rows.map f ∧
  ∀ r c, c ∈ (db u).cols → (u ≠ "task" ∨ c ≠ "deps" ∨ (r "deps").cls ≠ 0) → f r c = r c

theorem cols_ne_after : ∀ p ∈ columns, colName p.2 ≠ "after" := by decide
theorem cols_tables : ∀ p ∈ columns, p.1 ∈ migTables := by decide

theorem mem_migs {m : Stmt} (h : m ∈ migs) : (∃ p ∈ columns, m = .addCol p.1 p.2) ∨ m = .dropAfter := by
  simp only [migs, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with ⟨p, hp, rfl⟩ | rfl
  · exact Or.inl ⟨p, hp, rfl⟩
  · exact Or.inr rfl

theorem Keeps.refl (db : SDb) : Keeps db db := fun _ => ⟨id, by simp, fun _ _ _ _ => rfl⟩

/-- One migration of `migs` on a tidy db whose `done` it does not need: it runs, leaves the db tidy, needing neither
`done` nor itself, keeps every cell, and run again changes nothing. -/
theorem migrate_step (S : Sql) (hS : SqlExec S) (hI : SqlTableInfo S) {m : Stmt} (hm : m ∈ migs) {db : SDb}
    (ht : Tidy db) (ha : AfterOk db) {done : List Stmt} (hdm : ∀ m' ∈ done, m' ∈ migs)
    (hd : ∀ m' ∈ done, m'.needed db.cols = false) :
    ∃ db', S.migrate m db = some db' ∧ Tidy db' ∧ AfterOk db' ∧ (∀ m' ∈ done ++ [m], m'.needed db'.cols = false) ∧
      S.migrate m db' = some db' ∧ Keeps db db' := by
  have hcols : S.tableInfo = fun d => d.cols := by funext d t; exact hI d t
  by_cases hn' : m.needed db.cols = false
  · refine ⟨db, by simp [Sql.migrate, hcols, hn'], ht, ha, ?_, by simp [Sql.migrate, hcols, hn'], Keeps.refl db⟩
    intro m' hm'; rcases List.mem_append.mp hm' with h | h
    · exact hd m' h
    · simp at h; subst h; exact hn'
  have hn : m.needed db.cols = true := by simpa using hn'
  rcases mem_migs hm with ⟨⟨t, d⟩, hp, rfl⟩ | rfl
  · -- add column `d` to `t`
    have hc : colName d ∉ (db t).cols := by simpa [Stmt.needed, SDb.cols] using hn
    have hca : colName d ≠ "after" := cols_ne_after _ hp
    obtain ⟨⟨c₀, hc₀, -⟩, -⟩ := ht t (cols_tables _ hp)
    have hne : (db t).cols.isEmpty = false := by
      cases h : (db t).cols with
      | nil => simp [h] at hc₀
      | cons _ _ => rfl
    have hcont : (db t).cols.contains (colName d) = false := by simpa using hc
    let v := declDefault d
    let tx := if (d.splitOn " ")[1]? == some "text" then (db t).text ++ [colName d] else (db t).text
    let rs := (db t).rows.map (fun r => setCells r [colName d] [v])
    let db' := db.set t
      { db t with
        cols := (db t).cols ++ [colName d], text := tx, dflt := setCells (db t).dflt [colName d] [v], rows := rs }
    have hrun : S.migrate (.addCol t d) db = some db' := by
      simp only [Sql.migrate, hcols, hn, ite_true]
      rw [hS _ _ (by simp only [Stmt.Pre]; exact hp)]; simp [Stmt.run, hne, hc, db', v, tx, rs]
    have hcols' : ∀ u, (db' u).cols = if u = t then (db t).cols ++ [colName d] else (db u).cols := by
      intro u; by_cases hu : u = t <;> simp [db', SDb.set, hu]
    have hsub : ∀ u c, c ∈ (db u).cols → c ∈ (db' u).cols := by
      intro u c h; rw [hcols']; split <;> simp_all
    refine ⟨db', hrun, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨⟨c, h1, h2⟩, h3⟩ := ht u hu
      refine ⟨⟨c, hsub u c h1, h2⟩, ?_⟩
      rw [hcols']; split
      · subst_vars
        exact List.nodup_append.mpr ⟨h3, by simp, fun a ha b hb e => hc (by simp at hb; rw [← hb, ← e]; exact ha)⟩
      · exact h3
    · intro r hr
      by_cases htk : t = "task"
      · subst htk
        simp only [db', rs, SDb.set_same, List.mem_map] at hr
        obtain ⟨r, hr, rfl⟩ := hr
        rw [setCells_other (by simpa using hca.symm)]; exact ha r hr
      · simp only [db', SDb.set, Ne.symm htk, ite_false] at hr; exact ha r hr
    · intro m' hm'
      rcases List.mem_append.mp hm' with h | h
      · have := hd m' h
        rcases mem_migs (hdm m' h) with ⟨⟨t', d'⟩, -, rfl⟩ | rfl
        · simp only [Stmt.needed, SDb.cols, Bool.not_eq_false', List.contains_iff_mem] at this ⊢
          exact hsub t' _ this
        · simp only [Stmt.needed, SDb.cols] at this ⊢
          have h1 : "after" ∉ (db "task").cols := by simpa using this
          rw [hcols']; split
          · subst_vars; simp [h1, Ne.symm hca]
          · exact this
      · simp at h; subst h
        simp only [Stmt.needed, SDb.cols, Bool.not_eq_false', List.contains_iff_mem, hcols']; simp
    · simp only [Sql.migrate, hcols]
      have : (Stmt.addCol t d).needed db'.cols = false := by
        simp only [Stmt.needed, SDb.cols, Bool.not_eq_false', List.contains_iff_mem, hcols']; simp
      simp [this]
    · intro u
      by_cases hu : u = t
      · subst hu
        refine ⟨fun r => setCells r [colName d] [v], by simp [db', rs], fun r c hc' _ => ?_⟩
        exact setCells_other (by simp; intro e; exact hc (e ▸ hc'))
      · exact ⟨id, by simp [db', SDb.set, hu], fun _ _ _ _ => rfl⟩
  · -- move task.after into a NULL deps, drop after
    have hin : "after" ∈ (db "task").cols := by simpa [Stmt.needed, SDb.cols] using hn
    have hcont : (db "task").cols.contains "after" = true := by simpa using hin
    obtain ⟨-, hnd⟩ := ht "task" (by decide)
    let T := db "task"
    let copy := fun (r : String → Val) => if T.text.contains "deps" then textAff (r "after") else r "after"
    let f := fun (r : String → Val) =>
      if (r "deps").cls == 0 && (r "after").cls != 0 then setCells r ["deps"] [copy r] else r
    let db' := db.set "task" { T with cols := T.cols.erase "after", rows := T.rows.map f }
    have hrun : S.migrate .dropAfter db = some db' := by
      simp only [Sql.migrate, hcols, hn, ite_true]
      rw [hS _ _ (by simp only [Stmt.Pre]; exact ha)]; simp [Stmt.run, hin, db', T, f, copy]
    have hcols' : ∀ u, (db' u).cols = if u = "task" then (db "task").cols.erase "after" else (db u).cols := by
      intro u; by_cases hu : u = "task" <;> simp [db', SDb.set, hu, T]
    have hafter : "after" ∉ (db' "task").cols := by rw [hcols']; simpa using hnd.not_mem_erase
    refine ⟨db', hrun, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨⟨c, h1, h2⟩, h3⟩ := ht u hu
      rw [hcols']; split
      · subst_vars; exact ⟨⟨c, (List.mem_erase_of_ne h2).mpr h1, h2⟩, h3.erase _⟩
      · exact ⟨⟨c, h1, h2⟩, h3⟩
    · intro r hr
      simp only [db', SDb.set_same, List.mem_map] at hr
      obtain ⟨r, hr, rfl⟩ := hr
      simp only [f]; split
      · rw [setCells_other (by simp)]; exact ha r hr
      · exact ha r hr
    · intro m' hm'
      rcases List.mem_append.mp hm' with h | h
      · rcases mem_migs (hdm m' h) with ⟨⟨t', d'⟩, hp', rfl⟩ | rfl
        · have := hd _ h
          simp only [Stmt.needed, SDb.cols, Bool.not_eq_false', List.contains_iff_mem] at this ⊢
          rw [hcols']; split
          · subst_vars; exact (List.mem_erase_of_ne (cols_ne_after _ hp')).mpr this
          · exact this
        · simpa [Stmt.needed, SDb.cols] using hafter
      · simp at h; subst h; simpa [Stmt.needed, SDb.cols] using hafter
    · have : Stmt.dropAfter.needed db'.cols = false := by simpa [Stmt.needed, SDb.cols] using hafter
      simp [Sql.migrate, hcols, this]
    · intro u
      by_cases hu : u = "task"
      · subst hu
        refine ⟨f, by simp [db', T], fun r c _ hdeps => ?_⟩
        simp only [f]; split
        · rename_i hcond
          rcases hdeps with h | h | h
          · exact absurd rfl h
          · exact setCells_other (by simpa using h)
          · simp at hcond; exact absurd hcond.1 h
        · rfl
      · exact ⟨id, by simp [db', SDb.set, hu], fun _ _ _ _ => rfl⟩

/-- Migration `n` takes a db at schema version `n` to version `n+1`, keeping every cell the db had (but a NULL
task.deps the after migration fills), and is idempotent: run again on what it left, it changes nothing. -/
theorem migrate_version (S : Sql) (hS : SqlExec S) (hI : SqlTableInfo S) {n : Nat} (hn : n < migs.length) {db : SDb}
    (hv : AtVersion db n) (ha : AfterOk db) :
    ∃ db', S.migrate migs[n] db = some db' ∧ AtVersion db' (n + 1) ∧ AfterOk db' ∧ Keeps db db' ∧
      S.migrate migs[n] db' = some db' := by
  obtain ⟨db', h1, h2, h3, h4, h5, h6⟩ := migrate_step S hS hI (List.getElem_mem hn) hv.1 ha
    (done := migs.take n) (fun _ h => List.mem_of_mem_take h) hv.2
  refine ⟨db', h1, ⟨h2, ?_⟩, h3, h6, h5⟩
  rw [List.take_add_one, List.getElem?_eq_getElem hn]; exact h4

/-- A db needing none of `ms` is left as it is by them. -/
theorem migrateAll_none (S : Sql) (hI : SqlTableInfo S) {db : SDb} {ms : List Stmt}
    (h : ∀ m ∈ ms, m.needed db.cols = false) : S.migrateAll ms db = some db := by
  have hcols : S.tableInfo = fun d => d.cols := by funext d t; exact hI d t
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [Sql.migrateAll, Sql.migrate, hcols]
    rw [h m (by simp)]
    simpa using ih fun m' hm' => h m' (List.mem_cons_of_mem _ hm')

/-- `connect`'s migrations take a db at any version `k` to the last, where they change nothing: run twice, they are
run once. -/
theorem migrateAll_last (S : Sql) (hS : SqlExec S) (hI : SqlTableInfo S) (k : Nat) {db : SDb} (hv : AtVersion db k)
    (ha : AfterOk db) :
    ∃ db', S.migrateAll (migs.drop k) db = some db' ∧ AtVersion db' migs.length ∧ S.migrateAll migs db' = some db' := by
  induction h : migs.length - k generalizing k db with
  | zero =>
    have hk : migs.drop k = [] := List.drop_eq_nil_of_le (by omega)
    have hv' : AtVersion db migs.length := ⟨hv.1, fun m hm => hv.2 m (by
      rw [List.take_of_length_le (by omega)]; simpa using List.mem_of_mem_take hm)⟩
    refine ⟨db, by simp [hk, Sql.migrateAll], hv', migrateAll_none S hI fun m hm => hv'.2 m (by simpa using hm)⟩
  | succ d ih =>
    have hk : k < migs.length := by omega
    obtain ⟨db₁, h1, hv₁, ha₁, -, -⟩ := migrate_version S hS hI hk hv ha
    obtain ⟨db', h2, hv', hid⟩ := ih (k + 1) hv₁ ha₁ (by omega)
    refine ⟨db', ?_, hv', hid⟩
    rw [List.drop_eq_getElem_cons hk, Sql.migrateAll, h1, Option.bind_some, h2]

end SwarmLean
