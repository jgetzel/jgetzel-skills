import LuaLean.Denote

/-! world.lua lifted by `lua-lean lift`: each function's parsed body, its shallow form, and the proof
that the two are the same. GENERATED: do not edit. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace World
open Lua


def chunk_body : Block :=
  [(.locfn "greet" ["name"] false 
  [(.call (.site ⟨"world.lua", 5, [], ("field", "write"), false⟩ (.call (.site ⟨"world.lua", 5, [("global", "io")], ("", ""), false⟩ (.index (.var "io") (.str "write".toList))) [(.str "hello, ".toList), (.var "name"), (.str "\n".toList)])))] (4, 6)), (.locfn "readings" [] false 
  [(.loc ["t0"] [(.site ⟨"world.lua", 9, [], ("field", "time"), false⟩ (.call (.site ⟨"world.lua", 9, [("global", "os")], ("", ""), false⟩ (.index (.var "os") (.str "time".toList))) []))]), (.loc ["t1"] [(.site ⟨"world.lua", 10, [], ("field", "time"), false⟩ (.call (.site ⟨"world.lua", 10, [("global", "os")], ("", ""), false⟩ (.index (.var "os") (.str "time".toList))) []))]), (.ret [(.var "t0"), (.var "t1")])] (8, 12)), (.ret [(.var "greet"), (.var "readings")])]

def greet_body : Block :=
  [(.call (.site ⟨"world.lua", 5, [], ("field", "write"), false⟩ (.call (.site ⟨"world.lua", 5, [("global", "io")], ("", ""), false⟩ (.index (.var "io") (.str "write".toList))) [(.str "hello, ".toList), (.var "name"), (.str "\n".toList)])))]

def readings_body : Block :=
  [(.loc ["t0"] [(.site ⟨"world.lua", 9, [], ("field", "time"), false⟩ (.call (.site ⟨"world.lua", 9, [("global", "os")], ("", ""), false⟩ (.index (.var "os") (.str "time".toList))) []))]), (.loc ["t1"] [(.site ⟨"world.lua", 10, [], ("field", "time"), false⟩ (.call (.site ⟨"world.lua", 10, [("global", "os")], ("", ""), false⟩ (.index (.var "os") (.str "time".toList))) []))]), (.ret [(.var "t0"), (.var "t1")])]

def chunk (I : Sem) (env0 : Env) (fn0 : Nat) : List Val → Nat → M (List Val) :=
  S.fn fn0 fun args n => S.letEnd ((S.block (S.qLocalFn "greet" ["name"] false greet_body (4, 6) (env0) fn0 fun c_greet =>
      (S.qLocalFn "readings" [] false readings_body (8, 12) (("greet", c_greet) :: env0) fn0 fun c_readings =>
      (S.qStat (S.sReturn (S.lCons (S.eCell c_greet) (S.lLast (S.mOne (S.eCell c_readings))))) (S.gotos [] [])
      S.qEnd)))) n)

theorem chunk_ok (I : Sem) (env0 : Env) (fn0 fenv0 : Nat) (src0 : List Char) (ln0 : Nat × Nat)
    (root0 : Option Nat) (ks0 : List (Nat × Nat))
    (h_io : env0.lookup "io" = none)
    (h_os : env0.lookup "os" = none) :
    CFn I (chunk I env0 fn0) fn0 ⟨[], true, chunk_body, env0, fenv0, src0, ln0, root0, ks0⟩ :=
  D.fn_ok I (res1 "io" none (res1 "os" none (fun x => env0.lookup x))) fn0 ⟨[], true, chunk_body, env0, fenv0, src0, ln0, root0, ks0⟩ (res1_ok h_io (res1_ok h_os (fun _ => rfl)))

def greet (I : Sem) (env0 : Env) (fn0 : Nat) : List Val → Nat → M (List Val) :=
  S.fn fn0 fun args n => S.let1 fun c_name => S.letEnd ((S.block (S.qStat (S.sCall (S.mSite ⟨"world.lua", 5, [], ("field", "write"), false⟩ (S.mCall I (some fn0) (S.eSite ⟨"world.lua", 5, [("global", "io")], ("", ""), false⟩ (S.eIndex I (S.eGlob I fn0 "io") (S.eStr "write".toList))) (S.lCons (S.eStr "hello, ".toList) (S.lCons (S.eCell c_name) (S.lLast (S.mOne (S.eStr "\n".toList)))))))) (S.gotos [] [])
      S.qEnd)) n)

theorem greet_ok (I : Sem) (env0 : Env) (fn0 fenv0 : Nat) (src0 : List Char) (ln0 : Nat × Nat)
    (root0 : Option Nat) (ks0 : List (Nat × Nat))
    (h_io : env0.lookup "io" = none) :
    CFn I (greet I env0 fn0) fn0 ⟨["name"], false, greet_body, env0, fenv0, src0, ln0, root0, ks0⟩ :=
  D.fn_ok I (res1 "io" none (fun x => env0.lookup x)) fn0 ⟨["name"], false, greet_body, env0, fenv0, src0, ln0, root0, ks0⟩ (res1_ok h_io (fun _ => rfl))

def readings (I : Sem) (env0 : Env) (fn0 : Nat) : List Val → Nat → M (List Val) :=
  S.fn fn0 fun args n => S.letEnd ((S.block (S.qLocal (S.lLast (S.mSite ⟨"world.lua", 9, [], ("field", "time"), false⟩ (S.mCall I (some fn0) (S.eSite ⟨"world.lua", 9, [("global", "os")], ("", ""), false⟩ (S.eIndex I (S.eGlob I fn0 "os") (S.eStr "time".toList))) S.lNil))) fun n => S.let1 fun c_t0 => S.letEnd
      ((S.qLocal (S.lLast (S.mSite ⟨"world.lua", 10, [], ("field", "time"), false⟩ (S.mCall I (some fn0) (S.eSite ⟨"world.lua", 10, [("global", "os")], ("", ""), false⟩ (S.eIndex I (S.eGlob I fn0 "os") (S.eStr "time".toList))) S.lNil))) fun n => S.let1 fun c_t1 => S.letEnd
      ((S.qStat (S.sReturn (S.lCons (S.eCell c_t0) (S.lLast (S.mOne (S.eCell c_t1))))) (S.gotos [] [])
      S.qEnd) n)) n))) n)

theorem readings_ok (I : Sem) (env0 : Env) (fn0 fenv0 : Nat) (src0 : List Char) (ln0 : Nat × Nat)
    (root0 : Option Nat) (ks0 : List (Nat × Nat))
    (h_os : env0.lookup "os" = none) :
    CFn I (readings I env0 fn0) fn0 ⟨[], false, readings_body, env0, fenv0, src0, ln0, root0, ks0⟩ :=
  D.fn_ok I (res1 "os" none (fun x => env0.lookup x)) fn0 ⟨[], false, readings_body, env0, fenv0, src0, ln0, root0, ks0⟩ (res1_ok h_os (fun _ => rfl))

end World
-- checksum World 458090887
