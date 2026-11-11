import LuaLean.Shallow

/-! world.lua lifted by `lua-lean lift`: each function's parsed body, its shallow form, and the proof
that the two are the same. GENERATED: do not edit. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace World
open Lua


def chunk_body : Block :=
  [(.locfn "greet" ["name"] false 
  [(.call (.site ⟨"world.lua", 5, [], ("field", "write"), false⟩ (.call (.site ⟨"world.lua", 5, [("global", "io")], ("", ""), false⟩ (.index (.var "io") (.str "write".toList))) [(.str "hello, ".toList), (.var "name"), (.str "\n".toList)])))]), (.locfn "readings" [] false 
  [(.loc ["t0"] [(.site ⟨"world.lua", 9, [], ("field", "time"), false⟩ (.call (.site ⟨"world.lua", 9, [("global", "os")], ("", ""), false⟩ (.index (.var "os") (.str "time".toList))) []))]), (.loc ["t1"] [(.site ⟨"world.lua", 10, [], ("field", "time"), false⟩ (.call (.site ⟨"world.lua", 10, [("global", "os")], ("", ""), false⟩ (.index (.var "os") (.str "time".toList))) []))]), (.ret [(.var "t0"), (.var "t1")])]), (.ret [(.var "greet"), (.var "readings")])]

def greet_body : Block :=
  [(.call (.site ⟨"world.lua", 5, [], ("field", "write"), false⟩ (.call (.site ⟨"world.lua", 5, [("global", "io")], ("", ""), false⟩ (.index (.var "io") (.str "write".toList))) [(.str "hello, ".toList), (.var "name"), (.str "\n".toList)])))]

def readings_body : Block :=
  [(.loc ["t0"] [(.site ⟨"world.lua", 9, [], ("field", "time"), false⟩ (.call (.site ⟨"world.lua", 9, [("global", "os")], ("", ""), false⟩ (.index (.var "os") (.str "time".toList))) []))]), (.loc ["t1"] [(.site ⟨"world.lua", 10, [], ("field", "time"), false⟩ (.call (.site ⟨"world.lua", 10, [("global", "os")], ("", ""), false⟩ (.index (.var "os") (.str "time".toList))) []))]), (.ret [(.var "t0"), (.var "t1")])]

def chunk (I : Sem) (env0 : Env) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.letEnd ((S.block (S.qLocalFn "greet" ["name"] false greet_body (env0) fun c_greet =>
      (S.qLocalFn "readings" [] false readings_body (("greet", c_greet) :: env0) fun c_readings =>
      (S.qStat (S.sReturn (S.lCons (S.eCell c_greet) (S.lLast (S.mOne (S.eCell c_readings))))) (S.gotos [] [])
      S.qEnd)))) n)

theorem chunk_ok (I : Sem) (env0 : Env)
    (h_io : env0.lookup "io" = none)
    (h_os : env0.lookup "os" = none) :
    CFn I (chunk I env0) ⟨[], true, chunk_body, env0⟩ :=
  CFn_fn fun args n => CBs_end ((CK_block (CQ_localFn (by rfl) fun c_greet =>
      (CQ_localFn (by rfl) fun c_readings =>
      (CQ_stat (CS_return (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))
      CQ_end rfl rfl rfl)))) n)

def greet (I : Sem) (env0 : Env) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.let1 fun c_name => S.letEnd ((S.block (S.qStat (S.sCall (S.mSite ⟨"world.lua", 5, [], ("field", "write"), false⟩ (S.mCall I (S.eSite ⟨"world.lua", 5, [("global", "io")], ("", ""), false⟩ (S.eIndex I (S.eGlob "io") (S.eStr "write".toList))) (S.lCons (S.eStr "hello, ".toList) (S.lCons (S.eCell c_name) (S.lLast (S.mOne (S.eStr "\n".toList)))))))) (S.gotos [] [])
      S.qEnd)) n)

theorem greet_ok (I : Sem) (env0 : Env)
    (h_io : env0.lookup "io" = none) :
    CFn I (greet I env0) ⟨["name"], false, greet_body, env0⟩ :=
  CFn_fn fun args n => CBs_let fun c_name => CBs_end ((CK_block (CQ_stat (CS_call (CM_site (CM_call (CE_site (CE_index (CE_glob h_io) CE_str)) (CL_cons CE_str (CL_cons (CE_cell rfl) (CL_last (CM_one rfl CE_str)))))))
      CQ_end rfl rfl rfl)) n)

def readings (I : Sem) (env0 : Env) : List Val → Nat → M (List Val) :=
  S.fn fun args n => S.letEnd ((S.block (S.qLocal (S.lLast (S.mSite ⟨"world.lua", 9, [], ("field", "time"), false⟩ (S.mCall I (S.eSite ⟨"world.lua", 9, [("global", "os")], ("", ""), false⟩ (S.eIndex I (S.eGlob "os") (S.eStr "time".toList))) S.lNil))) fun n => S.let1 fun c_t0 => S.letEnd
      ((S.qLocal (S.lLast (S.mSite ⟨"world.lua", 10, [], ("field", "time"), false⟩ (S.mCall I (S.eSite ⟨"world.lua", 10, [("global", "os")], ("", ""), false⟩ (S.eIndex I (S.eGlob "os") (S.eStr "time".toList))) S.lNil))) fun n => S.let1 fun c_t1 => S.letEnd
      ((S.qStat (S.sReturn (S.lCons (S.eCell c_t0) (S.lLast (S.mOne (S.eCell c_t1))))) (S.gotos [] [])
      S.qEnd) n)) n))) n)

theorem readings_ok (I : Sem) (env0 : Env)
    (h_os : env0.lookup "os" = none) :
    CFn I (readings I env0) ⟨[], false, readings_body, env0⟩ :=
  CFn_fn fun args n => CBs_end ((CK_block (CQ_local (CL_last (CM_site (CM_call (CE_site (CE_index (CE_glob h_os) CE_str)) CL_nil))) fun n => CBs_let fun c_t0 => CBs_end
      ((CQ_local (CL_last (CM_site (CM_call (CE_site (CE_index (CE_glob h_os) CE_str)) CL_nil))) fun n => CBs_let fun c_t1 => CBs_end
      ((CQ_stat (CS_return (CL_cons (CE_cell rfl) (CL_last (CM_one rfl (CE_cell rfl)))))
      CQ_end rfl rfl rfl) n)) n))) n)

end World
-- checksum World 458090887
