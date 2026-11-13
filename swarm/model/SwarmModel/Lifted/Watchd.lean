import LuaLean.Denote

/-! watchd.lua lifted by `lua-lean lift`: each function's parsed body, its shallow form, and the proof
that the two are the same. GENERATED: do not edit. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Swarm.Lifted.Watchd
open Lua


def iteration_body : Block :=
  [(.loc ["pcall", "pass", "failed", "pause", "once", "interval"] [(.var "pcall"), (.site ⟨"watchd.lua", 1157, [("upvalue", "M")], ("", ""), false⟩ (.index (.var "M") (.str "watchd_pass".toList))), (.site ⟨"watchd.lua", 1157, [("upvalue", "M")], ("", ""), false⟩ (.index (.var "M") (.str "tick_failed".toList))), (.var "pause"), (.site ⟨"watchd.lua", 1157, [("local", "opts")], ("", ""), false⟩ (.index (.var "opts") (.str "once".toList))), (.site ⟨"watchd.lua", 1157, [("local", "opts")], ("", ""), false⟩ (.index (.var "opts") (.str "interval".toList)))]), (.loc ["ok", "r", "why"] []), (.assign [(.var "ok"), (.var "r"), (.var "why")] [(.site ⟨"watchd.lua", 1159, [], ("local", "pcall"), false⟩ (.call (.var "pcall") [(.var "pass"), (.var "c"), (.var "mine"), (.var "comms"), (.var "repo"), (.var "opts"), (.var "up")]))]), (.ite (.var "ok") 
  [(.assign [(.var "up")] [(.var "r")])] 
  [(.call (.site ⟨"watchd.lua", 1160, [], ("local", "pcall"), false⟩ (.call (.var "pcall") [(.var "failed"), (.var "c"), (.var "comms"), (.var "r")])))]), (.ite (.and (.un .not (.var "why")) (.un .not (.var "once"))) 
  [(.call (.site ⟨"watchd.lua", 1161, [], ("local", "pcall"), false⟩ (.call (.var "pcall") [(.var "pause"), (.var "interval")])))] 
  []), (.ret [(.var "up"), (.var "why")])]

def M_loop_body : Block :=
  [(.loc ["pcall", "iteration", "once"] [(.var "pcall"), (.var "iteration"), (.site ⟨"watchd.lua", 1168, [("local", "opts")], ("", ""), false⟩ (.index (.var "opts") (.str "once".toList)))]), (.loc ["up", "ok", "r", "why"] [.fls]), (.rpt 
  [(.assign [(.var "ok"), (.var "r"), (.var "why")] [(.site ⟨"watchd.lua", 1171, [], ("local", "pcall"), false⟩ (.call (.var "pcall") [(.var "iteration"), (.var "c"), (.var "mine"), (.var "comms"), (.var "repo"), (.var "opts"), (.var "up")]))]), (.assign [(.var "up")] [(.and (.var "ok") (.var "r"))])] (.or (.var "why") (.var "once"))), (.ret [(.var "why"), (.var "up")])]

def iteration (I : Sem) (env0 : Env) (fn0 : Nat) (c_M c_pause : Nat) : List Val → Nat → M (List Val) :=
  S.fn fn0 fun args n => S.let1 fun c_c => S.let1 fun c_mine => S.let1 fun c_comms => S.let1 fun c_repo => S.let1 fun c_opts => S.let1 fun c_up => S.letEnd ((S.block (S.qLocal (S.lCons (S.eGlob I fn0 "pcall") (S.lCons (S.eSite ⟨"watchd.lua", 1157, [("upvalue", "M")], ("", ""), false⟩ (S.eIndex I (S.eCell c_M) (S.eStr "watchd_pass".toList))) (S.lCons (S.eSite ⟨"watchd.lua", 1157, [("upvalue", "M")], ("", ""), false⟩ (S.eIndex I (S.eCell c_M) (S.eStr "tick_failed".toList))) (S.lCons (S.eCell c_pause) (S.lCons (S.eSite ⟨"watchd.lua", 1157, [("local", "opts")], ("", ""), false⟩ (S.eIndex I (S.eCell c_opts) (S.eStr "once".toList))) (S.lLast (S.mSite ⟨"watchd.lua", 1157, [("local", "opts")], ("", ""), false⟩ (S.mOne (S.eIndex I (S.eCell c_opts) (S.eStr "interval".toList)))))))))) fun n => S.let1 fun c_pcall => S.let1 fun c_pass => S.let1 fun c_failed => S.let1 fun c_pause1 => S.let1 fun c_once => S.let1 fun c_interval => S.letEnd
      ((S.qLocal S.lNil fun n => S.let1 fun c_ok => S.let1 fun c_r => S.let1 fun c_why => S.letEnd
      ((S.qStat (S.sAssign (S.pVar (S.wCell c_ok) (S.pVar (S.wCell c_r) (S.pVar (S.wCell c_why) S.pNil))) (S.lLast (S.mSite ⟨"watchd.lua", 1159, [], ("local", "pcall"), false⟩ (S.mCall I (some fn0) (S.eCell c_pcall) (S.lCons (S.eCell c_pass) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_mine) (S.lCons (S.eCell c_comms) (S.lCons (S.eCell c_repo) (S.lCons (S.eCell c_opts) (S.lLast (S.mOne (S.eCell c_up))))))))))))) (S.gotos [] [])
      (S.qStat (S.sIf (S.eCell c_ok) (S.block (S.qStat (S.sAssign (S.pVar (S.wCell c_up) S.pNil) (S.lLast (S.mOne (S.eCell c_r)))) (S.gotos [] [])
        S.qEnd)) (S.block (S.qStat (S.sCall (S.mSite ⟨"watchd.lua", 1160, [], ("local", "pcall"), false⟩ (S.mCall I (some fn0) (S.eCell c_pcall) (S.lCons (S.eCell c_failed) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_comms) (S.lLast (S.mOne (S.eCell c_r))))))))) (S.gotos [] [])
        S.qEnd))) (S.gotos [] [])
      (S.qStat (S.sIf (S.eAnd (S.eUn I .not (S.eCell c_why)) (S.eUn I .not (S.eCell c_once))) (S.block (S.qStat (S.sCall (S.mSite ⟨"watchd.lua", 1161, [], ("local", "pcall"), false⟩ (S.mCall I (some fn0) (S.eCell c_pcall) (S.lCons (S.eCell c_pause1) (S.lLast (S.mOne (S.eCell c_interval))))))) (S.gotos [] [])
        S.qEnd)) (S.block S.qEnd)) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lCons (S.eCell c_up) (S.lLast (S.mOne (S.eCell c_why))))) (S.gotos [] [])
      S.qEnd)))) n)) n))) n)

theorem iteration_ok (I : Sem) (env0 : Env) (fn0 fenv0 : Nat) (src0 : List Char) (ln0 : Nat × Nat)
    (root0 : Option Nat) (ks0 : List (Nat × Nat)) (c_M c_pause : Nat)
    (h_M : env0.lookup "M" = some c_M)
    (h_pause : env0.lookup "pause" = some c_pause)
    (h_pcall : env0.lookup "pcall" = none) :
    CFn I (iteration I env0 fn0 c_M c_pause) fn0 ⟨["c", "mine", "comms", "repo", "opts", "up"], false, iteration_body, env0, fenv0, src0, ln0, root0, ks0⟩ :=
  D.fn_ok I (res1 "M" (some c_M) (res1 "pause" (some c_pause) (res1 "pcall" none (fun x => env0.lookup x)))) fn0 ⟨["c", "mine", "comms", "repo", "opts", "up"], false, iteration_body, env0, fenv0, src0, ln0, root0, ks0⟩ (res1_ok h_M (res1_ok h_pause (res1_ok h_pcall (fun _ => rfl))))

def M_loop (I : Sem) (env0 : Env) (fn0 : Nat) (c_iteration : Nat) : List Val → Nat → M (List Val) :=
  S.fn fn0 fun args n => S.let1 fun c_c => S.let1 fun c_mine => S.let1 fun c_comms => S.let1 fun c_repo => S.let1 fun c_opts => S.letEnd ((S.block (S.qLocal (S.lCons (S.eGlob I fn0 "pcall") (S.lCons (S.eCell c_iteration) (S.lLast (S.mSite ⟨"watchd.lua", 1168, [("local", "opts")], ("", ""), false⟩ (S.mOne (S.eIndex I (S.eCell c_opts) (S.eStr "once".toList))))))) fun n => S.let1 fun c_pcall => S.let1 fun c_iteration1 => S.let1 fun c_once => S.letEnd
      ((S.qLocal (S.lLast (S.mOne S.eFalse)) fun n => S.let1 fun c_up => S.let1 fun c_ok => S.let1 fun c_r => S.let1 fun c_why => S.letEnd
      ((S.qStat (S.sRepeat (S.qStat (S.sAssign (S.pVar (S.wCell c_ok) (S.pVar (S.wCell c_r) (S.pVar (S.wCell c_why) S.pNil))) (S.lLast (S.mSite ⟨"watchd.lua", 1171, [], ("local", "pcall"), false⟩ (S.mCall I (some fn0) (S.eCell c_pcall) (S.lCons (S.eCell c_iteration1) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_mine) (S.lCons (S.eCell c_comms) (S.lCons (S.eCell c_repo) (S.lCons (S.eCell c_opts) (S.lLast (S.mOne (S.eCell c_up))))))))))))) (S.gotos [] [])
        (S.qStat (S.sAssign (S.pVar (S.wCell c_up) S.pNil) (S.lLast (S.mOne (S.eAnd (S.eCell c_ok) (S.eCell c_r))))) (S.gotos [] [])
        (S.qEndRpt (S.eOr (S.eCell c_why) (S.eCell c_once)))))) (S.gotos [] [])
      (S.qStat (S.sReturn (S.lCons (S.eCell c_why) (S.lLast (S.mOne (S.eCell c_up))))) (S.gotos [] [])
      S.qEnd)) n)) n))) n)

theorem M_loop_ok (I : Sem) (env0 : Env) (fn0 fenv0 : Nat) (src0 : List Char) (ln0 : Nat × Nat)
    (root0 : Option Nat) (ks0 : List (Nat × Nat)) (c_iteration : Nat)
    (h_iteration : env0.lookup "iteration" = some c_iteration)
    (h_pcall : env0.lookup "pcall" = none) :
    CFn I (M_loop I env0 fn0 c_iteration) fn0 ⟨["c", "mine", "comms", "repo", "opts"], false, M_loop_body, env0, fenv0, src0, ln0, root0, ks0⟩ :=
  D.fn_ok I (res1 "iteration" (some c_iteration) (res1 "pcall" none (fun x => env0.lookup x))) fn0 ⟨["c", "mine", "comms", "repo", "opts"], false, M_loop_body, env0, fenv0, src0, ln0, root0, ks0⟩ (res1_ok h_iteration (res1_ok h_pcall (fun _ => rfl)))

end Swarm.Lifted.Watchd
-- checksum Swarm.Lifted.Watchd 3345251129
