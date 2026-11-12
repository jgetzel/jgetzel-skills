import LuaLean.Denote

/-! watchd.lua lifted by `lua-lean lift`: each function's parsed body, its shallow form, and the proof
that the two are the same. GENERATED: do not edit. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Swarm.Lifted.Watchd
open Lua


def M_iterate_body : Block :=
  [(.loc ["ok", "r", "why"] [(.site ⟨"watchd.lua", 1043, [], ("global", "pcall"), false⟩ (.call (.var "pcall") [(.var "iteration"), (.var "c"), (.var "mine"), (.var "comms"), (.var "repo"), (.var "opts"), (.var "up")]))]), (.ret [(.and (.var "ok") (.var "r")), (.var "why")])]

def M_iterate (I : Sem) (env0 : Env) (fn0 : Nat) (c_iteration : Nat) : List Val → Nat → M (List Val) :=
  S.fn fn0 fun args n => S.let1 fun c_c => S.let1 fun c_mine => S.let1 fun c_comms => S.let1 fun c_repo => S.let1 fun c_opts => S.let1 fun c_up => S.letEnd ((S.block (S.qLocal (S.lLast (S.mSite ⟨"watchd.lua", 1043, [], ("global", "pcall"), false⟩ (S.mCall I (some fn0) (S.eGlob I fn0 "pcall") (S.lCons (S.eCell c_iteration) (S.lCons (S.eCell c_c) (S.lCons (S.eCell c_mine) (S.lCons (S.eCell c_comms) (S.lCons (S.eCell c_repo) (S.lCons (S.eCell c_opts) (S.lLast (S.mOne (S.eCell c_up)))))))))))) fun n => S.let1 fun c_ok => S.let1 fun c_r => S.let1 fun c_why => S.letEnd
      ((S.qStat (S.sReturn (S.lCons (S.eAnd (S.eCell c_ok) (S.eCell c_r)) (S.lLast (S.mOne (S.eCell c_why))))) (S.gotos [] [])
      S.qEnd) n))) n)

theorem M_iterate_ok (I : Sem) (env0 : Env) (fn0 fenv0 : Nat) (src0 : List Char) (ln0 : Nat × Nat) (c_iteration : Nat)
    (h_iteration : env0.lookup "iteration" = some c_iteration)
    (h_pcall : env0.lookup "pcall" = none) :
    CFn I (M_iterate I env0 fn0 c_iteration) fn0 ⟨["c", "mine", "comms", "repo", "opts", "up"], false, M_iterate_body, env0, fenv0, src0, ln0⟩ :=
  D.fn_ok I (res1 "iteration" (some c_iteration) (res1 "pcall" none (fun x => env0.lookup x))) fn0 ⟨["c", "mine", "comms", "repo", "opts", "up"], false, M_iterate_body, env0, fenv0, src0, ln0⟩ (res1_ok h_iteration (res1_ok h_pcall (fun _ => rfl)))

end Swarm.Lifted.Watchd
-- checksum Swarm.Lifted.Watchd 2286380225
