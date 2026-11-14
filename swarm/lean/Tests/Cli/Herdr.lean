import Tests.Cli.Fixture
import SwarmLean.Herdr.Install

/-! herdr-mods (SwarmLean/Herdr): events.lua's self-test, carried over, and the installer's main path. -/

namespace SwarmLean.Tests.Cli.Herdr
open SwarmLean.Tests.Cli
open Lean (Json)

def herdrMods : IO String := return (← swarmDir) ++ "/../herdr-mods/herdr-mods"

def test_events_selftest (t : T) : IO Unit := do
  let r ← t.exec [← herdrMods, "events", "--test"]
  eq r.code 0 r.stderr
  eq r.stdout "ok\n"

/-- On a Herdr home whose shipped tabs and agents are just the patch anchors, and no herdr-app that answers: patched
copies, the layout, the Swarm link, the Calendar copy, and the stamp `swarm who` compares. -/
def test_install_main_path (t : T) : IO Unit := do
  let h := t.d ++ "/herdr"
  for d in ["mods/tabs", "mods/agents", "layouts"] do IO.FS.createDirAll (h ++ "/" ++ d)
  let anchors (ps : List (String × String)) := "\n".intercalate (ps.map (·.1))
  put (h ++ "/mods/tabs/main.js") (anchors Herdr.Install.tabsPatch)
  put (h ++ "/mods/agents/main.js") (anchors Herdr.Install.agentsPatch)
  put (h ++ "/layouts/main.json") ("{\"id\":\"root\",\"children\":[{\"id\":\"tabs\",\"content\":{\"mod\":\"tabs\"}}," ++
    "{\"id\":\"sidebar-lists\",\"children\":[{\"id\":\"agents\",\"content\":{\"mod\":\"agents\"}}]},{\"id\":\"main\",\"content\":{\"tab\":\"active\"}}," ++
    "{\"id\":\"panel\",\"max\":400,\"size\":{\"px\":300}," ++
    "\"children\":[{\"id\":\"panel-body\",\"children\":[{\"id\":\"files\"},{\"id\":\"swarm\"}]}]}]}")
  let fb ← t.fake "herdr-app" "#!/bin/sh\nexit 1\n"
  let r ← t.exec [← herdrMods, "install"]
    { env := [("HERDR_APP_HOME", some h), ("PATH", some s!"{dirname fb}:{← basePath}")] }
  eq r.code 0 r.stderr
  has r.stdout "show it with: herdr-app do layout.switch --name jgetzel"
  let tabs := (← slurp (h ++ "/mods/jgetzel-tabs/main.js")).getD ""
  for (_, rep) in Herdr.Install.tabsPatch do has tabs rep
  let agents := (← slurp (h ++ "/mods/jgetzel-agents/main.js")).getD ""
  for (_, rep) in Herdr.Install.agentsPatch do has agents rep
  let panel := ",{\"id\":\"main\",\"content\":{\"tab\":\"active\"}},{\"id\":\"panel\",\"size\":{\"weight\":1}," ++
    "\"children\":[{\"id\":\"panel-body\",\"children\":[{\"id\":\"files\"},{\"id\":\"swarm\",\"type\":\"block\"," ++
    "\"content\":{\"mod\":\"swarm\"}},{\"id\":\"calendar\",\"type\":\"block\",\"content\":{\"mod\":\"calendar\"}}]}]}"
  let layout (lists : String) := Json.parse ("{\"id\":\"root\",\"children\":[{\"id\":\"tabs\",\"content\":{\"mod\":\"jgetzel-tabs\"}}," ++
    lists ++ panel ++ "]}") |>.toOption.get!
  let some lay := Json.decode ((← slurp (h ++ "/layouts/jgetzel.json")).getD "") | fail "layout is not JSON"
  eq lay (layout "{\"id\":\"sidebar-lists\",\"children\":[{\"id\":\"agents\",\"content\":{\"mod\":\"jgetzel-agents\"}}]}")
  let some rw := Json.decode ((← slurp (h ++ "/layouts/rework.json")).getD "") | fail "rework layout is not JSON"
  eq rw (Json.parse ("{\"id\":\"root\",\"type\":\"column\",\"children\":[{\"id\":\"bar\",\"type\":\"block\"," ++
    "\"size\":{\"px\":52},\"window_drag\":true,\"content\":{\"mod\":\"rw-bar\"}},{\"id\":\"body\",\"children\":[" ++
    "{\"id\":\"rail\",\"type\":\"block\",\"content\":{\"mod\":\"rw-rail\"}}" ++
    panel.replace "{\"tab\":\"active\"}" ("{\"tab\":\"active\",\"pane\":{\"gap\":10,\"radius\":12,\"background\":\"surface\"," ++
      "\"border\":{\"width\":1,\"color\":\"border\"},\"focus\":{\"width\":1,\"color\":\"accent\"},\"lone\":true," ++
      "\"header\":{\"content\":{\"mod\":\"rw-pane\"},\"height\":38,\"position\":\"top\",\"reveal\":\"always\"}}}") ++ "]}]}")
    |>.toOption.get!)
  unless ← System.FilePath.pathExists (h ++ "/mods/rw-rail/tree.js") do fail "no rw-rail copy"
  -- The other rw mods' tree.js and marks.js are links to rw-rail's in the checkout, and files in the copies.
  for f in ["rw-bar/tree.js", "rw-bar/marks.js", "rw-pane/tree.js", "rw-pane/marks.js", "rw-swarm/tree.js", "rw-swarm/marks.js"] do
    unless (← System.FilePath.symlinkMetadata (h ++ "/mods/" ++ f)).type == .file do fail s!"no {f} copy"
  let here ← IO.FS.realPath ((← swarmDir) ++ "/../herdr-mods")
  eq (← IO.FS.realPath (h ++ "/mods/swarm")).toString (← IO.FS.realPath ((← swarmDir) ++ "/herdr/mods/swarm")).toString
  unless ← System.FilePath.pathExists (h ++ "/mods/calendar/feed.js") do fail "no calendar copy"
  let some m := Json.decode ((← slurp (h ++ "/mods/jgetzel-tabs/mod.json")).getD "") | fail "mod.json is not JSON"
  eq (m.f "installer") s!"{here}/herdr-mods"
  eq (m.f "cloned_from") (Json.mkObj [("name", "tabs")])
  let stamp := ((← t.exec ["sh", "-c", herdrStampCmd] { cwd := some here.toString }).stdout.take 64).toString
  eq (← slurp (h ++ "/jgetzel-install.stamp")) (some (stamp ++ "\n"))

def tests : List Case := [
  ("test_events_selftest", test_events_selftest),
  ("test_install_main_path", test_install_main_path)]

end SwarmLean.Tests.Cli.Herdr
