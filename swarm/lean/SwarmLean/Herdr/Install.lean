import SwarmLean.Herdr.Events

/-! `herdr-mods install` (was herdr-mods/install.lua): this repo's Herdr mods, the Swarm and Calendar side panels and the
tab bar and layout that show them. Safe to re-run. The tab bar re-runs it after a Herdr update (its mod.json records
the herdr-mods/herdr-mods launcher).
  mods/swarm            -> symlink to swarm/herdr/mods/swarm (edits there are live)
  mods/calendar         <- copy of herdr-mods/calendar (re-run after editing it)
  mods/jgetzel-tabs     <- Herdr's shipped tabs mod plus Calendar and Swarm buttons (generated: tabs has no extension
                           point)
  mods/jgetzel-agents   <- Herdr's shipped agents mod listing each agent once (generated likewise)
  layouts/jgetzel.json  <- Herdr's shipped main layout with jgetzel-tabs, jgetzel-agents, "swarm" and "calendar"
                           children in the side panel, and that panel at half the work area
Switch to it once with: herdr-app do layout.switch --name jgetzel
Calendar config (calendar.json): see Events.lean. Run it as: herdr-mods/herdr-mods install (install.sh does). -/

namespace SwarmLean.Herdr.Install
open Lean (Json)

-- (anchor in Herdr's tabs/main.js, replacement); each anchor must appear exactly once.
def tabsPatch : List (String × String) := [
  (r##"import { spaces, panes, run, openOverlay, theme, window, shared, layout, settings } from "herdr";"##,
   r##"import { spaces, panes, run, openOverlay, theme, window, shared, layout, settings, exec, appHome, focused } from "herdr";
import { calendarFeed, markCalendarOpened } from "./feed.js";"##),
  (r##"  init() {
"##,
   r##"  init(_props, cx) {
    this.feed = calendarFeed(cx);
    this.swarm = {}; // machine:folder -> has a live swarm (undefined: not checked yet)
    cx.timer.every(15000, cx => this.swarmCheck(cx));
"##),
  (r##"  render() {
"##,
   r##"  swarmFolder() {
    const space = spaces().find(s => s.active), f = focused();
    if (!space) return null;
    const cwd = (f?.pane ? panes().find(p => p.pane === f.pane)?.cwd : null) || f?.cwd || space.folder;
    return cwd ? { cwd, on: space.machine ?? null, key: `${space.machine}:${cwd}` } : null;
  }

  swarmCheck(cx) {
    const loc = this.swarmFolder();
    if (!loc || this.swarmBusy) return;
    this.swarmBusy = true;
    cx.spawn(async cx => {
      let on = false;
      // Another machine: its installed swarm skill (full state if it predates --view); here: the CLI beside
      // mods/swarm. Only `active` is read, so the cheapest view.
      const r = loc.on ? exec("sh", ["-c", 'S="$HOME/.claude/skills/swarm/swarm"; env -u SWARM_DB "$S" state --json --view board 2>/dev/null || exec env -u SWARM_DB "$S" state --json'], { cwd: loc.cwd, on: loc.on })
        : exec("env", ["-u", "SWARM_DB", `${appHome()}/mods/swarm/../../../swarm`, "state", "--json", "--view", "board"], { cwd: loc.cwd });
      try { const out = await r; on = out.code === 0 && JSON.parse(out.stdout).active === true; } catch {}
      this.swarmBusy = false;
      if (this.swarm[loc.key] !== on) { this.swarm[loc.key] = on; cx.notify(); }
    });
  }

  render(cx) {
    this.feed.render(cx);
"##),
  (r##"    const enabled = shared("workspace.panels") ?? ["files", "changes"];
"##,
   r##"    const loc = this.swarmFolder(), swarmOn = loc ? this.swarm[loc.key] : false;
    if (loc && swarmOn === undefined) this.swarmCheck(cx);
    // Unchecked counts as on, so restoring a space's Swarm panel survives the first check.
    const enabled = [...(shared("workspace.panels") ?? ["files", "changes"]), "calendar", ...(swarmOn !== false ? ["swarm"] : [])];
    if (swarmOn === false && panel && !panel.hidden && body?.active === "swarm") run("layout.hide", { id: "panel" });
"##),
  (r##"      .when(enabled.includes("changes"), el => el.child(panelButton("changes", "Changes", "mods/changes/changes.svg")))
"##,
   r##"      .when(enabled.includes("changes"), el => el.child(panelButton("changes", "Changes", "mods/changes/changes.svg")))
      .child(panelButton("calendar", "Calendar", "mods/calendar/calendar.svg").children(this.feed.badge(t)))
      .when(swarmOn === true, el => el.child(panelButton("swarm", "Swarm", "mods/jgetzel-tabs/swarm.svg")))
"##),
  (r##"else { run("layout.select", { stack: "panel-body", child: id });"##,
   r##"else { if (id === "calendar") markCalendarOpened(); run("layout.select", { stack: "panel-body", child: id });"##)]

-- Herdr's agents/main.js roots every agent with a pane and nests it again under its hc parent. Here an agent with a
-- pane shows once: under its parent when both are in the same group and space, else as a root. In order: one status
-- per agent; nest only the listed; a nested agent with a pane opens like its root row did; nest stays empty until the
-- groups are known; the machine only where the group's agents aren't all on one; the time says what it measures; the
-- sort menu opens this mod, not the shipped one.
def agentsPatch : List (String × String) := [
  (r##"  const s = listed.get(k.address) ?? k.status;
"##,
   r##"  if (listed.has(k.address)) return listed.get(k.address).status;
  const s = k.status;
"##),
  (r##"    const kids = all.filter((k) => k.parent === addr && k.state === "live");
"##,
   r##"    const kids = all.filter((k) => k.parent === addr && k.state === "live" && (!this.listed.has(k.address) || this.nest.has(k.address)));
"##),
  (r##"    const on = k.address === shown;
"##,
   r##"    const own = this.listed.get(k.address);
    const on = own ? own.focused : k.address === shown;
"##),
  (r##"      .on_click(() => this.peek(k.address))
"##,
   r##"      .on_click(() => (own ? run("pane.focus", { pane: own.pane }) : this.peek(k.address)))
"##),
  (r##"    this.listed = new Map(list.map((a) => [a.address, a.status]));
"##,
   r##"    this.listed = new Map(list.map((a) => [a.address, a]));
    this.nest = new Set();
"##),
  (r##"    setAgentOrder(list.map((a) => a.address));
"##,
   r##"    setAgentOrder(list.map((a) => a.address));
    const gid = (a) => (pinned.includes(a) ? "pinned" : byPriority ? `sec-${rankOf(a) || RANK.idle}` : `sp-${a.space}`);
    const machines = {}; // group -> the machines its agents are on
    for (const a of list) (machines[gid(a)] ??= new Set()).add(a.address.includes("/") ? a.address.split("/")[0] : "");
    for (const k of all) {
      const a = this.listed.get(k.address), p = this.listed.get(k.parent);
      if (a && p && k.state === "live" && a.space === p.space && gid(a) === gid(p)) this.nest.add(a.address);
    }
"##),
  (r##"      .when(Boolean(machine), el =>"##,
   r##"      .when(Boolean(machine) && machines[gid(a)].size > 1, el =>"##),
  (r##".child(duration(now - when))"##,
   r##".child(`${a.status} ${duration(now - when)}`)"##),
  (r##"g.members.flatMap(withKids))"##,
   r##"g.members.filter((a) => !this.nest.has(a.address)).flatMap(withKids))"##),
  (r##"openOverlay({ mod: "agents","##,
   r##"openOverlay({ mod: "jgetzel-agents","##)]

/-- The newer Herdr's one differing anchor, put back to the older form agentsPatch expects (an unknown form still dies in patch). -/
def agentsNormalize : List (String × String) := [
  (r##"      .on_click(() => (this.listed.has(k.address) ? run("pane.focus", { terminal: k.address }) : this.peek(k.address)))
"##,
   r##"      .on_click(() => this.peek(k.address))
"##)]

def die (msg : String) : IO α := do IO.eprintln msg; IO.Process.exit 1

/-- `argv`'s stdout when it exits 0, else none (proc.run). -/
def run (argv : List String) (cwd : Option String := none) : IO (Option String) := do
  try
    let o ← IO.Process.output { cmd := argv.head!, args := argv.tail.toArray, cwd := cwd.map (⟨·⟩) }
    return if o.exitCode == 0 then some o.stdout else none
  catch _ => return none

def SRC := "swarm/lean/SwarmLean/Herdr/Install.lean"

def patch (src : String) (edits : List (String × String)) (mod : String) : IO String := do
  let mut src := src
  for (a, b) in edits do
    let n := (src.splitOn a).length - 1
    if n != 1 then
      die s!"install: Herdr's {mod} mod changed ({n} matches for {Events.luaQ (cut (strip a) 70)}); update {mod}Patch in {SRC}"
    src := src.replace a b
  return src

partial def find (node : Json) (id : String) : Option Json :=
  if Json.fstr node "id" == some id then some node
  else (Json.items ((Json.field node "children").getD .null)).findSome? (find · id)

def withMod (node : Json) (mod : String) : Json := node.setObjVal! "content" (((Json.field node "content").getD (Json.mkObj [])).setObjVal! "mod" mod)

/-- The layout with the tab bar and agents list swapped for this repo's, the side panel at half the work area, and the
Swarm and Calendar children last in the panel body. -/
partial def edit (j : Json) : Json := Id.run do
  let mut j := j
  match Json.fstr j "id" with
  | some "tabs" => j := withMod j "jgetzel-tabs"
  | some "agents" => j := withMod j "jgetzel-agents"
  -- weight 1 beside the tab's weight 1; the window's left sidebar is a fixed px column, so an exact half of the window
  -- isn't expressible
  | some "panel" =>
    j := j.setObjVal! "size" (Json.mkObj [("weight", 1)])
    if let .obj kv := j then j := .obj (kv.erase "max")
  | some "panel-body" =>
    let kids := (Json.items ((Json.field j "children").getD .null)).filter fun c =>
      Json.fstr c "id" != some "swarm" && Json.fstr c "id" != some "calendar"
    let block (id : String) := Json.mkObj [("id", id), ("type", "block"), ("content", Json.mkObj [("mod", id)])]
    j := j.setObjVal! "children" (.arr (kids ++ [block "swarm", block "calendar"]).toArray)
  | _ => pure ()
  if let some (.arr cs) := Json.field j "children" then j := j.setObjVal! "children" (.arr (cs.map edit))
  return j

def exists_ (p : String) (follow := true) : IO Bool := do
  try
    discard <| if follow then System.FilePath.metadata p else System.FilePath.symlinkMetadata p
    return true
  catch _ => return false

def copy (src dir : String) : IO Unit := do IO.FS.writeBinFile (dir ++ "/" ++ basename src) (← IO.FS.readBinFile src)

/-- herdr-mods/: beside the swarm/ the launcher names, else above this binary (a lake build in the checkout). -/
def hereDir : IO String := do
  if let some h ← IO.getEnv "SWARM_HERE" then if h != "" then return (← IO.FS.realPath (h ++ "/../herdr-mods")).toString
  let mut dir := (← IO.appPath).parent
  while dir.isSome do
    let d := dir.get!
    if ← (d / "herdr-mods" / "herdr-mods").pathExists then return (← IO.FS.realPath (d / "herdr-mods")).toString
    dir := if d.parent == some d then none else d.parent
  die "install: can't find herdr-mods/: run herdr-mods/herdr-mods install"

def main : IO UInt32 := do
  let here ← hereDir
  let dflt := ((← IO.getEnv "HOME").getD "") ++ "/.config/herdr-app"
  let home := (← IO.getEnv "HERDR_APP_HOME").getD ""
  let home := if home != "" then home else dflt
  unless ← exists_ (home ++ "/mods/tabs") do
    die s!"install: no Herdr app home with shipped mods at {home} (start Herdr once, or set HERDR_APP_HOME)"
  let mods := home ++ "/mods"
  let swarm := here ++ "/../swarm/herdr/mods/swarm"
  let version := (← run ["herdr-app", "--version"]).bind fun o => (words o).getLast?

  -- Everything that can fail on a changed Herdr runs before the first write: rewriting the tab bar reloads it, which
  -- ends the task that reports a failed re-install (feed.js).
  let tabsJs ← patch (← IO.FS.readFile (mods ++ "/tabs/main.js")) tabsPatch "tabs"
  let agentsSrc := (← IO.FS.readFile (mods ++ "/agents/main.js"))
  let agentsSrc := agentsNormalize.foldl (fun s (a, b) => s.replace a b) agentsSrc
  let agentsJs ← patch agentsSrc agentsPatch "agents"
  let lay ← match Json.decode (← IO.FS.readFile (home ++ "/layouts/main.json")) with
    | some l => pure l
    | none => die s!"install: {home}/layouts/main.json is not JSON"
  let modOf (n : Option Json) := n.bind fun n => (Json.field n "content").bind (Json.fstr · "mod")
  if modOf (find lay "tabs") != some "tabs" || (find lay "panel-body").isNone then
    die s!"install: Herdr's main layout changed (no tabs block or panel-body stack); update {SRC}"
  if modOf (find lay "agents") != some "agents" then die s!"install: Herdr's main layout changed (no agents block); update {SRC}"
  if (find lay "panel").isNone then die s!"install: Herdr's main layout changed (no panel column); update {SRC}"
  let lay := edit lay

  let link := mods ++ "/swarm"
  if ← exists_ link false then
    if (← System.FilePath.symlinkMetadata link).type != .symlink then
      die s!"install: {link} is a real directory; remove it and re-run"
    IO.FS.removeFile link
  if (← run ["ln", "-s", (← IO.FS.realPath swarm).toString, link]).isNone then die s!"install: can't link {link}"
  IO.println s!"linked {link}"

  -- A copy, not a link: svg() refuses a path that resolves outside Herdr's home.
  let cal := mods ++ "/calendar"
  if ← exists_ cal false then
    -- Replaced only when it is a copy this installer made (those hold feed.js; older ones events.lua).
    unless (← exists_ (cal ++ "/feed.js")) || (← exists_ (cal ++ "/events.lua")) do
      die s!"install: {cal} is not this installer's copy; remove it and re-run"
    discard <| run ["rm", "-rf", cal]
  IO.FS.createDirAll cal
  for e in ← System.FilePath.readDir (here ++ "/calendar") do
    if !e.fileName.startsWith "." then copy e.path.toString cal
  IO.println s!"wrote {cal}"

  let shipped (mod dir : String) : IO Unit := do
    for f in ["gpui-kit.d.ts", "jsconfig.json"] do
      if ← exists_ (mods ++ "/" ++ mod ++ "/" ++ f) then copy (mods ++ "/" ++ mod ++ "/" ++ f) dir
  let cloned (name : String) : Json :=
    Json.mkObj ([("name", Json.str name)] ++ (version.map fun v => [("version", Json.str v)]).getD [])
  let tabs := mods ++ "/jgetzel-tabs"
  IO.FS.createDirAll tabs
  IO.FS.writeFile (tabs ++ "/main.js") tabsJs
  IO.FS.writeFile (tabs ++ "/mod.json") (Json.encode (Json.mkObj [("place", "none"), ("title", "Tabs"),
    ("installer", Json.str (here ++ "/herdr-mods")), ("cloned_from", cloned "tabs")]))
  copy (swarm ++ "/swarm.svg") tabs -- assets don't load through a symlinked mod dir
  copy (here ++ "/calendar/feed.js") tabs -- mods can't import across mod folders
  shipped "tabs" tabs
  IO.println s!"wrote {tabs}"

  let agents := mods ++ "/jgetzel-agents"
  IO.FS.createDirAll agents
  IO.FS.writeFile (agents ++ "/main.js") agentsJs
  IO.FS.writeFile (agents ++ "/mod.json") (Json.encode (Json.mkObj [("place", "none"), ("title", "Agents"),
    ("cloned_from", cloned "agents")]))
  shipped "agents" agents
  IO.println s!"wrote {agents}"

  let out := home ++ "/layouts/jgetzel.json"
  IO.FS.writeFile (out ++ ".tmp") (Json.encode lay)
  IO.FS.rename (out ++ ".tmp") out
  IO.println s!"wrote {out}"

  if version.isSome then
    for m in [tabs, agents, cal] do
      let o ← IO.Process.output { cmd := "herdr-app", args := #["check", m] }
      if o.exitCode != 0 then die s!"install: herdr-app check {m} failed: {strip (if o.stderr != "" then o.stderr else o.stdout)}"

  -- The swarm-only copies an earlier installer made: move a window off them, then remove them. With no window to ask,
  -- or a switch that failed, they stay for a later run: the saved layout may still be "swarm".
  if let some status := (← run ["herdr-app", "status"]).bind Json.decode then
    if Json.fstr status "layout" != some "swarm" || (← run ["herdr-app", "do", "layout.switch", "--name", "jgetzel"]).isSome then
      discard <| run ["rm", "-rf", mods ++ "/swarm-tabs", home ++ "/layouts/swarm.json", home ++ "/swarm-install.stamp"]

  -- Hash of what the copies come from; `swarm who` runs the same command to say they're stale.
  let stamp := ((← run ["sh", "-c", herdrStampCmd] here).getD "").take 64
  IO.FS.writeFile (home ++ "/jgetzel-install.stamp") (stamp.toString ++ "\n")
  let keys ← try IO.FS.readFile (home ++ "/keys.json") catch _ => pure ""
  if !hasSub keys "\"jgetzel-tabs.calendar\"" then
    IO.println "toggle the Calendar panel from a key: add \"cmd-shift-k\": \"jgetzel-tabs.calendar\" to keys.json's \"global\""
  IO.println "show it with: herdr-app do layout.switch --name jgetzel"
  return 0

end SwarmLean.Herdr.Install
