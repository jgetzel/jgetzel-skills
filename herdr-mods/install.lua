-- Install this repo's Herdr mods: the Swarm and Calendar side panels, and the tab bar and layout that show them.
-- Safe to re-run. The tab bar re-runs it after a Herdr update (its mod.json records this file's path).
--   mods/swarm            -> symlink to swarm/herdr/mods/swarm (edits there are live)
--   mods/calendar         <- copy of herdr-mods/calendar (re-run after editing it)
--   mods/jgetzel-tabs     <- Herdr's shipped tabs mod plus Calendar and Swarm buttons (generated: tabs has no
--                            extension point)
--   layouts/jgetzel.json  <- Herdr's shipped main layout with jgetzel-tabs, "swarm" and "calendar" children in
--                            the side panel, and that panel at half the work area
-- Switch to it once with: herdr-app do layout.switch --name jgetzel
-- Calendar config (calendar.json): see herdr-mods/calendar/events.lua.
-- Run it as: luajit herdr-mods/install.lua (install.sh does).
local here = arg[0]:match("^(.*)/[^/]*$") or "."
-- install.sh's rock tree (Homebrew/apt; Nix's luajit has the rocks built in)
local tree = os.getenv("XDG_DATA_HOME")
tree = ((tree and tree ~= "") and tree or os.getenv("HOME") .. "/.local/share") .. "/swarm/lua"
package.path = here .. "/../swarm/lua/?.lua;" .. tree .. "/share/lua/5.1/?.lua;" .. tree .. "/share/lua/5.1/?/init.lua;" .. package.path
package.cpath = tree .. "/lib/lua/5.1/?.so;" .. package.cpath
local lfs, unistd = require "lfs", require "posix.unistd"
local json, util, proc = require "swarm.json", require "swarm.util", require "swarm.proc"

local HERE = assert(require("posix.stdlib").realpath(here))
local HOME = os.getenv("HERDR_APP_HOME")
if not HOME or HOME == "" then HOME = os.getenv("HOME") .. "/.config/herdr-app" end

local function die(msg) io.stderr:write(msg, "\n"); os.exit(1) end

-- (anchor in Herdr's tabs/main.js, replacement); each anchor must appear exactly once.
local TABS_PATCH = {
  {
    [==[import { spaces, panes, run, openOverlay, theme, window, shared, layout, settings } from "herdr";]==],
    [==[import { spaces, panes, run, openOverlay, theme, window, shared, layout, settings, exec, appHome, focused } from "herdr";
import { calendarFeed, markCalendarOpened } from "./feed.js";]==],
  },
  {
    [==[  init() {
]==],
    [==[  init(_props, cx) {
    this.feed = calendarFeed(cx);
    this.swarm = {}; // machine:folder -> has a live swarm (undefined: not checked yet)
    cx.timer.every(15000, cx => this.swarmCheck(cx));
]==],
  },
  {
    [==[  render() {
]==],
    [==[  swarmFolder() {
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
]==],
  },
  {
    [==[    const enabled = shared("workspace.panels") ?? ["files", "changes"];
]==],
    [==[    const loc = this.swarmFolder(), swarmOn = loc ? this.swarm[loc.key] : false;
    if (loc && swarmOn === undefined) this.swarmCheck(cx);
    // Unchecked counts as on, so restoring a space's Swarm panel survives the first check.
    const enabled = [...(shared("workspace.panels") ?? ["files", "changes"]), "calendar", ...(swarmOn !== false ? ["swarm"] : [])];
    if (swarmOn === false && panel && !panel.hidden && body?.active === "swarm") run("layout.hide", { id: "panel" });
]==],
  },
  {
    [==[      .when(enabled.includes("changes"), el => el.child(panelButton("changes", "Changes", "mods/changes/changes.svg")))
]==],
    [==[      .when(enabled.includes("changes"), el => el.child(panelButton("changes", "Changes", "mods/changes/changes.svg")))
      .child(panelButton("calendar", "Calendar", "mods/calendar/calendar.svg").children(this.feed.badge(t)))
      .when(swarmOn === true, el => el.child(panelButton("swarm", "Swarm", "mods/jgetzel-tabs/swarm.svg")))
]==],
  },
  {
    [==[else { run("layout.select", { stack: "panel-body", child: id });]==],
    [==[else { if (id === "calendar") markCalendarOpened(); run("layout.select", { stack: "panel-body", child: id });]==],
  },
}

local function count(s, p)
  local n, i = 0, 1
  while true do
    local a, b = s:find(p, i, true)
    if not a then return n end
    n, i = n + 1, b + 1
  end
end

local function patch(src, edits)
  for _, e in ipairs(edits) do
    local n = count(src, e[1])
    if n ~= 1 then
      die(("install: Herdr's tabs mod changed (%d matches for %q); update TABS_PATCH in %s"):format(n, util.strip(e[1]):sub(1, 70), arg[0]))
    end
    local a, b = src:find(e[1], 1, true)
    src = src:sub(1, a - 1) .. e[2] .. src:sub(b + 1)
  end
  return src
end

local function find(node, id)
  if node.id == id then return node end
  for _, ch in ipairs(node.children or {}) do
    local f = find(ch, id)
    if f then return f end
  end
end

local function write(path, s)
  local f = assert(io.open(path, "wb"))
  f:write(s)
  f:close()
end

local function copy(src, dir) write(dir .. "/" .. util.basename(src), assert(util.slurp(src))) end

-- Hash of what the copies come from; `swarm who` runs the same command in this folder to say they're stale.
local function stamp()
  local out = proc.run({ "sh", "-c", "cat install.lua calendar/* ../swarm/herdr/mods/swarm/swarm.svg | sha256sum" }, HERE)
  return util.strip(out):sub(1, 64)
end

if not lfs.attributes(HOME .. "/mods/tabs", "mode") then
  die("install: no Herdr app home with shipped mods at " .. HOME .. " (start Herdr once, or set HERDR_APP_HOME)")
end
local mods, SWARM = HOME .. "/mods", HERE .. "/../swarm/herdr/mods/swarm"
local version = (proc.run({ "herdr-app", "--version" }) or ""):match("(%S+)%s*$")

-- Everything that can fail on a changed Herdr runs before the first write: rewriting the tab bar reloads it,
-- which ends the task that reports a failed re-install (feed.js).
local tabs_js = patch(assert(util.slurp(mods .. "/tabs/main.js")), TABS_PATCH)
local lay = assert(json.decode(assert(util.slurp(HOME .. "/layouts/main.json"))))
local bar, body = find(lay, "tabs"), find(lay, "panel-body")
if not bar or (bar.content or {}).mod ~= "tabs" or not body then
  die("install: Herdr's main layout changed (no tabs block or panel-body stack); update install.lua")
end
bar.content.mod = "jgetzel-tabs"
-- The side panel opens at half the work area (weight 1 beside the tab's weight 1); the window's
-- left sidebar is a fixed px column, so an exact half of the window isn't expressible.
local panel = find(lay, "panel")
if not panel then die("install: Herdr's main layout changed (no panel column); update install.lua") end
panel.size = { weight = 1 }
panel.max = nil
local kids = json.array()
for _, c in ipairs(body.children or {}) do
  if c.id ~= "swarm" and c.id ~= "calendar" then kids[#kids + 1] = c end
end
kids[#kids + 1] = { id = "swarm", type = "block", content = { mod = "swarm" } }
kids[#kids + 1] = { id = "calendar", type = "block", content = { mod = "calendar" } }
body.children = kids

local link = mods .. "/swarm"
local st = lfs.symlinkattributes(link)
if st and st.mode ~= "link" then die("install: " .. link .. " is a real directory; remove it and re-run") end
if st then os.remove(link) end
assert(unistd.link(assert(require("posix.stdlib").realpath(SWARM)), link, true))
print("linked " .. link)

-- A copy, not a link: svg() refuses a path that resolves outside Herdr's home.
local cal = mods .. "/calendar"
if lfs.symlinkattributes(cal) then
  -- Replaced only when it is a copy this installer made (those hold events.lua).
  if not lfs.attributes(cal .. "/events.lua") then die("install: " .. cal .. " is not this installer's copy; remove it and re-run") end
  proc.run({ "rm", "-rf", cal })
end
lfs.mkdir(cal)
for f in lfs.dir(HERE .. "/calendar") do
  if f:sub(1, 1) ~= "." then copy(HERE .. "/calendar/" .. f, cal) end
end
print("wrote " .. cal)

local tabs = mods .. "/jgetzel-tabs"
lfs.mkdir(tabs)
write(tabs .. "/main.js", tabs_js)
write(tabs .. "/mod.json", json.encode({ place = "none", title = "Tabs", installer = HERE .. "/install.lua",
  cloned_from = { name = "tabs", version = version } }))
copy(SWARM .. "/swarm.svg", tabs) -- assets don't load through a symlinked mod dir
copy(HERE .. "/calendar/feed.js", tabs) -- mods can't import across mod folders
for _, f in ipairs({ "gpui-kit.d.ts", "jsconfig.json" }) do
  if lfs.attributes(mods .. "/tabs/" .. f) then copy(mods .. "/tabs/" .. f, tabs) end
end
print("wrote " .. tabs)

local out = HOME .. "/layouts/jgetzel.json"
write(out .. ".tmp", json.encode(lay))
assert(os.rename(out .. ".tmp", out))
print("wrote " .. out)

if version then
  for _, m in ipairs({ tabs, cal }) do
    local stdout, stderr, code = proc.exec({ "herdr-app", "check", m })
    if code ~= 0 then die("install: herdr-app check " .. m .. " failed: " .. util.strip(stderr ~= "" and stderr or stdout)) end
  end
end

-- The swarm-only copies an earlier install.lua made: move a window off them, then remove them. With no
-- window to ask, or a switch that failed, they stay for a later run: the saved layout may still be "swarm".
local status = json.decode(proc.run({ "herdr-app", "status" }) or "")
if status and (status.layout ~= "swarm" or proc.run({ "herdr-app", "do", "layout.switch", "--name", "jgetzel" })) then
  proc.run({ "rm", "-rf", mods .. "/swarm-tabs", HOME .. "/layouts/swarm.json", HOME .. "/swarm-install.stamp" })
end

write(HOME .. "/jgetzel-install.stamp", stamp() .. "\n")
if not (util.slurp(HOME .. "/keys.json") or ""):find('"jgetzel-tabs.calendar"', 1, true) then
  print('toggle the Calendar panel from a key: add "cmd-shift-k": "jgetzel-tabs.calendar" to keys.json\'s "global"')
end
print("show it with: herdr-app do layout.switch --name jgetzel")
