#!/usr/bin/env python3
"""Install the Herdr Swarm panel. Safe to re-run; re-run after a Herdr update to pick up its new tab bar and layout.

- mods/swarm        -> symlink to this repo's panel (edits here are live)
- mods/swarm-tabs   <- Herdr's shipped tabs mod plus a Swarm button (generated: tabs has no extension point)
- layouts/swarm.json <- Herdr's shipped main layout with swarm-tabs and a "swarm" child in the side panel
Switch to it once with: herdr-app do layout.switch --name swarm"""
import json, os, shutil, sys

HERE = os.path.dirname(os.path.realpath(__file__))
HOME = os.environ.get("HERDR_APP_HOME") or os.path.expanduser("~/.config/herdr-app")

# (anchor in Herdr's tabs/main.js, replacement); each anchor must appear exactly once.
TABS_PATCH = [
    ('import { spaces, panes, run, openOverlay, theme, window, shared, layout, settings } from "herdr";',
     'import { spaces, panes, run, openOverlay, theme, window, shared, layout, settings, exec, appHome, focused } from "herdr";'),
    ("  init() {\n",
     "  init(_props, cx) {\n"
     "    this.swarm = {}; // folder -> has a live swarm (undefined: not checked yet)\n"
     "    cx.timer.every(15000, cx => this.swarmCheck(cx));\n"),
    ("  render() {\n",
     "  swarmFolder() {\n"
     "    const space = spaces().find(s => s.active), f = focused();\n"
     "    if (!space || space.machine) return null; // the swarm CLI runs here only\n"
     "    return (f?.pane ? panes().find(p => p.pane === f.pane)?.cwd : null) || f?.cwd || space.folder || null;\n"
     "  }\n\n"
     "  swarmCheck(cx) {\n"
     "    const folder = this.swarmFolder();\n"
     "    if (!folder || this.swarmBusy) return;\n"
     "    this.swarmBusy = true;\n"
     "    cx.spawn(async cx => {\n"
     "      let on = false;\n"
     '      try { const r = await exec("env", ["-u", "SWARM_DB", "python3", `${appHome()}/mods/swarm/../../../swarm`, "state", "--json"], { cwd: folder }); on = r.code === 0 && JSON.parse(r.stdout).active === true; } catch {}\n'
     "      this.swarmBusy = false;\n"
     "      if (this.swarm[folder] !== on) { this.swarm[folder] = on; cx.notify(); }\n"
     "    });\n"
     "  }\n\n"
     "  render(cx) {\n"),
    ('    const enabled = shared("workspace.panels") ?? ["files", "changes"];\n',
     '    const folder = this.swarmFolder(), swarmOn = folder ? this.swarm[folder] : false;\n'
     '    if (folder && swarmOn === undefined) this.swarmCheck(cx);\n'
     '    // Unchecked counts as on, so restoring a space\'s Swarm panel survives the first check.\n'
     '    const enabled = [...(shared("workspace.panels") ?? ["files", "changes"]), ...(swarmOn !== false ? ["swarm"] : [])];\n'
     '    if (swarmOn === false && panel && !panel.hidden && body?.active === "swarm") run("layout.hide", { id: "panel" });\n'),
    ('      .when(enabled.includes("changes"), el => el.child(panelButton("changes", "Changes", "mods/changes/changes.svg")))\n',
     '      .when(enabled.includes("changes"), el => el.child(panelButton("changes", "Changes", "mods/changes/changes.svg")))\n'
     '      .when(swarmOn === true, el => el.child(panelButton("swarm", "Swarm", "mods/swarm-tabs/swarm.svg")))\n'),
]


def patch(src, edits):
    for old, new in edits:
        n = src.count(old)
        if n != 1:
            sys.exit(f"install: Herdr's tabs mod changed ({n} matches for {old.strip()[:70]!r}); update TABS_PATCH in {__file__}")
        src = src.replace(old, new)
    return src


def find(node, id_):
    if node.get("id") == id_:
        return node
    for ch in node.get("children", []):
        if (f := find(ch, id_)):
            return f
    return None


def main():
    if not os.path.isdir(os.path.join(HOME, "mods", "tabs")):
        sys.exit(f"install: no Herdr app home with shipped mods at {HOME} (start Herdr once, or set HERDR_APP_HOME)")
    mods = os.path.join(HOME, "mods")

    link = os.path.join(mods, "swarm")
    if os.path.exists(link) and not os.path.islink(link):
        sys.exit(f"install: {link} is a real directory; remove it and re-run")
    if os.path.islink(link):
        os.remove(link)
    os.symlink(os.path.join(HERE, "mods", "swarm"), link)
    print(f"linked {link}")

    tabs = os.path.join(mods, "swarm-tabs")
    os.makedirs(tabs, exist_ok=True)
    src = open(os.path.join(mods, "tabs", "main.js")).read()
    open(os.path.join(tabs, "main.js"), "w").write(patch(src, TABS_PATCH))
    json.dump({"place": "none", "title": "Tabs (Swarm)"}, open(os.path.join(tabs, "mod.json"), "w"))
    shutil.copy(os.path.join(HERE, "mods", "swarm", "swarm.svg"), tabs)  # assets don't load through a symlinked mod dir
    for f in ("gpui-kit.d.ts", "jsconfig.json"):
        if os.path.exists(os.path.join(mods, "tabs", f)):
            shutil.copy(os.path.join(mods, "tabs", f), tabs)
    print(f"wrote {tabs}")

    lay = json.load(open(os.path.join(HOME, "layouts", "main.json")))
    bar, body = find(lay, "tabs"), find(lay, "panel-body")
    if not bar or bar.get("content", {}).get("mod") != "tabs" or not body:
        sys.exit("install: Herdr's main layout changed (no tabs block or panel-body stack); update install.py")
    bar["content"]["mod"] = "swarm-tabs"
    body["children"] = [c for c in body["children"] if c.get("id") != "swarm"] + [
        {"id": "swarm", "type": "block", "content": {"mod": "swarm"}}]
    out = os.path.join(HOME, "layouts", "swarm.json")
    with open(out + ".tmp", "w") as f:
        json.dump(lay, f, indent=2)
    os.replace(out + ".tmp", out)
    print(f"wrote {out}\nshow it with: herdr-app do layout.switch --name swarm")


if __name__ == "__main__":
    main()
