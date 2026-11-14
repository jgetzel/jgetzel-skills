// The rework's rail (swarm/herdr/UI-SPEC.md, slice 1): spaces by machine, each with its agents and then its shells,
// one row each (name, title or task, time, mark), on a guide line under the space's heading, sub-terminals under
// their parent on a thin line. A space folds to one line of counts. Click a row to focus its terminal; click a space
// to show it, click the shown one or any chevron to fold it. A space with a live swarm (its communicator's space, else
// its folder's) shows it as a block first (slice 6), from `swarm state --json --view summary`; its heading opens the swarm tab (slice 7). Each machine's
// heading (slice 10) has a menu (rename in place, hide, update, log in again, remove) and its state from
// `hc machine ls --json`: an unreachable machine's spaces dim with Retry; hidden machines are lines at the foot with Show.
// Once more than one swarm runs, an All swarms row heads the rail (slice 13); it shows rw-swarms in place of the tabs.
// A hung swarm agent is a toast at the rail's foot (canvas, Attention): what it holds, Nudge and Open.

import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex, HoverCard, Popover, InputState, Input } from "gpui-base";
import { spaces, panes, terminals, agents, focused, machines, run, theme, settings, setAgentOrder, shared, setShared, home, exec, hc, layout, appHome } from "herdr";
import { AGENT, abbrev, allShown, asksIn, dur, line, looked, machinesOf, nudgeArgs, openAsk, pollNext, due, prune, rollOf, rowText, rowsOf, settleOf, showAll, since, stamp, sumFor, sumOf,
  swarmAddrs, swarmOf, swarmsOf, swarmText } from "./tree.js";
import { mark } from "./marks.js";

const ROW = 24; // fixed, so the tree lines of stacked rows meet
const ORDER = ["asks", "hung", "working", "done", "idle"]; // a folded space's counts, then its shells
const find = (node, id) => (node?.id === id ? node : (node?.children ?? []).reduce((f, c) => f ?? find(c, id), null));
const HIDDEN = "rw-rail.hidden"; // the names of the machines hidden from the rail (shared() persists it)
const NARROW = 160; // a sidebar narrower than this shows tiles (as workspace-chrome goes by width)
// The swarm CLI as the swarm mod runs it: this checkout's (mods/swarm links into it), or the skill's on another machine.
const swarm = (cwd, on, args) => on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB SWARM_NAME=human "$HOME/.claude/skills/swarm/swarm" "$@"', "sh", ...args], { cwd, on })
  : exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", `${appHome()}/mods/swarm/../../../swarm`, ...args], { cwd });
const where = (s) => `${s.machine ?? ""}:${s.folder}`;
const base = (p) => line(p.replace(/\/+$/, "").replace(/.*\//, ""), 60);
const ROWS = 40; // a space's rows drawn before a "N more" line that shows the rest
const SPACES = 60; // a machine's spaces drawn (the shown one always among them) before a "N more spaces" line
const CHANGED = 5000; // agents' since-when times kept (the live ones always): the oldest of the rest go first

export default class Rail extends View {
  init(_props, cx) {
    try { this.folded = new Set(JSON.parse(localStorage.getItem("folded") ?? "[]")); } catch { this.folded = new Set(); }
    // Each agent's mark, turn and since when (ms), kept across restarts: terminals() leaves status_ms null.
    try { this.changed = JSON.parse(localStorage.getItem("changed") ?? "{}"); } catch { this.changed = {}; }
    cx.timer.every(30000, (cx) => { this.save(); cx.notify(); }); // the rows' times
    this.load = {}; // machine ("" here) -> { used, total } in kB, or null where /proc/meminfo can't be read
    cx.timer.every(10000, (cx) => this.poll(cx));
    try { this.opened = new Set(JSON.parse(localStorage.getItem("opened") ?? "[]")); } catch { this.opened = new Set(); }
    this.all = new Set(); // spaces whose big swarm shows every worker
    this.more = new Set(); // spaces showing all their rows, machines ("" here) all their spaces
    this.sums = new Map(); this.polls = new Map(); this.failed = new Map(); // per folder key (where()): summary, next read, why it failed
    this.asked = new Map(); // tab id -> when the rail last asked to put it away or bring it back
    this.mids = new Map(); // machine name -> a number for its elements' ids (a name is never part of one)
    cx.timer.every(5000, (cx) => this.swarms(cx));
    this.nudged = new Set(); // hung agents nudged from the toast ("<machine>:<db>:<name>"), until they aren't hung
    this.listed = null; // `hc machine ls --json`'s machines, null until read
    this.said = {}; // machine -> what is under way there, or what its last action failed with
    this.menu = null; // the machine whose menu is open
    this.removing = null; // the machine whose menu asks to confirm its removal
    this.renaming = null; // the machine whose heading is a field
    this.name = InputState.new({});
    this.name.on("submit", (_e, cx) => this.rename(cx));
    this.refreshMachines(cx);
    cx.timer.every(15000, (cx) => this.refreshMachines(cx));
  }

  // Each space folder's swarm, one `swarm state --view summary` per folder, then this computer's swarms with no space.
  // One round at a time, the next no sooner than twice as long as this one took (50 swarms of 500 agents read in ~20 s);
  // a folder with no swarm, or whose read fails, waits longer each time (pollNext). A swarm that stops answering keeps
  // its last summary and says why in one line at the rail's foot.
  swarms(cx) {
    if (this.reading || Date.now() < (this.round ?? 0)) return;
    this.reading = true;
    const t0 = Date.now();
    const at = [...new Map(spaces().filter((s) => s.folder).map((s) => [where(s), { folder: s.folder, on: s.machine ?? null }])).entries()];
    cx.spawn(async (cx) => {
      const read = async (key, folder, on) => {
        const p = this.polls.get(key);
        if (p && Date.now() < p.next) return;
        const t1 = Date.now();
        let j = null, err = null;
        try {
          const r = await swarm(folder, on, ["state", "--json", "--view", "summary"]);
          if (r.code !== 0) err = line(r.stderr || r.stdout) || `swarm exited ${r.code}`;
          else if (!(j = sumOf(JSON.parse(r.stdout)))) err = "swarm state printed no summary";
        } catch (e) { err = line(e?.message ?? e) || "swarm state failed"; }
        const fails = err ? (p?.fails ?? 0) + 1 : 0;
        this.polls.set(key, { next: Date.now() + pollNext(Date.now() - t1, !err, j?.active, fails), fails });
        if (err && this.sums.has(key)) this.failed.set(key, `${base(folder)}${on ? ` on ${on}` : ""}: ${err}`);
        if (err) return;
        this.failed.delete(key);
        if (j.active) this.sums.set(key, { ...j, on, folder }); else this.sums.delete(key);
      };
      const keys = new Set(at.map(([k]) => k));
      for (const [key, { folder, on }] of at) await read(key, folder, on);
      try {
        const r = await swarm(home(), null, ["state", "--json", "--view", "swarms"]);
        const seen = new Set([...keys].map((k) => this.sums.get(k)).filter((m) => m && !m.on).map((m) => m.db));
        for (const w of r.code === 0 ? swarmsOf(JSON.parse(r.stdout)) : []) {
          const key = `:${w.folder}`;
          if (seen.has(w.db) || keys.has(key)) continue;
          keys.add(key);
          await read(key, w.folder, null);
        }
      } catch {}
      for (const m of [this.sums, this.polls, this.failed]) for (const k of m.keys()) if (!keys.has(k)) m.delete(k);
      this.reading = false;
      this.round = Date.now() + Math.max(5000, 2 * (Date.now() - t0));
      const mine = [...this.sums.values()], js = JSON.stringify(mine);
      if (js !== this.sharedJs) { this.sharedJs = js; setShared("rw-rail.swarms", mine); } // rw-bar's Needs you counts their questions
      cx.notify();
    });
  }

  // `r.ask`: the agent's question (slice 8), shown above its pane.
  open(r, cx) {
    if (allShown(layout())) showAll(run, false);
    if (r.pane && r.ask) openAsk(run, panes(), r.pane, r.ask, (f) => cx.timer.after(300, f));
    else if (r.pane) run("pane.focus", { pane: r.pane }); else run("terminal.peek", { terminal: r.t.address });
    if (this.remember(r.t.address)) cx?.notify();
  }
  remember(address) {
    if (this.opened.has(address)) return false;
    this.opened.add(address);
    for (const a of this.opened) if (this.opened.size > 200) this.opened.delete(a); else break;
    localStorage.setItem("opened", JSON.stringify([...this.opened]));
    return true;
  }

  // The swarm tab (slice 7): the overview, mod rw-swarm, split beside the communicator's terminal, on the left, and that
  // tab moved first; one already open is focused. With no communicator pane here the overview is a tab of its own.
  openSwarm(s, sw, cx) {
    if (allShown(layout())) showAll(run, false);
    const ps = panes(), props = { folder: sw.sum.folder, machine: s.machine ?? null };
    const comms = sw.block.find((it) => it.comms)?.r.pane, tab = comms && ps.find((p) => p.pane === comms)?.tab;
    const have = ps.find((p) => p.mod === "rw-swarm" && (tab ? p.tab === tab : s.tabs.some((x) => x.id === p.tab)));
    if (have) return run("pane.focus", { pane: have.pane });
    if (tab) {
      run("pane.split", { pane: comms, direction: "right", mod: "rw-swarm", props });
      // Splits only go right or down: swap the two once the new pane has its place (swap goes by geometry).
      cx.timer.after(300, () => { run("pane.focus", { pane: comms }); run("pane.swap", { direction: "right" }); });
      return run("tab.move", { id: tab, index: 1 });
    }
    run("tab.new", { space: s.id, mod: "rw-swarm", props });
    const made = spaces().find((x) => x.id === s.id)?.tabs.find((x) => x.active);
    if (made) run("tab.move", { id: made.id, index: 1 });
  }

  // The shown space's machine's memory in use, for the foot.
  poll(cx) {
    const on = spaces().find((s) => s.active)?.machine ?? null;
    if (this.loading) return;
    this.loading = true;
    cx.spawn(async (cx) => {
      let v = null;
      try {
        const r = await exec("cat", ["/proc/meminfo"], { on });
        const kb = (k) => Number(r.stdout.match(new RegExp(`^${k}:\\s+(\\d+)`, "m"))?.[1]);
        const total = kb("MemTotal"), avail = kb("MemAvailable");
        if (r.code === 0 && total > 0 && avail >= 0) v = { used: total - avail, total };
      } catch {}
      this.loading = false;
      this.load[on ?? ""] = v;
      cx.notify();
    });
  }

  // The first hung swarm agent you haven't nudged: "<agent> is hung", what it holds, Nudge and Open.
  hung(t, sums, ps) {
    const key = (j, a) => `${j.on ?? ""}:${j.db}:${a.name}`;
    const all = sums.flatMap((j) => (j.agents ?? []).filter((a) => a.hung).map((a) => ({ j, a, k: key(j, a) })));
    for (const k of this.nudged) if (!all.some((h) => h.k === k)) this.nudged.delete(k);
    const h = all.find((x) => !this.nudged.has(x.k));
    if (!h) return null;
    const { j, a, k } = h, address = a.hc && (j.on && !a.hc.includes("/") ? `${j.on}/${a.hc}` : a.hc);
    const btn = (id, label, border, action) => div().id(id).flex_none().px(10).py(4).rounded(8).text_size(12.5).cursor_pointer()
      .when(border, (el) => el.border(1).border_color(t.blocked + "66").text_color(t.foreground)).when(!border, (el) => el.text_color(t.muted))
      .hover((s) => s.bg(t.hover)).on_click(action).child(label);
    return v_flex().id("hung-toast").flex_none().mx(10).mb(4).px(12).py(10).gap(6).rounded(10).border(1).border_color(t.blocked + "66")
      .bg(t.blocked + "14").text_size(12.5)
      .child(div().font_medium().text_color(t.blocked).child(`${a.name} is hung`))
      .child(div().line_height(1.4).whitespace_normal().text_color(t.foreground)
        .child(`No answer to the liveness check. ${a.task ? `It holds #${a.task.id}.` : "It holds no task."}`))
      .child(h_flex().gap(8)
        .child(btn("hung-nudge", "Nudge", true, (_e, cx) => {
          this.nudged.add(k); cx.notify();
          swarm(j.folder, j.on, nudgeArgs(a.name)).catch(() => {});
        }))
        .when(Boolean(address), (el) => el.child(btn("hung-open", "Open", false, (_e, cx) =>
          this.open({ t: { address }, pane: ps.find((p) => p.terminal === address)?.pane ?? null }, cx)))));
  }

  // What failed (a swarm that stopped answering, a space that couldn't be drawn), in one line.
  trouble(t, fails) {
    if (!fails.length) return null;
    return div().id("trouble").flex_none().mx(10).mb(4).px(10).truncate().text_size(11.5).text_color(t.blocked)
      .child(`${fails[0]}${fails.length > 1 ? ` (and ${fails.length - 1} more)` : ""}`);
  }

  // "N more": shows everything under `key` (a space's id: its rows; "m:<machine>": its spaces).
  moreLine(t, id, text, key) {
    return div().id(id).flex_none().mx(4).px(6).h(ROW).flex().items_center().rounded(7).text_size(11.5).text_color(t.dim)
      .cursor_pointer().hover((st) => st.bg(t.hover)).on_click((_e, cx) => { this.more.add(key); cx.notify(); }).child(text);
  }

  foot(t, sp) {
    const m = sp.find((s) => s.active)?.machine ?? null;
    const l = this.load[m ?? ""];
    if (!l) return null;
    const g = (kb) => Math.round(kb / 1048576);
    return v_flex().flex_none().px(20).pt(8).pb(10).gap(6).text_size(11.5).text_color(t.dim)
      .child(div().truncate().child(`${m ?? "This computer"} · ${g(l.used)} of ${g(l.total)} G in use`))
      .child(div().h(3).rounded(2).bg(t.border).child(div().h(3).rounded(2).bg(t.dim).w(`${Math.round((100 * l.used) / l.total)}%`)));
  }

  // hc reconnects a machine by itself once it answers again; Retry only reads its state now.
  refreshMachines(cx) {
    cx.spawn(async (cx) => {
      try {
        const r = await hc(["machine", "ls", "--json"]), ms = r.code === 0 ? JSON.parse(r.stdout)?.machines : null;
        if (Array.isArray(ms)) this.listed = ms.filter((x) => typeof x?.name === "string").slice(0, 200);
      } catch {}
      cx.notify();
    });
  }

  // `hc machine <verb> --json -- <names>` for machine `m`: `doing` meanwhile, the error after. After `--`, a name that
  // starts with a dash is still a name.
  machineDo(m, doing, [verb, ...names], cx, then = null) {
    this.menu = null;
    this.removing = null;
    this.said[m] = doing;
    cx.notify();
    cx.spawn(async (cx) => {
      let error = null;
      try {
        const r = await hc(["machine", verb, "--json", "--", ...names]);
        if (r.code !== 0) {
          try { error = JSON.parse(r.stdout || r.stderr).error?.message; } catch {}
          error ||= (r.stderr || r.stdout || "it failed").trim();
        }
      } catch (e) { error = String(e?.message ?? e); }
      if (error) this.said[m] = `Couldn't: ${line(error, 300)}`; else { delete this.said[m]; then?.(); }
      this.refreshMachines(cx);
      cx.notify();
    });
  }

  rename(cx) {
    const m = this.renaming, to = this.name.value().trim();
    this.renaming = null;
    if (m && to && to !== m) this.machineDo(m, "Renaming…", ["rename", m, to], cx);
    else cx.notify();
  }

  // Logging in may ask a password or code, so it runs in a terminal shown over the tab, as machine-add does; the
  // terminal stays until Enter so what hc said can be read.
  login(m, cx) {
    this.menu = null;
    cx.spawn(async (cx) => {
      let address = null;
      try {
        const r = await hc(["run", "--bg", "--json", "--no-parent", "--name", `login-${this.mid(m)}`, "--", "sh", "-c",
          'hc machine login -- "$1"; printf "\\nPress Enter to close. "; read _', "sh", m]);
        if (r.code === 0) address = JSON.parse(r.stdout).address;
      } catch {}
      if (address) run("terminal.peek", { terminal: address });
      else this.said[m] = `Couldn't open a terminal for it. Run hc machine login in one.`;
      cx.notify();
    });
  }

  mid(m) {
    if (!this.mids.has(m)) this.mids.set(m, this.mids.size);
    return this.mids.get(m);
  }

  hide(m, on) {
    const h = shared(HIDDEN) ?? [];
    setShared(HIDDEN, on ? [...h.filter((x) => x !== m), m] : h.filter((x) => x !== m));
  }

  note(t, id, text) {
    return div().id(id).flex_none().px(10).text_size(11.5).line_height(1.4).text_color(t.dim).child(text);
  }

  act(t, id, label, action) {
    return div().id(id).flex_none().px(8).py(1).rounded(6).border(1).border_color(t.border).text_size(11.5).font_normal()
      .text_color(t.foreground).cursor_pointer().hover((s) => s.bg(t.hover)).on_click(action).child(label);
  }

  // A machine's menu, and in its place the question before removing it.
  menuOf(t, mc) {
    const m = mc.name, n = this.mid(m), shown = line(m, 60);
    const item = (id, text, action, red = false) => div().id(`${id}-${n}`).px(10).py(6).rounded(6).text_size(12.5)
      .font_normal().text_color(red ? t.blocked : t.foreground).cursor_pointer().hover((s) => s.bg(t.hover)).on_click(action).child(text);
    // terminals() costs ~0.1 ms a terminal: read only while the removal question shows
    const ns = mc.spaces.length, k = this.removing === m ? terminals().filter((x) => x.address.startsWith(`${m}/`)).length : 0;
    const content = this.removing === m
      ? v_flex().w(270).p(14).gap(10).rounded(10).bg(t.popover).border(1).border_color(t.border).shadow_lg().text_size(12.5)
        .font_normal().text_color(t.foreground)
        .child(div().text_size(14).font_semibold().child(`Remove ${shown}?`))
        .child(div().line_height(1.5).text_color(t.muted).child(`Herdr forgets this machine and its ${ns} ${ns === 1 ? "space leaves" : "spaces leave"
          } the window. ${k === 1 ? "The terminal" : `The ${k} terminals`} running there keep${k === 1 ? "s" : ""} running. Add it again to get them back.`))
        .child(h_flex().gap(8).justify_end()
          .child(div().id(`remove-no-${n}`).px(12).py(5).rounded(8).border(1).border_color(t.border).cursor_pointer()
            .hover((s) => s.bg(t.hover)).on_click((_e, cx) => { this.removing = null; this.menu = null; cx.notify(); }).child("Cancel"))
          .child(div().id(`remove-yes-${n}`).px(12).py(5).rounded(8).bg(t.blocked).text_color(t.background).font_semibold().cursor_pointer()
            .on_click((_e, cx) => this.machineDo(m, "Removing…", ["rm", m], cx, () => this.hide(m, false))).child(`Remove ${shown}`)))
      : v_flex().w(190).p(5).rounded(10).bg(t.popover).border(1).border_color(t.border).shadow_lg()
        .child(item("rename", "Rename", (_e, cx) => {
          this.menu = null; this.renaming = m; this.name.set_value(m); this.name.focus(); cx.notify();
        }))
        .child(item("hide", "Hide from the rail", (_e, cx) => { this.menu = null; this.hide(m, true); cx.notify(); }))
        .child(item("update", "Update Herdr there", (_e, cx) => this.machineDo(m, "Updating Herdr there…", ["update", m], cx)))
        .child(item("login", "Log in again", (_e, cx) => this.login(m, cx)))
        .child(div().h(1).mx(4).my(3).bg(t.border))
        .child(item("remove", "Remove…", (_e, cx) => { this.removing = m; cx.notify(); }, true));
    return Popover.new(`menu-${n}`).anchor("top_right").open(this.menu === m)
      .on_open_change((open, cx) => { this.menu = open ? m : null; if (!open) this.removing = null; cx.notify(); })
      .trigger(h_flex().id(`menu-button-${n}`).size(22).flex_none().items_center().justify_center().rounded(6).text_color(t.dim)
        .when(this.menu === m, (el) => el.bg(t.hover)).hover((s) => s.bg(t.hover).text_color(t.foreground))
        .child(svg("mods/rw-rail/dots.svg").size(14)))
      .content(content);
  }

  // A machine's heading, as a field while it is renamed, then a line for its state or what its last action said.
  heading(t, mc, now) {
    const m = mc.name, n = this.mid(m), off = mc.state === "unreachable";
    const head = h_flex().id(`machine-${m ? n : "local"}`).h(m ? 39 : 27).flex_none().mt(m ? 14 : 0).mb(2).pt(m ? 12 : 4).px(8).gap(7)
      .items_center().when(Boolean(m), (el) => el.border_t(1).border_color(t.border))
      .text_size(12).font_semibold().text_color(off ? t.blocked : t.foreground)
      .child(svg(`mods/workspace-chrome/${m ? "server" : "monitor"}.svg`).size(13).flex_none().text_color(off ? t.blocked : t.dim));
    if (m && this.renaming === m) return [
      head.child(div().id(`rename-${n}`).flex_1().min_w(0).h(26).px(8).flex().items_center().rounded(6).border(1).border_color(t.accent)
        .bg(t.background).font_normal().cursor_text()
        .on_key_down((e, cx) => { if (e.key === "escape") { this.renaming = null; cx.stop_propagation(); cx.notify(); } })
        .child(Input.new(this.name).h_full().text_size(12).text_color(t.foreground))),
      this.note(t, `rename-note-${n}`, "Enter to save · Esc to cancel")];
    const state = m && mc.state && !["connected", "unreachable"].includes(mc.state) ? mc.state.replace(/_/g, " ") : null;
    const at = mc.since && new Date(mc.since).toDateString() === new Date(now).toDateString()
      ? ` since ${new Date(mc.since).toTimeString().slice(0, 5)}` : mc.since ? ` for ${dur(now - mc.since)}` : "";
    return [
      head.child(div().flex_1().min_w(0).truncate().child(m ? line(m, 60) : "This computer"))
        .when(off, (el) => el.child(mark(t, "hung")).child(this.act(t, `retry-${n}`, "Retry", (_e, cx) => this.refreshMachines(cx))))
        .when(Boolean(state), (el) => el.child(div().flex_none().text_size(11.5).font_normal().text_color(t.dim).child(state)))
        .when(mc.state === "needs_login", (el) => el.child(this.act(t, `login-${n}`, "Log in", (_e, cx) => this.login(m, cx))))
        .when(Boolean(m), (el) => el.child(this.menuOf(t, mc))),
      ...(off ? [this.note(t, `off-${n}`, `Can't reach it${at}. Its terminals keep running there.`)] : []),
      ...(m && this.said[m] ? [this.note(t, `said-${n}`, this.said[m])] : [])];
  }

  fold(id, cx) {
    this.folded.has(id) ? this.folded.delete(id) : this.folded.add(id);
    localStorage.setItem("folded", JSON.stringify([...this.folded]));
    cx.notify();
  }

  // Saved at most every 2 s (a big window's times are 100s of kB), and kept to CHANGED entries.
  track(rows, now, at, cx) {
    if (!stamp(this.changed, rows, now, at)) return;
    prune(this.changed, new Set(rows.map((r) => r.t.address)), now, CHANGED);
    this.dirty = true;
    if (now - (this.savedAt ?? 0) >= 2000) this.save();
    else if (!this.flushing) { this.flushing = true; cx.timer.after(2000, () => { this.flushing = false; this.save(); }); }
  }
  save() {
    if (!this.dirty) return;
    this.dirty = false; this.savedAt = Date.now();
    localStorage.setItem("changed", JSON.stringify(this.changed));
    setShared("rw-rail.changed", this.changed); // rw-pane's headers say the same times
  }

  tree(t, lines) {
    const half = ROW / 2;
    return lines.map((l) => div().relative().w(10).h(ROW).flex_none()
      .when(l !== "", (el) => el.child(div().absolute().left(4).top(0).w(1).h(l === "└" ? half : ROW).bg(t.input)))
      .when(l === "├" || l === "└", (el) => el.child(div().absolute().left(4).top(half).w(6).h(1).bg(t.input))));
  }

  // `text`: a swarm row's own what and side (swarmText).
  row(t, r, tabName, on, now, text = null) {
    const shell = !AGENT.has(r.mark);
    let { name, what } = rowText(r.t, r.mark, tabName, this.home);
    let sideText = since(r.mark, this.changed[r.t.address]?.at, now);
    if (text) ({ name, what, side: sideText } = text);
    return h_flex().id(`row-${r.t.address}`).h(ROW).flex_none().mx(4).px(6).gap(8).items_center().rounded(7)
      .text_size(12.5).cursor_pointer()
      .when(on, (el) => el.bg(t.raised))
      .when(!on, (el) => el.hover((s) => s.bg(t.hover)))
      .on_click((_e, cx) => this.open(r, cx))
      .children(this.tree(t, r.lines))
      .child(div().flex_none().max_w(120).truncate().font_medium().text_color(shell ? t.muted : t.foreground)
        .when(shell, (el) => el.font_family(this.mono).text_size(12))
        .child(name))
      .child(div().flex_1().min_w(0).truncate().text_size(11.5).text_color(t.dim).child(what))
      .when(Boolean(sideText), (el) => el.child(div().flex_none().text_size(11.5).text_color(r.mark === "asks" || r.mark === "hung" ? t.blocked : t.dim).child(sideText)))
      .child(mark(t, r.mark));
  }

  counts(t, rows) {
    const n = {};
    for (const r of rows) { const k = AGENT.has(r.mark) ? r.mark : "shell"; n[k] = (n[k] ?? 0) + 1; }
    const count = (k, icon) => h_flex().flex_none().gap(4).items_center().text_size(11.5)
      .text_color(k === "asks" || k === "hung" ? t.blocked : t.muted).child(icon).child(String(n[k]));
    return [...ORDER.filter((k) => n[k]).map((k) => count(k, mark(t, k))),
      ...(n.shell ? [count("shell", svg("mods/workspace-chrome/terminal.svg").size(11).flex_none().text_color(t.dim))] : [])];
  }

  // A swarm's block: a heading (tag, agents, tasks left), its agents' rows, and past 8 agents two counts that show all.
  block(t, s, sw, tabNames, shownTerm, now) {
    const sum = sw.sum;
    const tag = (sum.comms ?? "").replace(/-?comms\d*$/, "");
    const left = ["open", "claimed", "blocked"].reduce((n, k) => n + (sum.counts?.[k] ?? 0), 0);
    const n = sum.agents.length;
    const rows = this.capped(t, `b:${s.id}`, sw.block.flatMap((it) => {
      if (it.fold) return [() => h_flex().id(`fold-${s.id}-${it.fold}`).h(ROW).flex_none().mx(4).px(6).gap(8).items_center().rounded(7)
        .text_size(12.5).cursor_pointer().hover((st) => st.bg(t.hover))
        .on_click((_e, cx) => { this.all.add(s.id); cx.notify(); })
        .child(div().flex_1().min_w(0).truncate().font_medium().text_color(t.foreground)
          .child(it.fold === "working" ? `${it.n} ${it.more ? "more " : ""}working` : `${it.n} ${it.more ? "more " : ""}idle`))
        .child(div().flex_none().text_size(11.5).text_color(t.dim).child("show"))
        .child(mark(t, it.fold))];
      const opened = sw.big && !it.comms && it.r.mark !== "asks" && it.r.mark !== "hung" && this.opened.has(it.r.t.address);
      const text = swarmText(it, this.changed[it.r.t.address]?.at, now, opened);
      const asks = it.r.mark === "asks" && (sum.needs ?? []).some((q) => q.kind === "question" && q.agent === it.a.name);
      const root = asks ? { ...it.r, ask: { folder: sum.folder, machine: s.machine ?? null, agent: it.a.name } } : it.r;
      return [root, ...it.kids].map((r, i) => () => this.row(t, r, tabNames.get(r.t.address), r.t.address === shownTerm, now, i ? null : text));
    }), (f) => f());
    if (this.all.has(s.id) && n > 8) rows.push(h_flex().id(`fewer-${s.id}`).h(ROW).flex_none().mx(4).px(6).items_center().rounded(7)
      .text_size(11.5).text_color(t.dim).cursor_pointer().hover((st) => st.bg(t.hover))
      .on_click((_e, cx) => { this.all.delete(s.id); cx.notify(); }).child("show fewer"));
    return v_flex().id(`swarm-${s.id}`).flex_none().mx(4).mb(6).pt(5).pb(4).rounded(8).border(1).border_color(t.input).bg(t.swarm_block ?? t.chrome)
      .child(h_flex().id(`swarm-head-${s.id}`).mx(4).px(6).pt(3).pb(5).gap(7).items_center().rounded(7).text_size(11.5).text_color(t.muted)
        .cursor_pointer().hover((st) => st.bg(t.hover).text_color(t.foreground)).on_click((_e, cx) => this.openSwarm(s, sw, cx))
        .child(svg("mods/rw-rail/diamond.svg").size(8).flex_none().text_color(t.muted))
        .child(div().flex_1().min_w(0).truncate().child(`Swarm${tag ? ` ${tag}` : ""} · ${n} ${n === 1 ? "agent" : "agents"} · ${left} left`)))
      .children(rows);
  }

  // `fly`: the collapsed rail's hover card, always open and not marked as shown. `sw`: the space's swarm (swarmOf).
  space(t, s, rows, tabNames, shownTerm, now, fly = false, sw = null) {
    const folded = !fly && this.folded.has(s.id);
    const open = !folded && rows.length > 0;
    const tabs = s.tabs.length;
    const stop = (_e, cx) => cx.stop_propagation();
    return v_flex().id(`${fly ? "fly" : "space"}-${s.id}`).flex_none().rounded(9).when(s.active && !fly, (el) => el.bg(t.selected)).when(open, (el) => el.pb(6))
      .child(h_flex().id(`head-${s.id}`).h(32).pl(4).pr(10).gap(4).items_center().cursor_pointer()
        .when(!s.active || fly, (el) => el.rounded(9).hover((st) => st.bg(t.hover)))
        .on_click((_e, cx) => { if (allShown(layout())) showAll(run, false); else if (s.active && !fly) return this.fold(s.id, cx); run("space.select", { id: s.id }); })
        .child(h_flex().id(`fold-${s.id}`).size(18).flex_none().items_center().justify_center().rounded(5).text_color(t.dim)
          .hover((st) => st.bg(t.hover).text_color(t.foreground))
          .on_mouse_down("left", stop).on_click((_e, cx) => { cx.stop_propagation(); this.fold(s.id, cx); })
          .child(svg(`mods/workspace-chrome/chevron-${folded ? "right" : "down"}.svg`).size(12)))
        .child(div().flex_1().min_w(0).truncate().text_size(14).font_bold().text_color(t.foreground).child(line(s.name, 80)))
        .when(folded, (el) => el.child(h_flex().flex_none().gap(8).children(this.counts(t, rows))))
        .when(!folded, (el) => el.child(div().flex_none().text_size(11).text_color(t.dim).child(`${tabs} ${tabs === 1 ? "tab" : "tabs"}`))))
      // The space's rows hang on a guide line under its chevron.
      .when(open, (el) => el.child(v_flex().ml(12).pl(2).border_l(1).border_color(t.border)
        .when(Boolean(sw), (el) => el.child(this.block(t, s, sw, tabNames, shownTerm, now)))
        .children(this.capped(t, s.id, (sw ? sw.rest : rows), (r) => this.row(t, r, tabNames.get(r.t.address), r.t.address === shownTerm, now)))));
  }

  // A list of rows: past ROWS, the first ROWS - 1 and a line that shows the rest (`key`: the space's id).
  capped(t, key, xs, draw) {
    if (xs.length <= ROWS || this.more.has(key)) return xs.map(draw);
    return [...xs.slice(0, ROWS - 1).map(draw), this.moreLine(t, `more-${key}`, `${xs.length - ROWS + 1} more`, key)];
  }

  // To tiles, or back to the width the rail had (shared with workspace-chrome's toggle).
  toggle(narrow) {
    const width = find(layout(), "sidebar")?.size?.px;
    if (!narrow) setShared("sidebar.width", width);
    setShared("sidebar.collapsed", !narrow);
    run("layout.resize", { id: "sidebar", px: narrow ? (shared("sidebar.width") ?? 268) : 64 });
  }

  button(t, id, icon, action) {
    return h_flex().id(id).size(26).flex_none().items_center().justify_center().rounded(7).text_color(t.dim)
      .hover((s) => s.bg(t.hover).text_color(t.foreground)).on_click(action)
      .child(svg(`mods/workspace-chrome/${icon}.svg`).size(14));
  }

  // One tile per space with its agents' marks; hovering it opens the space's rows beside it.
  tile(t, s, rows, tabNames, shownTerm, now, sw) {
    const roll = rollOf(rows);
    const trigger = v_flex().id(`tile-${s.id}`).flex_none().items_center().gap(6).cursor_pointer()
      .on_click(() => run("space.select", { id: s.id }))
      .child(h_flex().size(40).items_center().justify_center().rounded(10).border(1)
        .bg(s.active ? t.selected : t.raised).border_color(s.active ? t.accent : t.border)
        .text_size(12).font_semibold().text_color(roll.length ? t.foreground : t.muted).child(abbrev(line(s.name, 80))))
      .child(h_flex().h(7).gap(3).items_center().children(roll.map((k) => mark(t, k, 7))));
    return HoverCard.new(`hover-${s.id}`).anchor("top_left").open_delay(150).trigger(trigger)
      // The card hangs from the tile's bottom left; the margins move it beside the tile, level with its top.
      .content(v_flex().ml(52).mt(-54).w(290).py(4).rounded(10).bg(t.popover).border(1).border_color(t.border).shadow_lg()
        .child(this.space(t, s, rows, tabNames, shownTerm, now, true, sw)));
  }

  // The All swarms row: how many run and how many of their agents ask you; it shows the view, or the tabs again.
  allRow(t, sums, shown) {
    const n = asksIn(sums).length;
    return v_flex().id("all-swarms").flex_none().mx(10).mt(6).px(10).py(8).gap(2).rounded(9).cursor_pointer()
      .when(shown, (el) => el.bg(t.selected)).when(!shown, (el) => el.hover((st) => st.bg(t.hover)))
      .on_click(() => showAll(run, !shown))
      .child(h_flex().gap(8).items_center().text_size(13).font_medium().text_color(t.foreground)
        .child(svg("mods/rw-rail/diamond.svg").size(8).flex_none().text_color(t.foreground)).child("All swarms"))
      .child(div().text_size(11.5).text_color(n ? t.blocked : t.dim).child(`${sums.length} running${n ? ` · ${n} ${n === 1 ? "needs" : "need"} you` : ""}`));
  }

  render(cx) {
    const t = theme();
    const now = Date.now();
    this.home = home();
    this.mono = settings().font_family ?? "JetBrains Mono"; // once a render: a host call per row adds up
    const all = looked(terminals(), agents());
    const byAddr = new Map(all.filter((x) => x.state === "live").map((x) => [x.address, x]));
    const ps = panes();
    const sp = spaces();
    if (!((sp.find((s) => s.active)?.machine ?? "") in this.load)) this.poll(cx); // a machine not read yet
    const shownTerm = focused()?.terminal ?? null;
    // The All swarms view gives way to the tabs once another tab is shown (a pill, a key, a click elsewhere).
    const shownAll = allShown(layout()), tab = focused()?.tab ?? null;
    if (shownAll && this.viewTab !== undefined && tab !== this.viewTab) showAll(run, false);
    this.viewTab = shownAll ? (this.viewTab === undefined ? tab : this.viewTab) : undefined;
    const sums = Array.isArray(shared("rw-rail.swarms")) ? shared("rw-rail.swarms") : [];
    const tabName = new Map(sp.flatMap((s) => s.tabs).filter((tab) => tab.named).map((tab) => [tab.id, tab.name]));
    const tabNames = new Map(ps.filter((p) => p.terminal).map((p) => [p.terminal, tabName.get(p.tab)]));
    if (!this.started) { this.started = true; this.swarms(cx); }
    const swBy = new Map();
    const ids = new Set(sp.map((s) => s.id));
    // A space that can't be drawn is one line at the foot; the others draw.
    const broken = [];
    const rowsBy = new Map(sp.map((s) => {
      try {
        const sum = sumFor(sums, s, ids);
        const rows = rowsOf(s, ps, byAddr, swarmAddrs(sum, s.machine ?? null));
        if (!sum) return [s.id, rows];
        const sw = { ...swarmOf(rows, sum, byAddr, s.machine ?? null, this.opened, this.all.has(s.id)), sum };
        swBy.set(s.id, sw);
        return [s.id, sw.rows];
      } catch (e) {
        broken.push(`Couldn't draw ${line(s.name, 40)}: ${line(e?.message ?? e, 120)}`);
        return [s.id, []];
      }
    }));
    // A large swarm (slice 9): the tabs of workers you haven't opened are put away, so the bar shows the ones you have.
    for (const [id, sw] of swBy) {
      const o = settleOf(new Set(sw.put), new Set(sw.hot), ps, sp.find((s) => s.id === id).tabs);
      for (const tab of due(this.asked, o.settle, now)) run("tab.settle", { id: tab });
      for (const tab of due(this.asked, o.unsettle, now)) run("tab.unsettle", { id: tab });
      for (const a of o.opened) this.remember(a);
    }
    // Folds and "show all" of spaces that are gone.
    if (sp.length) {
      const n = this.folded.size;
      for (const set of [this.folded, this.all, this.more]) for (const id of set) if (!ids.has(id.replace(/^b:/, "")) && !id.startsWith("m:")) set.delete(id);
      if (this.folded.size !== n) localStorage.setItem("folded", JSON.stringify([...this.folded]));
    }
    // An agent alone in its tab: the tab's change time is the app's own, kept while the rail isn't shown.
    const tabOf = new Map(sp.flatMap((s) => s.tabs).map((tab) => [tab.id, tab]));
    const changedAt = new Map(ps.filter((p) => p.terminal && tabOf.get(p.tab)?.panes === 1).map((p) => [p.terminal, tabOf.get(p.tab).changed_at]));
    this.track([...rowsBy.values()].flat(), now, (a) => changedAt.get(a) ?? null, cx);
    setAgentOrder([...rowsBy.values()].flat().filter((r) => AGENT.has(r.mark) && r.pane).map((r) => r.t.address));

    // A heading per machine once a space or a machine isn't this computer; spaces() lists this computer's first.
    const ms = machinesOf(sp, machines().map((m) => m.name), this.listed, shared(HIDDEN) ?? []);
    const many = ms.length > 1;
    const narrow = (find(layout(), "sidebar")?.size?.px ?? Infinity) < NARROW;
    // An unreachable machine's spaces: dimmed, without rows or marks (their state is unknown).
    const dim = (el) => div().flex_none().opacity(0.45).child(el);
    const items = ms.filter((mc) => !mc.hidden).flatMap((mc) => {
      const off = mc.state === "unreachable";
      // Past SPACES spaces, the first ones and the shown one, then a line that shows the rest.
      const key = `m:${mc.name ?? ""}`, cut = mc.spaces.length > SPACES && !this.more.has(key);
      const shown = cut ? mc.spaces.filter((s, i) => i < SPACES - 1 || s.active).slice(0, SPACES) : mc.spaces;
      const more = cut ? [this.moreLine(t, `more-spaces-${this.mid(mc.name)}`, narrow ? `+${mc.spaces.length - shown.length}`
        : `${mc.spaces.length - shown.length} more spaces`, key)] : [];
      if (narrow) {
        const rule = div().id(`machine-${this.mid(mc.name)}`).w(32).h(1).flex_none().bg(t.border);
        return [...(mc.name ? [rule] : []), ...shown.map((s) => off ? dim(this.tile(t, s, [], tabNames, shownTerm, now, null))
          : this.tile(t, s, rowsBy.get(s.id), tabNames, shownTerm, now, swBy.get(s.id))), ...more];
      }
      return [...(many ? this.heading(t, mc, now) : []), ...shown.map((s) => off ? dim(this.space(t, s, [], tabNames, shownTerm, now))
        : this.space(t, s, rowsBy.get(s.id), tabNames, shownTerm, now, false, swBy.get(s.id))), ...more];
    });
    // Hidden machines, one line each with how many agents there ask you.
    const hidden = ms.filter((mc) => mc.hidden);
    const asks = (mc) => mc.spaces.reduce((n, s) => n + rowsBy.get(s.id).filter((r) => r.mark === "asks").length, 0);
    if (!narrow && hidden.length) items.push(
      div().id("hidden-head").flex_none().mt(14).px(10).text_size(11.5).font_semibold().text_color(t.muted).child("Hidden"),
      ...hidden.map((mc) => h_flex().id(`hidden-${this.mid(mc.name)}`).h(28).flex_none().px(10).gap(8).items_center().text_size(12.5).text_color(t.muted)
        .child(div().flex_1().min_w(0).truncate().font_medium().child(line(mc.name, 60)))
        .when(asks(mc) > 0, (el) => el.child(h_flex().flex_none().gap(4).items_center().text_size(11.5).text_color(t.blocked)
          .child(mark(t, "asks")).child(String(asks(mc)))))
        .child(this.act(t, `show-${this.mid(mc.name)}`, "Show", () => this.hide(mc.name, false)))),
      this.note(t, "hidden-note", "Hidden: its spaces leave the rail and its terminals keep running. An agent that asks you there still counts in Needs you."));

    if (narrow) return v_flex().size_full().min_h(0).pt(10).gap(14).items_center().bg(t.chrome).text_size(13)
      .child(this.button(t, "rail-expand", "chevron-right", () => this.toggle(true)))
      .child(v_flex().id("rail-tiles").flex_1().min_h(0).w_full().pb(12).gap(14).items_center().overflow_y_scrollbar().children(items));
    return v_flex().size_full().min_h(0).bg(t.chrome).text_size(13)
      .when(sums.length > 1 || shownAll, (el) => el.child(this.allRow(t, sums, shownAll)))
      .child(h_flex().h(31).flex_none().pl(20).pr(14).pt(6).items_center().text_size(11.5).text_color(t.dim)
        .child(div().flex_1().child("Spaces")).child(this.button(t, "rail-collapse", "chevron-left", () => this.toggle(false))))
      .child(v_flex().id("rail-list").flex_1().min_h(0).px(10).pb(12).gap(8).overflow_y_scrollbar().children(items))
      .children([this.hung(t, sums, ps), this.trouble(t, [...broken, ...this.failed.values()]), this.foot(t, sp)].filter(Boolean));
  }
}
