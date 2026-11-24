// The rework's rail, direction B (U-RailB on the kit, swarm/herdr/kit): per machine, its swarms first (a header with the
// swarm's tag, counts and Talk, its repos as tags, a kit agent row per agent), then its spaces with whatever terminals
// no swarm holds, each saying how many it hides. Below, as before (swarm/herdr/UI-SPEC.md, slice 1 and Part II.2): spaces by machine, each with its tabs in order,
// a row per terminal (name, title or task, time, mark), on a guide line under the space's heading, sub-terminals under
// their parent on a thin line, a split tab's rows in a bracket, and a New tab row at the end of the shown space. A space folds to one line of counts. Click a row to focus its terminal; click a space
// to show it, click the shown one or any chevron to fold it. Each machine's swarms come from one `swarm state --json
// --view swarms` (sw-global §5); a swarm shows as a block first (slice 6) in its space (the one showing its communicator's
// terminal, homesOf), each agent row with its repo; its heading opens the swarm view (Part II.3), and its Side button on hover the side view (II.7). Each machine's
// heading (slice 10) has a menu (rename in place, hide, update, log in again, remove) and its state from
// `hc machine ls --json`: an unreachable machine's spaces dim with Retry; hidden machines are lines at the foot with Show.
// Once more than one swarm runs, an All swarms row heads the rail (slice 13); it shows rw-swarms in place of the tabs.
// A hung swarm agent is a row in the bar's Needs you (round 4, proposal 1), not a card here.

import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex, HoverCard, Popover, InputState, Input } from "gpui-base";
import { spaces, panes, terminals, agents, focused, machines, run, theme, settings, setAgentOrder, shared, setShared, home, exec, hc, layout, appHome, openOverlay, watchFolder } from "herdr";
import { AGENT, leftOf, abbrev, allShown, viewShown, swarmShown, showSwarm, showSide, leaving, asksIn, dur, line, looked, machinesOf, openAsk, pollNext, due, prune, rollOf, rowText, rowsOf, settleOf, showAll, since, stamp, sumFor, homesOf,
  swarmAddrs, swarmOf, swarmsOf, swarmText, tabGroups, closeOf, dropAt, animOn, Entering, addrOf, ciWord, repoName, SELECT, selectedAgent } from "./tree.js";
import { mark, look } from "./marks.js";
import * as kit from "./kit.js";

const ROW = 24; // fixed, so the tree lines of stacked rows meet
const ORDER = ["asks", "hung", "working", "done", "idle"]; // a folded space's counts, then its shells
const find = (node, id) => (node?.id === id ? node : (node?.children ?? []).reduce((f, c) => f ?? find(c, id), null));
const HIDDEN = "rw-rail.hidden"; // the names of the machines hidden from the rail (shared() persists it)
const NARROW = 160; // a sidebar narrower than this shows tiles (as workspace-chrome goes by width)
// The swarm CLI as the swarm mod runs it: this checkout's (mods/swarm links into it), or the skill's on another machine.
// `name`: the swarm it acts on (its --swarm; sw-global §2: never the folder's); `cwd` the repo a repo's command runs in.
const swarm = (cwd, on, args, name = null) => { const a = name ? ["--swarm", name, ...args] : args; return on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB SWARM_NAME=human "$HOME/.claude/skills/swarm/swarm" "$@"', "sh", ...a], { cwd: cwd ?? undefined, on })
  : exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", `${appHome()}/mods/swarm/../../../swarm`, ...a], { cwd: cwd ?? undefined }); };
const keyOf = (j) => `${j.on ?? ""}:${j.swarm}`;
const ROWS = 40; // a space's rows drawn before a "N more" line that shows the rest
const SPACES = 60; // a machine's spaces drawn (the shown one always among them) before a "N more spaces" line
const CHANGED = 5000; // agents' since-when times kept (the live ones always): the oldest of the rest go first
const QUIET = 30000; // a watched swarm db that hasn't changed is read again this often (its times and watchd still move), as rw-swarm
const SHOWN = 4; // a swarm's agent rows drawn before "N more, M working" (those that ask you or hang always show)
// A swarm row's kit status: asks, hung, working and gone from its mark, landing from its task, else idle.
const statusOf = (it) => (["asks", "hung", "working", "gone"].includes(it.r.mark) ? it.r.mark : it.a.task?.state === "in_review" ? "landing" : "idle");

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
    this.sums = new Map(); this.polls = new Map(); this.failed = new Map(); // per machine ("" here): its live swarms, next read, why it failed
    this.watched = new Map(); // per machine: { dir, dirty, at }, the local db's folder watched
    this.asked = new Map(); // tab id -> when the rail last asked to put it away or bring it back
    this.mids = new Map(); // machine name -> a number for its elements' ids (a name is never part of one)
    cx.timer.every(5000, (cx) => this.swarms(cx));
    this.listed = null; // `hc machine ls --json`'s machines, null until read
    this.lists = new Map(); this.ghosts = new Map(); // rows leaving (proposal 10): list key -> last [{k, x}]; "<list>|<k>" -> {x, after, at, list}
    this.ent = new Entering(); this.marks = new Map(); // motion (II.4a): what just came; address -> {kind, prev, at} for the marks' cross-fade
    this.motion = new kit.Motion(); // the kit's motions, for the swarm rows drawn with it
    this.said = {}; // machine -> what is under way there, or what its last action failed with
    this.menu = null; // the machine whose menu is open
    this.removing = null; // the machine whose menu asks to confirm its removal
    this.renaming = null; // the machine whose heading is a field
    this.name = InputState.new({});
    this.name.on("submit", (_e, cx) => this.rename(cx));
    this.drag = null; // { space, tab, y, live, pane }: a row pressed, dragged once it moves 4 px (Part II.2)
    this.overTab = null; // { space, tab }: the tab under the pointer
    this.keys = cx.focus_handle(); // holds the keyboard while a drag is live, for Escape
    this.retitle = null; // { tab, address }: the row whose tab is renamed in place (Part II.2)
    this.tabInput = InputState.new({});
    this.tabInput.on("submit", (_e, cx) => {
      if (this.retitle) run("tab.rename", { id: this.retitle.tab, name: this.tabInput.value().trim() }); // empty: its number again
      this.retitle = null; cx.notify();
    });
    this.refreshMachines(cx);
    cx.timer.every(15000, (cx) => this.refreshMachines(cx));
  }

  // Every swarm, one `swarm state --json --view swarms` per machine (sw-global §5): this computer's, then each connected
  // machine's with a space open here. One round at a time, the next no sooner than twice as long as this one took; a
  // machine whose read fails waits longer each time (pollNext) and keeps its swarms, saying why in one line at the foot.
  // A swarm with no live agent isn't listed. Which space shows each swarm is the render's (homesOf).
  swarms(cx) {
    if (this.reading || Date.now() < (this.round ?? 0)) return;
    this.reading = true;
    const t0 = Date.now(), hidden = shared(HIDDEN) ?? [];
    const at = new Map([["", { cwd: home(), on: null }]]);
    for (const s of spaces()) if (s.machine && !at.has(s.machine) && !hidden.includes(s.machine)
      && !(this.listed ?? []).some((m) => m.name === s.machine && m.state === "unreachable")) at.set(s.machine, { cwd: s.folder || null, on: s.machine });
    cx.spawn(async (cx) => {
      for (const [key, { cwd, on }] of at) {
        const p = this.polls.get(key), w = this.watched.get(key);
        if (p && Date.now() < p.next) continue;
        if (w && !w.dirty && Date.now() - w.at < QUIET) continue; // a watched db that hasn't changed: its swarms haven't
        if (w) { w.dirty = false; w.at = Date.now(); }
        const t1 = Date.now();
        let ws = null, db = null, err = null;
        try {
          const r = await swarm(cwd, on, ["state", "--json", "--view", "swarms"]);
          if (r.code !== 0) err = line(r.stderr || r.stdout) || `swarm exited ${r.code}`;
          else { const j = JSON.parse(r.stdout); ws = swarmsOf(j); db = typeof j?.db === "string" ? j.db : null; }
        } catch (e) { err = line(e?.message ?? e) || "swarm state failed"; }
        const live = (ws ?? []).filter((x) => x.active);
        const fails = err ? (p?.fails ?? 0) + 1 : 0;
        this.polls.set(key, { next: Date.now() + pollNext(Date.now() - t1, !err, live.length > 0, fails), fails });
        if (err) { if (this.sums.has(key)) this.failed.set(key, `${on ?? "this computer"}: ${err}`); continue; }
        this.failed.delete(key);
        this.sums.set(key, live.map((x) => ({ ...x, on })));
        if (!on && db) this.watch(key, db.replace(/\/[^/]*$/, ""));
      }
      for (const m of [this.sums, this.polls, this.failed, this.watched]) for (const k of m.keys()) if (!at.has(k)) m.delete(k);
      this.reading = false;
      this.round = Date.now() + Math.max(5000, 2 * (Date.now() - t0));
      const js = JSON.stringify([...this.sums.values()]), fails = JSON.stringify([...this.failed]);
      if (js !== this.readJs) { this.readJs = js; this.gen = (this.gen ?? 0) + 1; } // the render shares them, with their spaces
      else if (fails === this.failsJs) return; // nothing to draw again
      this.failsJs = fails;
      cx.notify();
    });
  }

  // As rw-swarm: a local db's folder changing marks its swarms stale; our own reads touch only the -shm index.
  watch(key, dir) {
    if (this.watched.get(key)?.dir === dir) return;
    const w = { dir, dirty: false, at: Date.now() };
    this.watched.set(key, w);
    (async () => {
      try { while (this.watched.get(key) === w) if ((await watchFolder(dir)).some((p) => !p.endsWith("-shm"))) w.dirty = true; }
      catch { if (this.watched.get(key) === w) this.watched.delete(key); }
    })();
  }

  // `r.ask`: the agent's question (slice 8), shown above its pane.
  open(r, cx) {
    if (r.mark === "gone") return; // its terminal is gone: nothing to show
    if (viewShown(layout())) showAll(run, false);
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

  // The swarm view (Part II.3): the swarm full width in place of the tabs, from its Overview.
  openSwarm(s, sw) {
    showSwarm(run, setShared, { swarm: sw.sum.swarm, folder: sw.sum.folder, machine: sw.sum.on ?? null, section: "overview" });
  }
  // The heading's Side button (II.7): the swarm's space shown, its swarm in the side panel beside the tabs.
  openSide(s) {
    if (!s.active) run("space.select", { id: s.id });
    if (viewShown(layout())) showAll(run, false);
    showSide(run, true);
  }

  // Each shown machine's memory in use (this computer's, and every reachable machine with a space here), for its heading.
  poll(cx) {
    if (this.loading) return;
    this.loading = true;
    const hidden = shared(HIDDEN) ?? [], off = new Set((this.listed ?? []).filter((m) => m.state === "unreachable").map((m) => m.name));
    const ons = [null, ...new Set(spaces().map((s) => s.machine).filter((m) => m && !hidden.includes(m) && !off.has(m)))];
    cx.spawn(async (cx) => {
      const drawn = (l) => l ? `${Math.round(l.used / 1048576)} ${Math.round(l.total / 1048576)} ${Math.round((100 * l.used) / l.total)}` : "";
      let changed = false;
      for (const on of ons) {
        let v = null;
        try {
          const r = await exec("cat", ["/proc/meminfo"], { on });
          const kb = (k) => Number(r.stdout.match(new RegExp(`^${k}:\\s+(\\d+)`, "m"))?.[1]);
          const total = kb("MemTotal"), avail = kb("MemAvailable");
          if (r.code === 0 && total > 0 && avail >= 0) v = { used: total - avail, total };
        } catch {}
        const was = this.load[on ?? ""];
        this.load[on ?? ""] = v;
        if (was === undefined || drawn(was) !== drawn(v)) changed = true; // its heading would draw differently
      }
      this.loading = false;
      if (changed) cx.notify();
    });
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

  // A machine's memory in use, on its heading: "12 of 94 G".
  loadOf(t, m) {
    const l = this.load[m ?? ""];
    if (!l) return null;
    const g = (kb) => Math.round(kb / 1048576);
    return div().flex_none().font_family(this.mono).text_size(kit.TYPE.meta).font_normal().text_color(t.dim)
      .child(`${g(l.used)} of ${g(l.total)} G`);
  }

  // hc reconnects a machine by itself once it answers again; Retry only reads its state now.
  refreshMachines(cx) {
    cx.spawn(async (cx) => {
      try {
        const r = await hc(["machine", "ls", "--json"]), ms = r.code === 0 ? JSON.parse(r.stdout)?.machines : null;
        if (Array.isArray(ms)) {
          const listed = ms.filter((x) => typeof x?.name === "string").slice(0, 200), js = JSON.stringify(listed);
          if (js === this.listedJs) return; // the same machines in the same states
          this.listedJs = js; this.listed = listed;
        }
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
    const button = h_flex().id(`menu-button-${n}`).size(22).flex_none().items_center().justify_center().rounded(6).text_color(t.dim)
      .when(this.menu === m, (el) => el.bg(t.hover)).hover((s) => s.bg(t.hover).text_color(t.foreground))
      .child(svg("mods/rw-rail/dots.svg").size(14));
    // A Popover only while open: one in the view keeps every spinner in the rail rebuilding the whole rail as it turns.
    if (this.menu !== m) return button.on_click((_e, cx) => { this.menu = m; this.removing = null; cx.notify(); });
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
          .child(look(div().id(`remove-yes-${n}`).px(12).py(5).rounded(8).cursor_pointer(), t, "solid")
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
    return Popover.new(`menu-${n}`).anchor("top_right").open(true)
      .on_open_change((open, cx) => { this.menu = open ? m : null; if (!open) this.removing = null; cx.notify(); })
      .trigger(button).content(content);
  }

  // A machine's heading, as a field while it is renamed, then a line for its state or what its last action said.
  heading(t, mc, now) {
    const m = mc.name, n = this.mid(m), off = mc.state === "unreachable";
    const first = !m;
    const head = h_flex().id(`machine-${m ? n : "local"}`).h(first ? kit.ROW : kit.ROW + 8).flex_none().mt(first ? 0 : 6).pt(first ? 0 : 8).px(8).gap(8)
      .items_center().when(!first, (el) => el.border_t(1).border_color(t.border))
      .text_size(kit.TYPE.body).font_medium().text_color(off ? t.blocked : t.foreground)
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
        .children([off ? null : this.loadOf(t, m)].filter(Boolean))
        .when(Boolean(m), (el) => el.child(this.menuOf(t, mc))),
      ...(off ? [this.note(t, `off-${n}`, `Can't reach it${at}. Its terminals keep running there.`)] : []),
      ...(m && this.said[m] ? [this.note(t, `said-${n}`, this.said[m])] : [])];
  }

  // What hover shows (`field`: hotRow the x, hot + New tab, hovHead Side), applied 80 ms after the pointer settles: each
  // change is a render of the whole rail, and a pointer crossing the rail would otherwise render it once a row.
  settle(field, on, key, cx) {
    this.want ??= {};
    if (on) this.want[field] = key; else if ((this.want[field] ?? this[field]) === key) this.want[field] = null;
    if (this.settling) return;
    this.settling = true;
    cx.timer.after(80, (cx) => {
      this.settling = false;
      let changed = false;
      for (const [f, v] of Object.entries(this.want)) if (this[f] !== v) { this[f] = v; changed = true; }
      this.want = {};
      if (changed) cx.notify();
    });
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

  // Close a plain row's tab or pane (Part II.1), asking first where closeOf says to.
  close(r, name, what) {
    const c = closeOf(r, this.tabsOf.get(r.tab) ?? [], name, what);
    if (!c) return;
    if (c.ask) openOverlay({ mod: "confirm", kind: "dialog", width: 440, height: 200, props: { ...c.ask, command: c.command } });
    else run(c.command.name, c.command.args);
  }

  // The full title, folder, branch and state of a row, resting on it (Part II.2). A tooltip, not a HoverCard: a HoverCard
  // per row built its card every render and kept the rail's spinners off Herdr's cheap path (each turn rebuilt the rail).
  card(r, name, sideText) {
    const p = r.pane && this.paneBy.get(r.pane), cwd = p?.cwd ?? r.t.cwd;
    const state = { working: "working", asks: "asks you", hung: "hung", done: "done", idle: "idle", run: "a program in front", prompt: "at a prompt" }[r.mark];
    const where = [cwd && line(this.home && cwd.startsWith(this.home) ? `~${cwd.slice(this.home.length)}` : cwd, 120), p?.branch && line(p.branch, 60),
      sideText?.startsWith(state) ? sideText : [state, r.mark === "run" || r.mark === "prompt" ? null : sideText].filter(Boolean).join(" ")].filter(Boolean).join(" · ");
    return `${line(r.t.title, 200) || name}\n${where}`;
  }

  // `text`: a swarm row's own what and side (swarmText); a swarm row has no x and no rename (`plain` false); the
  // collapsed rail's card draws rows without a card of their own (`card` false).
  row(t, r, tabName, on, now, { text = null, plain = true, card = true, menu = null } = {}) {
    const shell = !AGENT.has(r.mark);
    let { name, what } = rowText(r.t, r.mark, tabName, this.home);
    let sideText = since(r.mark, this.changed[r.t.address]?.at, now);
    if (text) ({ name, what, side: sideText } = text);
    if (plain && r.tab && this.retitle?.address === r.t.address) return h_flex().id(`retitle-${r.t.address}`).h(ROW).flex_none().mx(4).px(2)
      .items_center().rounded(7).bg(t.raised)
      .on_key_down((e, cx) => { if (e.key === "escape") { this.retitle = null; cx.stop_propagation(); cx.notify(); } })
      .child(div().flex_1().min_w(0).h(22).px(6).flex().items_center().rounded(6).border(1).border_color(t.ring ?? t.accent).bg(t.background)
        .cursor_text().child(Input.new(this.tabInput).h_full().text_size(12.5).text_color(t.foreground)));
    const closes = plain && Boolean(r.pane), x = closes && this.hotRow === r.t.address;
    const e = this.anim && this.ent.enter(`row:${r.t.address}`); // a new row grows in (II.4a)
    // Highlights are the row's own background, hover native: a fading layer per row cost two elements a row and a
    // render of the whole rail per row the pointer crossed.
    const el = h_flex().id(`row-${r.t.address}`).h(e ? 0 : ROW).flex_none().mx(4).px(6).gap(8).items_center().rounded(7)
      .text_size(12.5).cursor_pointer()
      .when(this.anim, (el) => el.overflow_hidden().opacity(e ? 0 : 1).transition("height", 160).transition("opacity", 160))
      .when(on, (el) => el.bg(t.raised))
      .when(!on, (el) => el.hover((s) => s.bg(t.hover)))
      // A double click's second focuses the field; a drop isn't a click.
      .on_click((e, cx) => { if (!(plain && r.tab && e?.click_count >= 2) && Date.now() - (this.droppedAt ?? 0) > 300) this.open(r, cx); })
      // Press: a drag of its tab may start (not a sub-terminal's). Double click: rename its tab in place.
      .when(plain && Boolean(r.tab), (el) => el.on_mouse_down("left", (e, cx) => {
        if (e.click_count === 1 && r.pane && !r.lines.length) this.drag = { space: this.spaceOfTab.get(r.tab), tab: r.tab, y: e.position.y, live: false };
        if (e.click_count !== 2) return;
        this.retitle = { tab: r.tab, address: r.t.address };
        this.tabInput.set_value(this.tabName.get(r.tab) ?? name); cx.notify();
        cx.timer.after(50, () => this.tabInput.focus()); // once the field is drawn
      }))
      // Hover: the x in place of the mark (closes), and a menu's card making way until it leaves.
      .when(closes || Boolean(menu), (el) => el.on_hover((h, cx) => {
        const a = r.t.address;
        if (closes) this.settle("hotRow", h, a, cx);
        if (!h && this.menuFor === a) { this.menuFor = null; cx.notify(); }
      }))
      .when(closes, (el) => el.on_mouse_down("middle", (_e, cx) => { cx.stop_propagation(); this.close(r, name, what); }))
      // Right click: its menu; the row's hover card makes way until the pointer leaves the row.
      .when(Boolean(menu), (el) => el.on_mouse_down("right", (_e, cx) => { cx.stop_propagation(); this.menuFor = r.t.address; cx.notify(); menu(); }))
      .children(this.tree(t, r.lines))
      .child(div().flex_none().max_w(120).truncate().font_medium().text_color(shell ? t.muted : t.foreground)
        .when(shell, (el) => el.font_family(this.mono).text_size(12))
        .child(name))
      .child(div().flex_1().min_w(0).truncate().text_size(11.5).text_color(t.dim).child(what))
      .when(Boolean(sideText), (el) => el.child(div().flex_none().text_size(11.5).text_color(r.mark === "asks" || r.mark === "hung" ? t.blocked : t.dim).child(sideText)))
      // On hover the x takes the mark's place, so the row keeps its width.
      .child(x ? h_flex().id(`close-${r.t.address}`).size(16).mx(-3.5).flex_none().items_center().justify_center().rounded(5)
        .text_size(13).text_color(t.dim).hover((s) => s.bg(t.input).text_color(t.foreground))
        .on_mouse_down("left", (_e, cx) => cx.stop_propagation())
        .on_click((_e, cx) => { cx.stop_propagation(); this.close(r, name, what); }).child("×") : this.markOf(t, r.t.address, r.mark, now));
    if (x && this.anim) this.ent.enter(`mk:${r.t.address}:${r.mark}`); // the x stands in for the mark: it stays seen
    return card && this.menuFor !== r.t.address && !this.drag?.live ? el.tooltip(this.card(r, name, sideText)) : el;
  }

  // A row's mark (II.4a): cross-fades from the one before (two stacked, opacity 200 ms); a new "asks" pulses its first
  // minute. Without animations, the mark alone.
  markOf(t, address, kind, now) {
    if (!this.anim) return mark(t, kind);
    let m = this.marks.get(address);
    if (!m || m.kind !== kind) this.marks.set(address, m = { kind, prev: m?.kind ?? null, at: now });
    // Stacked layers only for the 230 ms a mark fades in or out, then one render more draws it as one box: a row's
    // elements are its cost on every frame.
    const settling = now - m.at < 230, fading = m.prev && m.prev !== kind && settling;
    if (settling) this.fadeAt = Math.min(this.fadeAt ?? Infinity, m.at + 230);
    const asks = kind === "asks" && now - (this.changed[address]?.at ?? 0) < 60000;
    const own = (k, on) => on && asks ? mark(t, k).loop("opacity", { from: 1, to: 0.3, period: 1000 }) : mark(t, k);
    const entering = this.ent.enter(`mk:${address}:${kind}`);
    if (!settling && !entering) return h_flex().size(10).flex_none().items_center().justify_center().child(own(kind, true));
    const one = (k, on) => h_flex().id(`mk-${address}-${k}`).absolute().inset_0().items_center().justify_center()
      .opacity(on && !entering ? 1 : 0).transition("opacity", 200).child(own(k, on));
    return div().relative().size(10).flex_none().when(Boolean(fading), (el) => el.child(one(m.prev, false))).child(one(kind, true));
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
  block(t, s, sw, tabNames, shownTerm, now, fly = false) {
    const sum = sw.sum;
    const tag = sum.swarm ?? "";
    const left = leftOf(sum.counts);
    const n = sum.agents.length;
    const rows = this.capped(t, `b:${s.id}`, sw.block.flatMap((it) => {
      if (it.fold) return [Object.assign(() => h_flex().id(`fold-${s.id}-${it.fold}`).h(ROW).flex_none().mx(4).px(6).gap(8).items_center().rounded(7)
        .text_size(12.5).cursor_pointer().hover((st) => st.bg(t.hover))
        .on_click((_e, cx) => { this.all.add(s.id); cx.notify(); })
        .child(div().flex_1().min_w(0).truncate().font_medium().text_color(t.foreground)
          .child(it.fold === "working" ? `${it.n} ${it.more ? "more " : ""}working` : `${it.n} ${it.more ? "more " : ""}idle`))
        .child(div().flex_none().text_size(11.5).text_color(t.dim).child("show"))
        .child(mark(t, it.fold)), { k: `fold:${it.fold}` })];
      const opened = sw.big && !it.comms && it.r.mark !== "asks" && it.r.mark !== "hung" && this.opened.has(it.r.t.address);
      const text = swarmText(it, this.changed[it.r.t.address]?.at, now, opened);
      const asks = it.r.mark === "asks" && (sum.needs ?? []).some((q) => q.kind === "question" && q.agent === it.a.name);
      const root = asks ? { ...it.r, ask: { swarm: sum.swarm, folder: sum.folder, machine: sum.on ?? null, agent: it.a.name } } : it.r;
      // Right click: its menu (II.1b), rw-bar's popup.
      const menu = () => openOverlay({ mod: "rw-bar", kind: "popup", width: 240,
        props: { agentMenu: { name: it.a.name, swarm: sum.swarm, folder: sum.folder, machine: sum.on ?? null, comms: Boolean(it.comms), task: it.a.task?.id ?? null } } });
      return [root, ...it.kids].map((r, i) => Object.assign(() => this.row(t, r, tabNames.get(r.t.address), r.t.address === shownTerm, now, { text: i ? null : text, plain: false, card: !fly, menu: i ? null : menu }), { k: r.t.address }));
    }), (f) => f(), (f) => f.k ?? null);
    if (this.all.has(s.id) && n > 8) rows.push(h_flex().id(`fewer-${s.id}`).h(ROW).flex_none().mx(4).px(6).items_center().rounded(7)
      .text_size(11.5).text_color(t.dim).cursor_pointer().hover((st) => st.bg(t.hover))
      .on_click((_e, cx) => { this.all.delete(s.id); cx.notify(); }).child("show fewer"));
    // in the shown space, whose own fill already boxes it, the block keeps only its darker fill (round 4, proposal 9)
    return v_flex().id(`swarm-${s.id}`).flex_none().mx(4).mb(6).pt(5).pb(4).rounded(8).border(1).border_color(s.active ? "#00000000" : t.input).bg(t.swarm_block ?? t.chrome)
      .child(h_flex().id(`swarm-head-${s.id}`).mx(4).px(6).pt(3).pb(5).gap(7).items_center().rounded(7).text_size(11.5).text_color(t.muted)
        .when(this.swarmOn === keyOf(sum), (el) => el.bg(t.raised).text_color(t.foreground))
        .cursor_pointer().hover((st) => st.bg(t.hover).text_color(t.foreground)).on_click(() => this.openSwarm(s, sw))
        .on_hover((h, cx) => this.settle("hovHead", h, s.id, cx))
        .child(svg("mods/rw-rail/diamond.svg").size(8).flex_none().text_color(t.muted))
        .child(div().flex_1().min_w(0).truncate().child(`Swarm${tag ? ` ${tag}` : ""} · ${n} ${n === 1 ? "agent" : "agents"} · ${left} left`))
        .when(this.hovHead === s.id, (el) => el.child(h_flex().id(`swarm-side-${s.id}`).flex_none().h(18).px(6).gap(4).items_center().rounded(5)
          .border(1).border_color(t.border).text_color(t.foreground).hover((st) => st.bg(t.selected))
          .on_click((_e, cx) => { cx.stop_propagation(); this.openSide(s); }).child(svg("mods/rw-rail/side.svg").size(11)).child("Side"))))
      .children(rows);
  }

  // Talk (sw-global §5, in place of Open space): the communicator's terminal, focused where a pane shows it, else peeked.
  talk(j) {
    const addr = j.comms_hc ? addrOf(j.comms_hc, j.on ?? null) : null;
    if (!addr) return;
    if (viewShown(layout())) showAll(run, false);
    const p = panes().find((x) => x.terminal === addr);
    if (p) run("pane.focus", { pane: p.pane }); else run("terminal.peek", { terminal: addr });
  }

  // A rail label: "Swarms 2", "Spaces not in a swarm".
  label(t, id, left, right) {
    return h_flex().id(id).flex_none().px(8).pt(6).pb(2).justify_between().text_size(kit.TYPE.meta).text_color(t.dim)
      .child(div().child(left)).child(div().child(right));
  }

  // Rail B's swarm (U-RailB): a header (fold, its tag and name, agents and working, then what asks you or Talk), its repos
  // as outlined tags, then a kit agent row per agent at rail density: the communicator first, then by name; past SHOWN
  // rows, those that don't ask you or hang fold into "N more, M working". Folded, the header keeps the working count
  // and what asks you. `sw`: swarmOf of every row on its machine, with every agent.
  swarmBlock(t, j, sw, tabNames, shownTerm, now) {
    const k = keyOf(j), fk = `sw:${k}`, folded = this.folded.has(fk), id = this.mid(k);
    const items = sw.block.filter((it) => it.r);
    const working = items.filter((it) => it.r.mark === "working").length;
    const asks = (j.needs ?? []).length;
    const on = this.swarmOn === k;
    // select-sync with the swarm view: while it shows, a row's click picks the agent (its tasks light there), a second
    // click on the picked one opens its terminal; a task picked there marks its holder here
    const sel = shared(SELECT), viewOn = swarmShown(layout());
    const many = (j.repos ?? []).length > 1;
    const stop = (_e, cx) => cx.stop_propagation();
    const meta = items.length === 1 && items[0].comms ? "communicator only" : `${items.length} ${items.length === 1 ? "agent" : "agents"}, ${working} working`;
    const right = [];
    if (folded && working) right.push(h_flex().flex_none().gap(4).items_center().text_size(kit.TYPE.meta).text_color(t.dim)
      .child(kit.agentGlyph(t, "working", 8)).child(String(working)));
    if (asks) right.push(div().flex_none().text_size(kit.TYPE.meta).text_color(kit.colors(t).asks).child(`${asks} ${asks === 1 ? "asks" : "ask"}`));
    // the header opens the swarm view: its buttons keep their press and click to themselves
    const own = (el) => el.on_mouse_down("left", stop);
    if (!asks && !folded && j.comms_hc) right.push(own(kit.button(t, `sw-talk-${id}`, "Talk", (cx) => { cx.stop_propagation(); this.talk(j); }, { kind: "ghost", small: true })));
    if (this.hovHead === k && this.homes?.get(k)) right.push(own(kit.button(t, `sw-side-${id}`, "Side", (cx) => { cx.stop_propagation(); this.openSide(this.homes.get(k)); }, { kind: "ghost", small: true })));
    const head = h_flex().id(`sw-head-${id}`).h(kit.ROW_C).flex_none().px(8).gap(6).items_center().rounded(kit.R.ctl).cursor_pointer()
      .when(on, (el) => el.bg(t.selected)).when(!on, (el) => el.hover((st) => st.bg(t.hover)))
      .on_click(() => showSwarm(run, setShared, { swarm: j.swarm, folder: j.folder, machine: j.on ?? null, section: "overview" }))
      .on_hover((h, cx) => this.settle("hovHead", h, k, cx))
      .child(h_flex().id(`sw-fold-${id}`).size(16).flex_none().items_center().justify_center().rounded(4).text_color(t.dim)
        .hover((st) => st.text_color(t.foreground)).on_mouse_down("left", stop)
        .on_click((_e, cx) => { cx.stop_propagation(); this.fold(fk, cx); })
        .child(svg(`mods/workspace-chrome/chevron-${folded ? "right" : "down"}.svg`).size(12)))
      .child(kit.swarmTag(t, j.swarm))
      .child(div().flex_none().max_w(90).truncate().font_medium().text_color(t.foreground).child(j.swarm))
      .child(div().flex_1().min_w(0).truncate().text_size(kit.TYPE.meta).text_color(t.dim).child(meta))
      .children(right);
    const out = v_flex().id(`sw-${id}`).flex_none().gap(0).child(head);
    if (folded) return out;
    // Its repos: each tag says, resting on it, its base, CI, locks and the other swarms on it.
    const info = new Map((j.repoInfo ?? []).map((r) => [r.path, r]));
    const tip = (p) => {
      const r = info.get(p), c = ciWord(r?.ci ?? null);
      return [p, [r?.base && `base ${r.base}`, c && `CI ${c}`, r?.locks ? `${r.locks} ${r.locks === 1 ? "lock" : "locks"}` : null].filter(Boolean).join(", "),
        r?.swarms?.length ? `also ${r.swarms.join(", ")}` : null].filter(Boolean).join("\n");
    };
    const red = (p) => ciWord(info.get(p)?.ci ?? null) === "red";
    if ((j.repos ?? []).length) out.child(h_flex().flex_none().flex_wrap().gap(4).pl(26).pr(8).pt(2).pb(4)
      .children(j.repos.map((p, i) => h_flex().id(`sw-repo-${id}-${i}`).flex_none().gap(3).items_center().tooltip(tip(p))
        .child(kit.repoTag(t, p, repoName(p).slice(0, 6)))
        .when(red(p), (el) => el.child(div().size(6).rounded(3).bg(kit.colors(t).asks))))));
    // The rows: kept ones always (communicator, asks, hung, opened by you), then the rest in order up to SHOWN.
    const all = this.all.has(fk);
    const kept = (it) => it.comms || it.r.mark === "asks" || it.r.mark === "hung";
    let room = Math.max(0, SHOWN - items.filter(kept).length);
    const shown = all || items.length <= SHOWN + 1 ? items : items.filter((it) => kept(it) || room-- > 0);
    const rest = items.filter((it) => !shown.includes(it));
    for (const it of shown) {
      const st = statusOf(it), opened = this.opened.has(it.r.t.address) && !kept(it);
      const text = swarmText(it, this.changed[it.r.t.address]?.at, now, opened);
      const side = st === "landing" ? "landing" : text.side;
      const ask = it.r.mark === "asks" && (j.needs ?? []).some((q) => q.kind === "question" && q.agent === it.a.name);
      const root = ask ? { ...it.r, ask: { swarm: j.swarm, folder: j.folder, machine: j.on ?? null, agent: it.a.name } } : it.r;
      const sub = it.comms ? "communicator" : it.a.task ? `#${it.a.task.id} ${it.a.task.title ?? ""}`.trim() : it.a.stay ? line(it.a.stay, 80) : "";
      const tags = many ? (it.a.repos ?? []).map((p) => kit.repoTag(t, p, repoName(p).slice(0, 6))) : [];
      const sideEl = side ? div().flex_none().text_size(kit.TYPE.meta)
        .text_color(st === "asks" || st === "hung" ? kit.colors(t).asks : st === "landing" ? kit.colors(t).landing : t.dim).child(side) : null;
      const menu = () => openOverlay({ mod: "rw-bar", kind: "popup", width: 240,
        props: { agentMenu: { name: it.a.name, swarm: j.swarm, folder: j.folder, machine: j.on ?? null, comms: Boolean(it.comms), task: it.a.task?.id ?? null } } });
      const picked = viewOn && selectedAgent(sel, j.swarm, it.a.name);
      const row = kit.agentRow(t, this.motion, { name: it.a.name, status: st, swarm: j.swarm }, {
        onClick: (cx) => {
          if (Date.now() - (this.droppedAt ?? 0) <= 300) return;
          if (viewOn && !picked) return setShared(SELECT, { from: "agent", agent: it.a.name, swarm: j.swarm, task: null });
          this.open(root, cx);
        },
        sel: shownTerm === it.r.t.address || picked ? true : null, sub, compact: true, right: [...tags, sideEl].filter(Boolean) })
        .on_mouse_down("right", (_e, cx) => { cx.stop_propagation(); menu(); })
        .tooltip(this.card(it.r, it.a.name, side));
      out.child(kit.arrive(row, this.motion, `ag:${k}:${it.a.name}`));
      // its sub-terminals (a sub-agent, a shell it started) on their tree lines under it
      if (it.kids.length) out.child(v_flex().flex_none().pl(20)
        .children(it.kids.map((r) => this.row(t, r, tabNames.get(r.t.address), r.t.address === shownTerm, now, { plain: false }))));
    }
    if (rest.length) {
      const w = rest.filter((it) => it.r.mark === "working").length;
      out.child(div().id(`sw-more-${id}`).flex_none().pl(44).pr(8).py(4).rounded(kit.R.ctl).text_size(kit.TYPE.meta).text_color(t.dim)
        .cursor_pointer().hover((st) => st.bg(t.hover).text_color(t.foreground))
        .on_click((_e, cx) => { this.all.add(fk); cx.notify(); })
        .child(`${rest.length} more${w ? `, ${w} working` : ""}`));
    } else if (all && items.length > SHOWN + 1) out.child(div().id(`sw-fewer-${id}`).flex_none().pl(44).pr(8).py(4).rounded(kit.R.ctl)
      .text_size(kit.TYPE.meta).text_color(t.dim).cursor_pointer().hover((st) => st.bg(t.hover).text_color(t.foreground))
      .on_click((_e, cx) => { this.all.delete(fk); cx.notify(); }).child("show fewer"));
    return out;
  }

  // The shipped new-menu (a terminal or an agent) in space `s`: it opens its tab in the shown space.
  newTab(s) {
    if (viewShown(layout())) showAll(run, false);
    if (!s.active) run("space.select", { id: s.id });
    openOverlay({ mod: "new-menu", kind: "popup", width: 250, height: 512 });
  }

  // Where a live drag would drop: { tab, over, after } with the line after `over` when the tab moves down (as the shipped
  // spaces mod draws it), or null over its own tab or another space.
  target() {
    const d = this.drag, o = this.overTab;
    if (!d?.live) return null;
    if (!o || o.space !== d.space || o.tab === d.tab) return { tab: d.tab, over: null, after: false };
    const at = (id) => (this.tabsOf.get(d.tab) ?? []).find((x) => x.id === id)?.index ?? 0;
    return { tab: d.tab, over: o.tab, after: at(d.tab) < at(o.tab) };
  }

  // Drop the dragged tab where the line shows (tab.move), or cancel; the keyboard goes back to the pane it was on.
  endDrag(cx, drop) {
    const d = this.drag, to = this.target();
    this.drag = null;
    if (!d?.live) return;
    this.droppedAt = Date.now();
    const index = drop && to.over && dropAt(this.tabsOf.get(d.tab) ?? [], d.tab, to.over, to.after);
    if (index) run("tab.move", { id: d.tab, index });
    if (d.pane) run("pane.focus", { pane: d.pane });
    cx.notify();
  }

  // A tab's rows: a split tab's joined by a bracket, with the tab's name over it when it was named. A tab of the rail's
  // own rows (not a swarm's) is a drag target: the line shows before or after it, never inside a bracket.
  tabOf(t, s, g, draw) {
    if (!g.tab) return g.rows.map(draw);
    const d = this.drag?.live && this.drag.space === s.id ? this.target() : null, name = g.split && this.tabName.get(g.tab);
    const part = Boolean(d) && this.anim && d.tab !== g.tab;
    return [v_flex().id(`tab-${g.tab}`).relative().flex_none()
      .when(g.split, (el) => el.ml(6).pl(2).border_l(2).border_color(t.input))
      .when(d?.tab === g.tab, (el) => el.rounded(8).bg(t.selected).shadow_lg().ml(g.split ? 20 : 14))
      // Hover still follows the pointer during a press (moves stop reaching rows once the drag is live).
      .on_hover((h, cx) => {
        if (h) this.overTab = { space: s.id, tab: g.tab }; else if (this.overTab?.tab === g.tab) this.overTab = null;
        if (this.drag?.live) cx.notify();
      })
      // II.4d: the rows part where the tab will land (height, 120 ms); the line sits in the gap
      .when(d?.over === g.tab, (el) => el.child(div().absolute().left(4).right(4).h(2).rounded(1).bg(t.working)
        .when(d.after, (l) => l.bottom(part ? 4 : -1)).when(!d.after, (l) => l.top(part ? 4 : -1))))
      .when(part, (el) => el.child(div().id(`gap-a-${g.tab}`).flex_none().h(d.over === g.tab && !d.after ? 10 : 0).transition("height", 120)))
      .when(Boolean(name), (el) => el.child(div().h(18).flex_none().px(8).truncate().text_size(11.5).text_color(t.dim).child(line(name, 80))))
      .children(g.rows.map(draw))
      .when(part, (el) => el.child(div().id(`gap-b-${g.tab}`).flex_none().h(d.over === g.tab && d.after ? 10 : 0).transition("height", 120)))];
  }

  // `fly`: the collapsed rail's hover card, always open and not marked as shown. `sw`: the space's swarm (swarmOf).
  // `hid`: rail B's word for the terminals a swarm above holds ("2 in nx", "8 in swarms"), with the tabs left.
  space(t, s, rows, tabNames, shownTerm, now, fly = false, sw = null, hid = null) {
    const folded = !fly && this.folded.has(s.id);
    const adds = s.active && !fly; // the shown space ends with a New tab row
    const open = !folded && (rows.length > 0 || adds);
    const tabs = hid ? tabGroups(rows).filter((g) => g.tab).length : s.tabs.length;
    const tabWord = hid && !tabs ? hid : `${tabs} ${tabs === 1 ? "tab" : "tabs"}${hid ? `, ${hid}` : ""}`;
    const stop = (_e, cx) => cx.stop_propagation();
    const draw = (r) => this.row(t, r, tabNames.get(r.t.address), r.t.address === shownTerm, now, { card: !fly });
    const away = this.drag?.live && this.drag.space !== s.id; // no command moves a tab to another space
    return v_flex().id(`${fly ? "fly" : "space"}-${s.id}`).flex_none().rounded(9).when(s.active && !fly, (el) => el.bg(t.selected)).when(open, (el) => el.pb(6))
      .when(away, (el) => el.opacity(0.45))
      .child(h_flex().id(`head-${s.id}`).h(32).pl(4).pr(10).gap(4).items_center().cursor_pointer()
        .when(!s.active || fly, (el) => el.rounded(9).hover((st) => st.bg(t.hover)))
        .when(!fly, (el) => el.on_hover((on, cx) => this.settle("hot", on, s.id, cx)))
        .on_click((_e, cx) => { if (viewShown(layout())) showAll(run, false); else if (s.active && !fly) return this.fold(s.id, cx); run("space.select", { id: s.id }); })
        .child(h_flex().id(`fold-${s.id}`).size(18).flex_none().items_center().justify_center().rounded(5).text_color(t.dim)
          .hover((st) => st.bg(t.hover).text_color(t.foreground))
          .on_mouse_down("left", stop).on_click((_e, cx) => { cx.stop_propagation(); this.fold(s.id, cx); })
          .child(svg(`mods/workspace-chrome/chevron-${open ? "down" : "right"}.svg`).size(12)))
        .child(div().flex_1().min_w(0).truncate().text_size(14).font_bold().text_color(t.foreground).child(line(s.name, 80)))
        .when(folded, (el) => el.child(h_flex().flex_none().gap(8).children(this.counts(t, rows))))
        .when(!folded, (el) => el.child(div().flex_none().text_size(11).text_color(t.dim).child(tabWord)))
        // New tab, on hover (Part II.2)
        .when(!fly && this.hot === s.id, (el) => el.child(h_flex().id(`add-${s.id}`).size(18).flex_none().items_center().justify_center()
          .rounded(5).text_color(t.dim).hover((st) => st.bg(t.input).text_color(t.foreground))
          .on_mouse_down("left", stop).on_click((_e, cx) => { cx.stop_propagation(); this.newTab(s); })
          .child(svg("mods/workspace-chrome/plus.svg").size(12)))))
      // The space's rows hang on a guide line under its chevron.
      .when(open, (el) => el.child(v_flex().ml(12).pl(2).border_l(1).border_color(t.border)
        .when(Boolean(sw), (el) => el.child(this.block(t, s, sw, tabNames, shownTerm, now, fly)))
        .children(this.capped(t, s.id, tabGroups(sw ? sw.rest : rows), (g) => this.tabOf(t, s, g, draw), (g) => g.tab ?? g.rows[0].t.address).flat())
        .when(adds, (el) => el.child(h_flex().id(`new-tab-${s.id}`).h(ROW).flex_none().mx(4).px(6).gap(8).items_center().rounded(7)
          .text_size(12.5).text_color(t.dim).cursor_pointer().hover((st) => st.bg(t.hover).text_color(t.foreground))
          .on_click(() => this.newTab(s))
          .child(svg("mods/workspace-chrome/plus.svg").size(12).flex_none()).child("New tab")))));
  }

  // A list of rows (or a space's tabs): past ROWS, the first ROWS - 1 and a line that shows the rest (`key`: the space's id).
  // With Animations on, a row (or tab) gone since the last render is drawn once more in its place and shrinks out
  // (height and opacity, 160 ms; round 4, proposal 10). `kOf`: an item's key.
  capped(t, key, xs, draw, kOf) {
    if (xs.length > ROWS && !this.more.has(key)) return [...xs.slice(0, ROWS - 1).map(draw), this.moreLine(t, `more-${key}`, `${xs.length - ROWS + 1} more`, key)];
    if (!this.anim || !kOf) return xs.map(draw);
    const ks = xs.map(kOf), was = this.lists.get(key) ?? [], mine = new Map();
    for (const [gk, g] of this.ghosts) if (g.list === key) mine.set(gk.slice(key.length + 1), g);
    const { fresh, order } = leaving(was.map((p) => p.k), ks, mine), now = Date.now();
    for (const [k, g] of fresh) this.ghosts.set(`${key}|${k}`, { ...g, list: key, at: now, x: was.find((p) => p.k === k).x, n: 0 });
    this.lists.set(key, xs.map((x, i) => ({ k: ks[i], x })));
    const byK = new Map(xs.map((x, i) => [ks[i], x]));
    return order.flatMap(({ k, ghost }) => {
      if (!ghost) return [draw(byK.get(k))];
      const g = this.ghosts.get(`${key}|${k}`);
      if (!g || g.n > 0 && now - g.at > 200) { this.ghosts.delete(`${key}|${k}`); return []; }
      const first = g.n++ === 0, h = (g.x.rows?.length ?? 1) * ROW;
      return [div().id(`leave-${key}-${k}`).flex_none().overflow_hidden().h(first ? h : 0).opacity(first ? 1 : 0)
        .transition("height", 160).transition("opacity", 160).child([draw(g.x)].flat()[0])];
    });
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
      .child(div().text_size(kit.TYPE.meta).text_color(n ? t.blocked : t.dim).child(`${sums.length} running${n ? `, ${n} ${n === 1 ? "needs" : "need"} you` : ""}`));
  }

  // Draws, then once more where something just came or a mark still fades (II.4a).
  render(cx) {
    this.anim = animOn(shared("rw.animations"));
    this.motion.begin(this.anim);
    const el = this.draw(cx);
    this.motion.end(cx);
    if (!this.anim) return el;
    for (const a of this.marks.keys()) if (!this.ent.now.has(`row:${a}`)) this.marks.delete(a);
    const now = Date.now();
    for (const [k, g] of this.ghosts) if (now - g.at > 400) this.ghosts.delete(k); // its list wasn't drawn (folded)
    // Once more 20 ms after something came or a row began to leave (its transition's start), and once when a leaving row
    // is gone or a mark has settled: not every 20 ms in between, each a render of the whole rail.
    const gs = [...this.ghosts.values()], soon = this.ent.end() || gs.some((g) => g.n === 1);
    const at = Math.min(soon ? now + 20 : Infinity, ...gs.map((g) => g.at + 210), this.fadeAt ?? Infinity); this.fadeAt = null;
    if (at < Infinity) cx.timer.after(Math.max(20, at - now), (cx) => cx.notify());
    return el;
  }
  draw(cx) {
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
    // The All swarms and swarm views give way to the tabs once another tab is shown (a row, a key, a click elsewhere).
    const lay = layout(), shownAll = allShown(lay), shownView = viewShown(lay), tab = focused()?.tab ?? null;
    if (shownView && this.viewTab !== undefined && tab !== this.viewTab) showAll(run, false);
    this.viewTab = shownView ? (this.viewTab === undefined ? tab : this.viewTab) : undefined;
    const v = swarmShown(lay) ? shared("rw-swarm.view") : null;
    this.swarmOn = v?.swarm ? `${v.machine ?? ""}:${v.swarm}` : null; // the swarm the view shows
    // Every machine's swarms, each with its space; shared ("rw-rail.swarms") for the other mods once they or their
    // spaces change (rw-bar's Needs you, rw-swarms, rw-swarm's side view, rw-pane).
    const read = [...this.sums.values()].flat(), homes = homesOf(read, sp, ps);
    const sums = read.map((j) => ({ ...j, space: homes.get(keyOf(j)) ?? null }));
    const hk = `${this.gen ?? 0}|${JSON.stringify([...homes])}`;
    if (hk !== this.sharedKey) { this.sharedKey = hk; setShared("rw-rail.swarms", sums); }
    this.paneBy = new Map(ps.map((p) => [p.pane, p]));
    this.tabsOf = new Map(sp.flatMap((s) => s.tabs.map((tab) => [tab.id, s.tabs])));
    this.spaceOfTab = new Map(sp.flatMap((s) => s.tabs.map((tab) => [tab.id, s.id])));
    const tabName = this.tabName = new Map(sp.flatMap((s) => s.tabs).filter((tab) => tab.named).map((tab) => [tab.id, tab.name]));
    const tabNames = new Map(ps.filter((p) => p.terminal).map((p) => [p.terminal, tabName.get(p.tab)]));
    if (!this.started) { this.started = true; this.swarms(cx); }
    this.homes = new Map([...homes].map(([k, id]) => [k, sp.find((s) => s.id === id)]).filter(([, s]) => s));
    kit.useMono(this.mono);
    const ids = new Set(sp.map((s) => s.id));
    const ms = machinesOf(sp, machines().map((m) => m.name), this.listed, shared(HIDDEN) ?? []);
    const narrow = (find(layout(), "sidebar")?.size?.px ?? Infinity) < NARROW;
    // A space that can't be drawn is one line at the foot; the others draw.
    const broken = [];
    const swBy = new Map(); // tiles: a space's swarm, as before rail B (in its home space)
    const swOf = new Map(); // rail B: keyOf(swarm) -> swarmOf over every row on its machine
    const hidBy = new Map(); // rail B: space id -> what its swarms hold ("2 in nx", "8 in swarms")
    let rowsBy;
    if (narrow) rowsBy = new Map(sp.map((s) => {
      try {
        const sum = sumFor(sums, s);
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
    else {
      // Rail B: each machine's swarm agents (each a tree of its own) come out of its spaces into the swarms above them.
      rowsBy = new Map();
      for (const mc of ms) {
        const mine = sums.filter((j) => (j.on ?? null) === mc.name);
        const own = new Set(mine.flatMap((j) => [...swarmAddrs(j, mc.name)]));
        const whose = new Map(mine.flatMap((j) => [...swarmAddrs(j, mc.name)].map((a) => [a, j.swarm])));
        const every = [];
        for (const s of mc.spaces) {
          try {
            const rows = rowsOf(s, ps, byAddr, own);
            const left = [], n = new Map();
            // a swarm agent no pane shows is a root in every space: it leaves each, and counts in none
            let held = null, counts = false;
            for (const r of rows) {
              if (!r.lines.length) { held = whose.get(r.t.address) ?? null; counts = Boolean(held) && r.pane != null; }
              if (!held) left.push(r); else if (counts) n.set(held, (n.get(held) ?? 0) + 1);
            }
            every.push(...rows);
            rowsBy.set(s.id, left);
            const total = [...n.values()].reduce((a, b) => a + b, 0);
            if (total) hidBy.set(s.id, n.size === 1 ? `${total} in ${[...n.keys()][0]}` : `${total} in swarms`);
          } catch (e) {
            broken.push(`Couldn't draw ${line(s.name, 40)}: ${line(e?.message ?? e, 120)}`);
            rowsBy.set(s.id, []);
          }
        }
        for (const j of mine) {
          try { swOf.set(keyOf(j), { ...swarmOf(every, j, byAddr, mc.name, this.opened, true), sum: j, tabs: mc.spaces.flatMap((s) => s.tabs) }); }
          catch (e) { broken.push(`Couldn't draw swarm ${line(j.swarm, 40)}: ${line(e?.message ?? e, 120)}`); }
        }
      }
    }
    // A large swarm (slice 9): the tabs of workers you haven't opened are put away, so the bar shows the ones you have.
    const settles = narrow ? [...swBy].map(([id, sw]) => [sw, sp.find((s) => s.id === id).tabs]) : [...swOf.values()].map((sw) => [sw, sw.tabs]);
    for (const [sw, tabs] of settles) {
      const o = settleOf(new Set(sw.put), new Set(sw.hot), ps, tabs);
      for (const tab of due(this.asked, o.settle, now)) run("tab.settle", { id: tab });
      for (const tab of due(this.asked, o.unsettle, now)) run("tab.unsettle", { id: tab });
      for (const a of o.opened) this.remember(a);
    }
    // Folds and "show all" of spaces that are gone (a swarm's, "sw:", stay).
    if (sp.length) {
      const n = this.folded.size;
      for (const set of [this.folded, this.all, this.more]) for (const id of set) if (!ids.has(id.replace(/^b:/, "")) && !id.startsWith("m:") && !id.startsWith("sw:")) set.delete(id);
      if (this.folded.size !== n) localStorage.setItem("folded", JSON.stringify([...this.folded]));
    }
    // An agent alone in its tab: the tab's change time is the app's own, kept while the rail isn't shown.
    const tabOf = new Map(sp.flatMap((s) => s.tabs).map((tab) => [tab.id, tab]));
    const changedAt = new Map(ps.filter((p) => p.terminal && tabOf.get(p.tab)?.panes === 1).map((p) => [p.terminal, tabOf.get(p.tab).changed_at]));
    const swRows = [...swOf.values()].flatMap((sw) => sw.block.filter((it) => it.r).flatMap((it) => [it.r, ...it.kids]));
    this.track([...swRows, ...[...rowsBy.values()].flat()], now, (a) => changedAt.get(a) ?? null, cx);
    setAgentOrder([...swRows, ...[...rowsBy.values()].flat()].filter((r) => AGENT.has(r.mark) && r.pane).map((r) => r.t.address));

    // A heading per machine (rail B: always); spaces() lists this computer's first. Under each, its swarms, then its spaces.
    const many = ms.length > 1;
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
      const none = many && mc.name && !mc.spaces.length && !off ? [h_flex().id(`nospace-${this.mid(mc.name)}`).h(26).flex_none().px(10).gap(6).items_center().text_size(12).text_color(t.dim)
        .child("No spaces open here ·").child(this.act(t, `newspace-${this.mid(mc.name)}`, "New space", () => run("space.new", { machine: mc.name })))] : [];
      const mine = off ? [] : sums.filter((j) => (j.on ?? null) === mc.name && swOf.has(keyOf(j)));
      const n = this.mid(mc.name);
      const swarmsPart = mine.length ? [this.label(t, `rl-sw-${n}`, "Swarms", String(mine.length)),
        ...mine.map((j) => this.swarmBlock(t, j, swOf.get(keyOf(j)), tabNames, shownTerm, now))] : [];
      const spacesPart = shown.length ? [...(mine.length ? [this.label(t, `rl-sp-${n}`, "Spaces", "not in a swarm")] : []),
        ...shown.map((s) => off ? dim(this.space(t, s, [], tabNames, shownTerm, now))
          : this.space(t, s, rowsBy.get(s.id), tabNames, shownTerm, now, false, null, hidBy.get(s.id) ?? null))] : [];
      return [...this.heading(t, mc, now), ...none, ...swarmsPart, ...spacesPart, ...more];
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
    return v_flex().id("rail").size_full().min_h(0).bg(t.chrome).text_size(13).track_focus(this.keys)
      // A release drops where the line shows; one outside the rail is seen at the next press, which cancels.
      .on_mouse_up("left", (_e, cx) => { if (this.drag) this.endDrag(cx, true); })
      .on_mouse_down_out((_e, cx) => { if (this.drag) this.endDrag(cx, false); })
      .on_key_down((e, cx) => { if (e.key === "escape" && this.drag) { cx.stop_propagation(); this.endDrag(cx, false); } })
      .on_mouse_move((e, cx) => {
        const dr = this.drag;
        if (dr && !dr.live && Math.abs(e.position.y - dr.y) >= 4) { dr.live = true; dr.pane = focused()?.pane ?? null; this.keys.focus(); cx.notify(); }
      })
      .child(h_flex().h(28).flex_none().pl(20).pr(14).pt(6).items_center().justify_end()
        .child(this.button(t, "rail-collapse", "chevron-left", () => this.toggle(false))))
      .when(sums.length > 1 || shownAll, (el) => el.child(this.allRow(t, sums, shownAll)))
      .child(v_flex().id("rail-list").flex_1().min_h(0).px(10).pt(4).pb(12).gap(2).overflow_y_scrollbar().children(items))
      .children([this.trouble(t, [...broken, ...this.failed.values()])].filter(Boolean));
  }
}
