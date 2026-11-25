// The rework's rail, fixed places (design E): every machine on one screen, under its heading its swarms, then its
// spaces with whatever terminals no swarm holds, each a lane: a heading, then one row per terminal in tab order (icon
// for its kind, a swarm agent's or named terminal's name, title or task, time, mark). A row never moves: its mark and
// time change in place, a stale agent dims, and rows come and go only as terminals open and close. A question is its
// row's own text; resting on the row opens its options over the rows below. As before (swarm/herdr/UI-SPEC.md, slice 1
// and Part II.2): sub-terminals under their parent on a thin line, a split tab's rows in an outline. Click a row to
// focus its terminal; click a space to show it; the shown space's name is bright, the others' softer; nothing folds. Each machine's swarms
// come from one `swarm state --json --view swarms` (sw-global §5); a swarm's heading has its tag, its workers' count
// and Talk (its communicator, lit while shown), and opens the swarm view (Part II.3), its Side button on hover the side
// view (II.7). Each machine's heading (slice 10) has a menu on its name (rename in place, hide, update,
// log in again, remove) and its state from `hc machine ls --json`: an unreachable machine's spaces dim with Retry;
// hidden machines leave the rail (Settings shows them again). Once more than one swarm runs, an All swarms row heads the rail
// (slice 13); it shows rw-swarms in place of the tabs.
// A hung swarm agent is a row in the bar's Needs you (round 4, proposal 1), not a card here.

import { View, div, svg, image } from "gpui-kit";
import { v_flex, h_flex, HoverCard, Popover, InputState, Input } from "gpui-base";
import { spaces, panes, terminals, agents, focused, machines, run, theme, settings, setAgentOrder, shared, setShared, home, exec, hc, layout, appHome, openOverlay, watchFolder } from "herdr";
import { AGENT, abbrev, allShown, viewShown, swarmShown, showSwarm, showSide, leaving, asksIn, dur, line, looked, machinesOf, openAsk, pollNext, due, prune, rollOf, rowText, rowsOf, settleOf, showAll, stamp, sumFor, homesOf,
  swarmAddrs, swarmOf, swarmsOf, swarmText, tabGroups, closeOf, dropAt, animOn, Entering, addrOf, ciWord, repoName, SELECT, selectedAgent,
  kindOf, ageOf, boxFor, promptButtons, answerBox, answerArgs } from "./tree.js";
import { mark, look } from "./marks.js";
import * as kit from "./kit.js";

const ROW = 25; // fixed, so the tree lines of stacked rows meet
const DAY = 86400000; // an agent idle this long is stale: it dims
const ICON = { agent: "mods/rw-rail/agent.svg", shell: "mods/workspace-chrome/terminal.svg", comms: "mods/rw-rail/comms.svg" };
// Glass (design E), on the opaque ground: a theme colour at alpha `x`, and a rounded box's 1 px top edge of light, a top
// border so it follows the corners.
const alpha = (c, x) => `${String(c).slice(0, 7)}${Math.round(x * 255).toString(16).padStart(2, "0")}`;
const lit = (el, t) => el.border_t(1).border_color(alpha(t.foreground, 0.26));
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
// A swarm row's kit status: asks, hung, working and gone from its mark, landing from its task, else idle.
const statusOf = (it) => (["asks", "hung", "working", "gone"].includes(it.r.mark) ? it.r.mark : it.a.task?.state === "in_review" ? "landing" : "idle");

export default class Rail extends View {
  init(_props, cx) {
    localStorage.removeItem("folded"); // the folds of the rails before design E, where nothing folds
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
    this.boxes = new Map(); this.sent = new Map(); // a question's prompt box (boxFor); "<address>:<task>" -> how its answer went
    this.replying = null; // { a, r, box, b }: the question whose answer field is in use
    this.reply = InputState.new({});
    this.reply.on("submit", (_e, cx) => this.sendReply(cx));
    this.said = {}; // machine -> what is under way there, or what its last action failed with
    this.menu = null; // the machine whose menu is open
    this.removing = null; // the machine whose menu asks to confirm its removal
    this.renaming = null; // the machine whose heading is a field
    this.name = InputState.new({});
    this.name.on("submit", (_e, cx) => this.rename(cx));
    this.name.on("blur", (_e, cx) => { this.renaming = null; cx.notify(); }); // a rename leaves its field unsaved when it loses focus
    this.drag = null; // { space, tab, y, live, pane }: a row pressed, dragged once it moves 4 px (Part II.2)
    this.overTab = null; // { space, tab }: the tab under the pointer
    this.keys = cx.focus_handle(); // holds the keyboard while a drag is live, for Escape
    this.retitle = null; // { tab }: the split tab renamed in place (Part II.2)
    this.tabInput = InputState.new({});
    this.tabInput.on("submit", (_e, cx) => {
      if (this.retitle) run("tab.rename", { id: this.retitle.tab, name: this.tabInput.value().trim() }); // empty: its number again
      this.retitle = null; cx.notify();
    });
    this.tabInput.on("blur", (_e, cx) => { this.retitle = null; cx.notify(); });
    this.spaceMenu = null; // the space whose menu is open
    this.ctx = null; // { key, x, y, step }: the right-click menu open, where the click was in its element
    this.spawnName = InputState.new({ placeholder: "name" });
    this.spawnText = InputState.new({ placeholder: "what to work on (optional)" });
    for (const i of [this.spawnName, this.spawnText]) i.on("submit", (_e, cx) => this.spawn(cx));
    this.respace = null; // the space whose name is a field
    this.spaceInput = InputState.new({});
    this.spaceInput.on("submit", (_e, cx) => {
      if (this.respace) run("space.rename", { id: this.respace, name: this.spaceInput.value().trim() }); // empty: its folder's name again
      this.respace = null; cx.notify();
    });
    this.spaceInput.on("blur", (_e, cx) => { this.respace = null; cx.notify(); });
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

  // A glass capsule (design E): a machine's name, Talk.
  capsule(t, el) {
    return lit(el.h(22).px(10).gap(5).flex_none().items_center().rounded(11).bg(alpha(t.foreground, 0.14)), t);
  }

  // A machine's menu on its name's capsule, and in its place the question before removing it.
  menuOf(t, mc, name) {
    const m = mc.name, n = this.mid(m), shown = line(m, 60);
    const button = this.capsule(t, h_flex().id(`menu-button-${n}`)).min_w(0).cursor_pointer()
      .when(this.menu === m, (el) => el.bg(alpha(t.foreground, 0.2))).hover((s) => s.bg(alpha(t.foreground, 0.2))).child(name);
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

  // A machine's heading: its name in a capsule (its menu, past this computer), its state or what its last action said,
  // its memory in use, resting on its name how many terminals it has (`count`), this computer's the collapse chevron;
  // as a field while it is renamed.
  heading(t, mc, now, count) {
    const m = mc.name, n = this.mid(m), off = mc.state === "unreachable";
    const head = h_flex().id(`machine-${m ? n : "local"}`).h(28).flex_none().when(Boolean(m), (el) => el.mt(16)).pl(4).pr(2).gap(8)
      .items_center().text_size(12).font_semibold().text_color(off ? t.blocked : t.foreground);
    if (m && this.renaming === m) return [
      head.child(div().id(`rename-${n}`).flex_1().min_w(0).h(26).px(8).flex().items_center().rounded(6).border(1).border_color(t.accent)
        .bg(t.background).font_normal().cursor_text()
        .on_key_down((e, cx) => { if (e.key === "escape") { this.renaming = null; cx.stop_propagation(); cx.notify(); } })
        .child(Input.new(this.name).h_full().text_size(12).text_color(t.foreground))),
      this.note(t, `rename-note-${n}`, "Enter to save · Esc to cancel")];
    const state = m && mc.state && !["connected", "unreachable"].includes(mc.state) ? mc.state.replace(/_/g, " ") : null;
    const at = mc.since && new Date(mc.since).toDateString() === new Date(now).toDateString()
      ? ` since ${new Date(mc.since).toTimeString().slice(0, 5)}` : mc.since ? ` for ${dur(now - mc.since)}` : "";
    const name = div().id(`machine-name-${m ? n : "local"}`).max_w(170).truncate()
      .when(count > 0, (el) => el.tooltip(`${count} ${count === 1 ? "terminal" : "terminals"}`)).child(m ? line(m, 60) : "This computer");
    return [
      head.when(Boolean(m), (el) => el.on_mouse_down("right", (_e, cx) => { cx.stop_propagation(); this.menu = m; this.removing = null; cx.notify(); }))
        .child(m ? this.menuOf(t, mc, name) : this.capsule(t, h_flex()).child(name))
        .when(off, (el) => el.child(mark(t, "hung")).child(this.act(t, `retry-${n}`, "Retry", (_e, cx) => this.refreshMachines(cx))))
        .when(Boolean(state), (el) => el.child(div().flex_none().text_size(11.5).font_normal().text_color(t.dim).child(state)))
        .when(mc.state === "needs_login", (el) => el.child(this.act(t, `login-${n}`, "Log in", (_e, cx) => this.login(m, cx))))
        .child(div().flex_1())
        .children([off ? null : this.loadOf(t, m)].filter(Boolean))
        .when(!m, (el) => el.child(this.button(t, "rail-collapse", "chevron-left", () => this.toggle(false)))),
      ...(off ? [this.note(t, `off-${n}`, `Can't reach it${at}. Its terminals keep running there.`)] : []),
      ...(m && this.said[m] ? [this.note(t, `said-${n}`, this.said[m])] : [])];
  }

  // What hover shows (`field`: hotRow the x, hot + New tab, hovHead Side, askRow and askPop a question's options),
  // applied 80 ms after the pointer settles: each change is a render of the whole rail, and a pointer crossing the rail would otherwise render it once a row.
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
    const state = { working: "working", asks: "asks", hung: "hung", done: "done", idle: "idle", run: "a program in front", prompt: "at a prompt" }[r.mark];
    const where = [cwd && line(this.home && cwd.startsWith(this.home) ? `~${cwd.slice(this.home.length)}` : cwd, 120), p?.branch && line(p.branch, 60),
      sideText?.startsWith(state) ? sideText : [state, r.mark === "run" || r.mark === "prompt" ? null : sideText].filter(Boolean).join(" ")].filter(Boolean).join(" · ");
    return `${line(r.t.title, 200) || name}\n${where}`;
  }

  // A row (design E): its kind's icon (`kind`, kindOf), a swarm agent's or named terminal's name, its title (an agent's
  // what, a shell's program in front or its name), its time and mark. `text`: a swarm row's own name, what and side; a
  // swarm row has no x and no rename (`plain` false); the collapsed rail's card draws rows without a card of their own
  // (`card` false); `onClick` in place of showing its terminal. A question's row says the question, and resting on it
  // opens its options (askCard).
  row(t, r, tabName, on, now, { text = null, plain = true, card = true, menu = null, kind = kindOf(r), onClick = null, task = null } = {}) {
    const shell = kind === "shell", a = r.t.address, c = kit.colors(t), at = this.changed[a]?.at;
    let { name, what } = rowText(r.t, r.mark, tabName, this.home);
    let who = r.t.name && !shell ? name : null, title = shell ? (r.mark === "run" ? what : name) : what || name;
    let sideText = shell ? (r.mark === "run" ? name : "") : ageOf(r.mark, at, now);
    if (text) ({ name: who, what: title, side: sideText } = text);
    const q = r.mark === "asks" ? line(r.need?.question ?? r.t.report?.msg, 300) : "";
    if (q) { title = q; task = null; }
    if (who === title) who = null;
    const stale = r.mark === "idle" && Boolean(at) && now - at >= DAY;
    const closes = plain && Boolean(r.pane), x = closes && this.hotRow === a, pop = Boolean(q) && this.hotAsk === a;
    const e = this.anim && this.ent.enter(`row:${a}`); // a new row grows in (II.4a)
    // Highlights are the row's own background, hover native: a fading layer per row cost two elements a row and a
    // render of the whole rail per row the pointer crossed. The shown row is glass: a fill and a top edge of light (not
    // on a sub-terminal, whose tree lines would shift).
    const el = h_flex().id(`row-${a}`).relative().h(e ? 0 : ROW).flex_none().px(8).gap(7).items_center().rounded(9)
      .text_size(13).cursor_pointer()
      .when(this.anim, (el) => el.overflow_hidden().opacity(e ? 0 : 1).transition("height", 160).transition("opacity", 160))
      .when(on, (el) => (r.lines.length ? el : lit(el, t)).bg(alpha(t.foreground, 0.15)))
      .when(!on && r.mark === "asks", (el) => el.bg(alpha(c.asks, 0.14)))
      .when(!on, (el) => el.hover((s) => s.bg(t.hover)))
      // A double click's second focuses the field; a drop isn't a click.
      .on_click((e, cx) => { if (!(r.split && plain && e?.click_count >= 2) && Date.now() - (this.droppedAt ?? 0) > 300) onClick ? onClick(cx) : this.open(r, cx); })
      // Press: a drag of its tab may start (not a sub-terminal's, nor a pinned row's). Double click in a split tab: rename it.
      .when(plain && Boolean(r.tab), (el) => el.on_mouse_down("left", (e, cx) => {
        if (e.click_count === 1 && r.pane && !r.lines.length && !r.pin) this.drag = { space: this.spaceOfTab.get(r.tab), tab: r.tab, y: e.position.y, live: false };
        if (e.click_count === 2 && r.split) this.startRetitle(r.tab, name, cx);
      }))
      // Hover: the x in place of the mark (closes), a question's options, and a menu's card making way until it leaves.
      .when(closes || Boolean(menu) || Boolean(q), (el) => el.on_hover((h, cx) => {
        if (closes) this.settle("hotRow", h, a, cx);
        if (q) this.settle("askRow", h, a, cx);
        if (!h && this.menuFor === a) { this.menuFor = null; cx.notify(); }
      }))
      .when(closes, (el) => el.on_mouse_down("middle", (_e, cx) => { cx.stop_propagation(); this.close(r, name, what); }))
      // Right click: its menu; the row's hover card makes way until the pointer leaves the row.
      .when(Boolean(menu), (el) => el.on_mouse_down("right", (_e, cx) => { cx.stop_propagation(); this.menuFor = a; cx.notify(); menu(); }))
      .children(this.tree(t, r.lines))
      .child(h_flex().w(14).flex_none().justify_center().child(this.icon(t, kind, r.t.program)))
      .when(Boolean(who), (el) => el.child(div().flex_none().max_w(90).truncate().text_size(11.5).font_semibold()
        .text_color(alpha(t.foreground, 0.78)).child(who)))
      .child(task ? h_flex().flex_1().min_w(0).child(this.taskChip(t, a, task))
        : div().flex_1().min_w(0).truncate().text_color(stale ? alpha(t.foreground, 0.8) : t.foreground).child(title))
      .when(Boolean(sideText), (el) => el.child(div().flex_none().text_size(11.5).text_color(r.mark === "asks" || r.mark === "hung" ? c.asks
        : r.mark === "landing" ? c.landing : alpha(t.foreground, stale ? 0.68 : 0.74)).child(sideText)))
      // On hover the x takes the mark's place, so the row keeps its width.
      .child(x ? h_flex().id(`close-${a}`).size(16).mx(-3.5).flex_none().items_center().justify_center().rounded(5)
        .text_size(13).text_color(t.dim).hover((s) => s.bg(t.input).text_color(t.foreground))
        .on_mouse_down("left", (_e, cx) => cx.stop_propagation())
        .on_click((_e, cx) => { cx.stop_propagation(); this.close(r, name, what); }).child("×") : this.markOf(t, a, r.mark, now, stale))
      // the question's options hang from the row's foot, over the rows below
      .when(pop, (el) => el.child(div().absolute().left(0).bottom(0).child(Popover.new(`ask-${a}`).anchor("top_left").open(true)
        .on_open_change((open, cx) => { if (!open) { this.askRow = this.askPop = this.replying = null; cx.notify(); } })
        .trigger(div().size(0)).content(this.askCard(t, r, who ?? name, q, now)))));
    if (x && this.anim) this.ent.enter(`mk:${a}:${r.mark}`); // the x stands in for the mark: it stays seen
    const tip = () => (task ? `#${task.id} ${line(task.title, 200)}\n` : "") + this.card(r, name, sideText) + (r.pin ? `\nin ${r.pin}` : "");
    // Right click: its menu, a swarm agent's (rw-bar's popup) or the rail's own.
    const k = `row:${a}`, own = card && !menu ? this.ctxMenu(el, t, k, () => this.rowItems(r, name, what, plain)) : el;
    return card && !pop && this.menuFor !== a && this.ctx?.key !== k && !this.drag?.live ? own.tooltip(tip()) : own;
  }

  // A swarm agent's task as a chip (#12): a click opens its page in the swarm view.
  taskChip(t, a, task) {
    return h_flex().id(`task-${a}`).h(18).px(6).flex_none().items_center().rounded(9).bg(alpha(t.foreground, 0.1))
      .text_size(11.5).font_medium().text_color(alpha(t.foreground, 0.85)).cursor_pointer()
      .hover((s) => s.bg(alpha(t.foreground, 0.2)).text_color(t.foreground))
      .on_mouse_down("left", (_e, cx) => cx.stop_propagation())
      .on_click((_e, cx) => { cx.stop_propagation(); task.open(); }).child(`#${task.id}`);
  }

  // A question's options (design H), solid over the rows below: the question in full, the agent's own options where
  // its screen's prompt box parses (II.6c: read again before a key is pressed, else its terminal shows), a swarm
  // question's answer field, and Open.
  askCard(t, r, name, q, now) {
    const c = kit.colors(t), a = r.t.address, at = this.changed[a]?.at, box = this.hotBox;
    const opt = (k, label, main, f) => h_flex().id(`ask-${k}-${a}`).relative().h(22).px(10).flex_none().items_center().rounded(11)
      .text_size(11.5).cursor_pointer().on_click((_e, cx) => { cx.stop_propagation(); f(cx); }).child(label)
      .when(main, (el) => el.bg(c.asks).text_color(c.ink).font_semibold())
      .when(!main, (el) => lit(el.bg(alpha(t.foreground, 0.14)).text_color(t.foreground).font_medium().hover((s) => s.bg(alpha(t.foreground, 0.2))), t));
    const say = (more) => (cx) => { this.replying = { a, r, ...more }; this.reply.set_value(""); cx.notify(); cx.timer.after(50, () => this.reply.focus()); };
    const field = r.need?.task != null || (this.replying?.a === a && this.replying.b);
    const opts = r.need?.task != null ? [] : promptButtons(box).map((b, k) => opt(k, b.label, k === 0 && !b.say,
      b.say ? say({ box, b }) : (cx) => answerBox(this.boxes, hc, a, box, b, null, cx, () => this.open(r))));
    return v_flex().id(`ask-card-${a}`).relative().w(Math.max(200, this.railW - 28)).p(4).rounded(16).bg(t.popover)
      .border(1).border_color(t.border).shadow_lg()
      .on_hover((h, cx) => this.settle("askPop", h, a, cx))
      .child(v_flex().relative().gap(5).px(9).py(6).rounded(13).bg(alpha(c.asks, 0.2)).border(1).border_color(alpha(c.asks, 0.3))
        .child(h_flex().items_start().gap(6).text_size(12.5).line_height(1.36)
          .child(div().flex_none().font_family(this.mono).text_size(11.5).font_semibold().text_color(c.asks).child(name))
          .child(div().flex_1().min_w(0).text_color(t.foreground).child(q)))
        .when(Boolean(field), (el) => el.child(h_flex().gap(5).items_center()
          .child(div().flex_1().min_w(0).h(24).px(8).flex().items_center().rounded(8).border(1).border_color(t.border).bg(t.background)
            .on_mouse_down("left", (_e, cx) => { if (this.replying?.a !== a) { this.replying = { a, r }; cx.notify(); } })
            .child(Input.new(this.reply).h_full().text_size(12.5).text_color(t.foreground)))
          .child(opt("send", "Send", true, (cx) => this.sendReply(cx)))))
        .child(h_flex().gap(5).flex_wrap().items_center().children(opts)
          .child(opt("open", "Open", false, (cx) => { this.askRow = this.askPop = this.replying = null; this.open(r, cx); }))
          .child(div().flex_1())
          .child(div().flex_none().text_size(11.5).text_color(c.asks).child(this.sent.get(`${a}:${r.need?.task}`) ?? (at ? dur(now - at) : "")))));
  }

  // Sends what the answer field holds: a prompt's "say what" after its key (answerBox), or a swarm question's answer
  // (`task unblock`); the card says how it went.
  sendReply(cx) {
    const w = this.replying, text = this.reply.value().trim();
    if (!w?.r || !text) return;
    this.replying = null;
    const r = w.r, a = r.t.address;
    if (w.b) return answerBox(this.boxes, hc, a, w.box, w.b, text, cx, () => this.open(r));
    if (r.need?.task == null || !r.ask) return;
    const k = `${a}:${r.need.task}`;
    this.sent.set(k, "Sending…"); cx.notify();
    cx.spawn(async (cx) => {
      let res = null;
      try { res = await swarm(r.ask.folder, r.ask.machine, answerArgs(r.need.task, text), r.ask.swarm); } catch (e) { res = { code: 1, stderr: String(e?.message ?? e) }; }
      this.sent.set(k, res.code === 0 ? "Sent" : line(res.stderr || res.stdout, 120).replace(/^swarm: /, "") || `swarm exited ${res.code}`);
      cx.notify();
    });
  }

  // A row's icon: an agent's own from the app's program table (Claude Code, pi, Codex...), else its kind's.
  icon(t, kind, p) {
    if (kind !== "agent" || !p?.icon) return svg(ICON[kind]).size(13).text_color(alpha(t.foreground, 0.74));
    return p.tint ? svg(p.icon).size(13).flex_none().text_color(alpha(t.foreground, 0.84)) : image(p.icon).w(13).h(13).flex_none();
  }

  // A row's mark (design E), 9 px: working a turning ring, asks a dot and hung a square in a halo, landing a thick ring, done a
  // light dot, idle a ring (fainter when `stale`), gone a dash; a shell none.
  dot(t, kind, stale = false) {
    const c = kit.colors(t), box = h_flex().size(9).flex_none();
    const halo = (el) => h_flex().size(15).mx(-3).my(-3).flex_none().items_center().justify_center().rounded(8).bg(alpha(c.asks, 0.28)).child(el);
    switch (kind) {
      case "working": return kit.agentGlyph(t, "working", 9);
      case "asks": return halo(box.rounded(5).bg(c.asks));
      case "hung": return halo(box.rounded(2).bg(c.asks));
      case "landing": return box.rounded(5).border(3).border_color(c.landing);
      case "done": return box.rounded(5).bg(alpha(t.foreground, 0.92));
      case "idle": return box.rounded(5).border(1.5).border_color(alpha(t.foreground, stale ? 0.36 : 0.62));
      case "gone": return mark(t, "gone");
    }
    return box;
  }

  // A row's mark (II.4a): cross-fades from the one before (two stacked, opacity 200 ms); a new "asks" pulses its first
  // minute. Without animations, the mark alone.
  markOf(t, address, kind, now, stale = false) {
    const draw = (k) => this.dot(t, k, stale);
    if (!this.anim) return draw(kind);
    let m = this.marks.get(address);
    if (!m || m.kind !== kind) this.marks.set(address, m = { kind, prev: m?.kind ?? null, at: now });
    // Stacked layers only for the 230 ms a mark fades in or out, then one render more draws it as one box: a row's
    // elements are its cost on every frame.
    const settling = now - m.at < 230, fading = m.prev && m.prev !== kind && settling;
    if (settling) this.fadeAt = Math.min(this.fadeAt ?? Infinity, m.at + 230);
    const asks = kind === "asks" && now - (this.changed[address]?.at ?? 0) < 60000;
    const own = (k, on) => on && asks ? draw(k).loop("opacity", { from: 1, to: 0.3, period: 1000 }) : draw(k);
    const entering = this.ent.enter(`mk:${address}:${kind}`);
    if (!settling && !entering) return h_flex().size(10).flex_none().items_center().justify_center().child(own(kind, true));
    const one = (k, on) => h_flex().id(`mk-${address}-${k}`).absolute().inset_0().items_center().justify_center()
      .opacity(on && !entering ? 1 : 0).transition("opacity", 200).child(own(k, on));
    return div().relative().size(10).flex_none().when(Boolean(fading), (el) => el.child(one(m.prev, false))).child(one(kind, true));
  }

  // A swarm's block: a heading (tag, agents, tasks left), its agents' rows, and past 8 agents two counts that show all.
  block(t, s, sw, tabNames, shownTerm, now, fly = false) {
    const sum = sw.sum;
    const tag = sum.swarm ?? "";
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
        .child(div().flex_none().child(`Swarm${tag ? ` ${tag}` : ""}`)).child(div().flex_none().font_family(settings().font_family).text_size(10.5).text_color(t.dim).child(String(n))).child(div().flex_1())
        .child(kit.taskGlyph(t, "ready", 10)).child(div().flex_none().font_family(settings().font_family).text_size(10.5).text_color(t.dim).child(String(sum.counts?.ready ?? 0)))
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

  // A swarm's lane (design E): a heading (its tag and repo, resting on it its repos' base, CI and locks, a red dot when
  // one's CI is red; how many workers; Side on hover; Talk, its communicator, lit while shown and tinted while it asks
  // or hangs), then a row per worker by name, each with its sub-terminals (the communicator's too, without it). The
  // heading opens the swarm view; while that shows, a click picks the agent (its tasks light there), a second click on
  // the picked one opens its terminal, and a task picked there marks its holder here. `sw`: swarmOf of every row on its
  // machine, with every agent.
  swarmLane(t, j, sw, tabNames, shownTerm, now) {
    const k = keyOf(j), id = this.mid(k), c = kit.colors(t);
    const sel = shared(SELECT), viewOn = swarmShown(layout());
    const own = (el) => el.on_mouse_down("left", (_e, cx) => cx.stop_propagation());
    const items = sw.block.filter((it) => it.r), of = new Map(), all = [];
    const comms = items.find((it) => it.comms), workers = items.length - (comms ? 1 : 0);
    for (const it of items) {
      if (it.comms) { all.push(...it.kids.map((r) => ({ ...r, lines: r.lines.slice(1) }))); continue; }
      const need = it.r.mark === "asks" ? (j.needs ?? []).find((q) => q.kind === "question" && q.agent === it.a.name) : null;
      const root = { ...it.r, mark: statusOf(it) === "landing" ? "landing" : it.r.mark,
        ...(need ? { need, ask: { swarm: j.swarm, folder: j.folder, machine: j.on ?? null, agent: it.a.name } } : {}) };
      all.push(root, ...it.kids); of.set(root.t.address, it);
    }
    // an agent's words, menu (rw-bar's popup) and click (select-sync); a sub-terminal's are a plain row's
    const drawRow = (r) => {
      const it = of.get(r.t.address);
      if (!it) return this.row(t, r, tabNames.get(r.t.address), r.t.address === shownTerm, now, { plain: false });
      const side = r.mark === "landing" ? (it.a.task?.pr != null ? `PR ${it.a.task.pr}` : "landing")
        : r.mark === "hung" ? swarmText(it, null, now, false).side : ageOf(r.mark, this.changed[r.t.address]?.at, now);
      const picked = viewOn && selectedAgent(sel, j.swarm, it.a.name);
      return this.row(t, r, tabNames.get(r.t.address), r.t.address === shownTerm || picked, now, { plain: false,
        text: { name: it.a.name, what: it.a.task?.title ?? (it.a.task ? `#${it.a.task.id}` : it.a.stay ? line(it.a.stay, 80) : ""), side },
        task: it.a.task?.id != null ? { id: it.a.task.id, title: it.a.task.title ?? "",
          open: () => showSwarm(run, setShared, { swarm: j.swarm, folder: j.folder, machine: j.on ?? null, section: "overview", page: { task: it.a.task.id } }) } : null,
        menu: () => openOverlay({ mod: "rw-bar", kind: "popup", width: 240,
          props: { agentMenu: { name: it.a.name, swarm: j.swarm, folder: j.folder, machine: j.on ?? null, comms: false, task: it.a.task?.id ?? null } } }),
        onClick: (cx) => {
          if (Date.now() - (this.droppedAt ?? 0) <= 300) return;
          if (viewOn && !picked) return setShared(SELECT, { from: "agent", agent: it.a.name, swarm: j.swarm, task: null });
          this.open(r, cx);
        } });
    };
    const info = new Map((j.repoInfo ?? []).map((r) => [r.path, r]));
    const tip = (j.repos ?? []).map((p) => {
      const r = info.get(p), ci = ciWord(r?.ci ?? null);
      return [p, [r?.base && `base ${r.base}`, ci && `CI ${ci}`, r?.locks ? `${r.locks} ${r.locks === 1 ? "lock" : "locks"}` : null].filter(Boolean).join(", "),
        r?.swarms?.length ? `also ${r.swarms.join(", ")}` : null].filter(Boolean).join("\n");
    }).join("\n\n");
    const red = (j.repos ?? []).some((p) => ciWord(info.get(p)?.ci ?? null) === "red");
    const working = items.filter((it) => !it.comms && it.r.mark === "working").length;
    const talkOn = Boolean(comms) && comms.r.t.address === shownTerm, talkAsks = comms && (comms.r.mark === "asks" || comms.r.mark === "hung");
    const head = h_flex().id(`sw-head-${id}`).h(24).mb(3).flex_none().pl(8).pr(2).gap(6).items_center().rounded(9).cursor_pointer()
      .when(this.swarmOn === k, (el) => el.bg(alpha(t.foreground, 0.08)))
      .when(this.swarmOn !== k, (el) => el.hover((st) => st.bg(t.hover)))
      .on_click(() => showSwarm(run, setShared, { swarm: j.swarm, folder: j.folder, machine: j.on ?? null, section: "overview" }))
      .on_hover((h, cx) => this.settle("hovHead", h, k, cx))
      .child(kit.swarmTag(t, j.swarm))
      .child(div().id(`sw-name-${id}`).flex_shrink_1().min_w(0).max_w(150).truncate().font_semibold().text_color(t.foreground)
        .when(Boolean(tip), (el) => el.tooltip(tip)).child(line(repoName(j.folder) || j.swarm, 80)))
      .when(red, (el) => el.child(div().size(6).flex_none().rounded(3).bg(c.asks)))
      .child(div().id(`sw-n-${id}`).flex_none().text_size(11.5).text_color(alpha(t.foreground, 0.74))
        .tooltip(`${workers} ${workers === 1 ? "worker" : "workers"}, ${working} working, ${j.ready ?? 0} ready`)
        .child(workers ? String(workers) : ""))
      .child(div().flex_1())
      .when(this.hovHead === k && Boolean(this.homes?.get(k)), (el) => el.child(own(kit.button(t, `sw-side-${id}`, "Side",
        (cx) => { cx.stop_propagation(); this.openSide(this.homes.get(k)); }, { kind: "ghost", small: true }))))
      .when(Boolean(j.comms_hc), (el) => el.child(own(h_flex().id(`sw-talk-${id}`).h(20).px(8).gap(4).flex_none().items_center().rounded(10)
        .border(1).border_color(alpha(t.foreground, 0.16)).cursor_pointer()
        .when(talkOn, (el) => lit(el, t).bg(alpha(t.foreground, 0.2))).when(Boolean(talkAsks), (el) => el.bg(alpha(c.asks, 0.3)).border_color(alpha(c.asks, 0.5)))
        .hover((st) => st.bg(alpha(t.foreground, 0.12))).text_size(11.5).font_medium().text_color(talkOn || talkAsks ? t.foreground : t.muted)
        .when(Boolean(talkAsks), (el) => el.tooltip(comms.r.mark === "hung" ? "The communicator is hung" : line(comms.r.t.report?.msg, 300) || "The communicator asks you"))
        .on_click((_e, cx) => { cx.stop_propagation(); this.talk(j); })
        .on_mouse_down("right", (_e, cx) => { cx.stop_propagation(); openOverlay({ mod: "rw-bar", kind: "popup", width: 240,
          props: { agentMenu: { name: comms.a.name, swarm: j.swarm, folder: j.folder, machine: j.on ?? null, comms: true, task: null } } }); })
        .child(svg(ICON.comms).size(11)).child("Talk"))));
    return v_flex().id(`sw-${id}`).flex_none().mt(9).child(this.ctxMenu(head.relative(), t, `sw:${k}`, () => this.swarmItems(j, k)))
      .child(v_flex().flex_none().pl(6).children(this.capped(t, `sw:${k}`, all, drawRow, (r) => r.t.address)));
  }

  // A space's menu, on its ... button and on a right click of its heading: rename, new tab, close (Herdr asks first).
  spaceMenuOf(t, s) {
    const button = h_flex().id(`more-${s.id}`).size(18).flex_none().items_center().justify_center().rounded(6).text_color(t.dim)
      .when(this.spaceMenu === s.id, (el) => el.bg(alpha(t.foreground, 0.13)).text_color(t.foreground))
      .hover((st) => st.bg(alpha(t.foreground, 0.13)).text_color(t.foreground))
      .on_mouse_down("left", (_e, cx) => cx.stop_propagation())
      .on_click((_e, cx) => { cx.stop_propagation(); this.spaceMenu = s.id; cx.notify(); })
      .child(svg("mods/rw-rail/more.svg").size(12));
    // A Popover only while open: one in the view keeps every spinner in the rail rebuilding the whole rail as it turns.
    if (this.spaceMenu !== s.id) return button;
    return Popover.new(`space-menu-${s.id}`).anchor("top_right").open(true)
      .on_open_change((open, cx) => { this.spaceMenu = open ? s.id : null; cx.notify(); })
      .trigger(button).content(this.menuCard(t, `space:${s.id}`, this.spaceItems(s), () => { this.spaceMenu = null; }));
  }

  // A space's menu items; `named`: with Rename (a tile has no field for it).
  spaceItems(s, named = true) {
    const same = this.sp.filter((x) => (x.machine ?? null) === (s.machine ?? null)), i = same.findIndex((x) => x.id === s.id);
    const to = (x) => () => run("space.move", { id: s.id, index: this.sp.findIndex((y) => y.id === x.id) + 1 });
    return [
      named && { id: "rename", text: "Rename", act: (cx) => {
        this.respace = s.id; this.spaceInput.set_value(s.name ?? "");
        cx.timer.after(50, () => this.spaceInput.focus()); // once the field is drawn
      } },
      { id: "new", text: "New tab", act: () => this.newTab(s) },
      i > 0 && { id: "up", text: "Move up", act: to(same[i - 1]) },
      i >= 0 && i < same.length - 1 && { id: "down", text: "Move down", act: to(same[i + 1]) },
      "-",
      { id: "close", text: "Close space…", act: () => run("space.close", { id: s.id }), red: true }];
  }

  // The rail's menus: `items` { id, text, act(cx), red } (false: left out) or "-" for a line between groups; a click
  // runs one and closes the menu (`close`).
  menuCard(t, key, items, close) {
    const n = this.mid(key), xs = items.filter(Boolean).filter((it, i, a) => it !== "-" || (i > 0 && i < a.length - 1 && a[i - 1] !== "-"));
    return v_flex().w(200).p(5).rounded(10).bg(t.popover).border(1).border_color(t.border).shadow_lg()
      .children(xs.map((it) => it === "-" ? div().h(1).mx(4).my(3).bg(t.border)
        : div().id(`mi-${n}-${it.id}`).px(10).py(6).rounded(6).text_size(12.5).font_normal().text_color(it.red ? t.blocked : t.foreground)
          .cursor_pointer().hover((st) => st.bg(t.hover)).on_mouse_down("left", (_e, cx) => cx.stop_propagation())
          .on_click((_e, cx) => { cx.stop_propagation(); close(); it.act(cx); cx.notify(); }).child(it.text)));
  }

  // A right click on `el` (relative) opens menu `key` where it was. A Popover only while open, as above.
  ctxMenu(el, t, key, items) {
    el = el.on_mouse_down("right", (e, cx) => {
      cx.stop_propagation(); this.ctx = { key, x: e.local_position?.x ?? 8, y: e.local_position?.y ?? 0 }; cx.notify();
    });
    const c = this.ctx;
    if (c?.key !== key) return el;
    const close = () => { if (this.ctx === c) this.ctx = null; };
    return el.child(div().absolute().left(c.x).top(c.y).child(Popover.new(`ctx-${this.mid(key)}`).anchor("top_left").open(true)
      .on_open_change((open, cx) => { if (!open && this.ctx === c) { this.ctx = null; cx.notify(); } })
      .trigger(div().size(0)).content(c.step === "spawn" ? this.spawnCard(t, c) : this.menuCard(t, key, items(), close))));
  }

  // A row's menu (agents, shells, sub-terminals). `plain`: a row of a space's (it closes, and renames a split tab).
  rowItems(r, name, what, plain) {
    const a = r.t.address, cwd = (r.pane && this.paneBy.get(r.pane)?.cwd) || r.t.cwd, pinned = this.pinned.has(a);
    const tab = r.split && plain && this.tabsOf.get(r.tab)?.find((x) => x.id === r.tab);
    const ask = (title, detail, name, args) => openOverlay({ mod: "confirm", kind: "dialog", width: 440, height: 200, props: { title, detail, command: { name, args } } });
    return [
      { id: "show", text: r.pane ? "Show" : "Peek", act: (cx) => this.open(r, cx) },
      tab && { id: "rename", text: "Rename tab", act: (cx) => this.startRetitle(r.tab, name, cx) },
      r.mark === "run" && { id: "int", text: "Interrupt (Ctrl-C)", act: () => hc(["interrupt", a]).catch(() => {}) },
      this.agentAddrs.has(a) && { id: "pin", text: pinned ? "Unpin" : "Pin to top", act: () => run("terminal.pin", { terminal: a, pinned: !pinned }) },
      !r.pane && { id: "keep", text: "Give it a tab", act: () => run("terminal.keep", { terminal: a, place: "tab" }) },
      r.pane && r.t.parent && { id: "park", text: "Back under its parent", act: () => run("terminal.park", { terminal: a }) },
      "-",
      cwd && { id: "copy", text: "Copy folder path", act: (cx) => cx.write_to_clipboard(cwd) },
      cwd && !a.includes("/") && { id: "reveal", text: "Reveal in Finder", act: () => exec("open", ["-R", cwd]).catch(() => {}) },
      "-",
      plain && r.pane && { id: "close", text: "Close", act: () => this.close(r, name, what), red: true },
      tab && (tab.panes ?? 1) > 1 && this.closeTabItem({ tab: r.tab, rows: [] }, tab),
      !r.pane && { id: "end", text: "End…", red: true,
        act: () => ask(`End ${line(name, 60)}?`, "Ends its terminal and any sub-agents under it.", "terminal.kill", { terminal: a }) }];
  }

  // Close a split tab, every pane in it, after asking.
  closeTabItem(g, tab = this.tabsOf.get(g.tab)?.find((x) => x.id === g.tab)) {
    const n = tab?.panes ?? g.rows.length;
    return { id: "close-tab", text: "Close tab…", red: true, act: () => openOverlay({ mod: "confirm", kind: "dialog", width: 440, height: 200,
      props: { title: "Close this tab?", detail: `Closes its ${n} panes and ends their terminals.`, command: { name: "tab.close", args: { id: g.tab, confirmed: true } } } }) };
  }

  // A swarm heading's menu.
  swarmItems(j, k) {
    const c = this.ctx;
    return [
      { id: "view", text: "Open swarm view", act: () => showSwarm(run, setShared, { swarm: j.swarm, folder: j.folder, machine: j.on ?? null, section: "overview" }) },
      this.homes?.get(k) && { id: "side", text: "Open side panel", act: () => this.openSide(this.homes.get(k)) },
      j.comms_hc && { id: "talk", text: "Talk to the communicator", act: () => this.talk(j) },
      "-",
      { id: "spawn", text: "New agent…", act: (cx) => {
        this.ctx = { ...c, step: "spawn", j, said: null }; this.spawnName.set_value(""); this.spawnText.set_value("");
        cx.timer.after(50, () => this.spawnName.focus());
      } },
      { id: "copy", text: "Copy swarm name", act: (cx) => cx.write_to_clipboard(j.swarm) }];
  }

  // New agent in a swarm (`swarm spawn <name> -- <text>`): its own worktree, no task claimed.
  spawnCard(t, c) {
    const box = (input) => div().h(28).px(8).flex().items_center().rounded(7).border(1).border_color(t.border).bg(t.background)
      .child(Input.new(input).h_full().text_size(12.5).text_color(t.foreground));
    return v_flex().w(280).p(12).gap(8).rounded(10).bg(t.popover).border(1).border_color(t.border).shadow_lg().text_size(12.5).text_color(t.foreground)
      .child(div().text_size(13.5).font_semibold().child(`New agent in ${line(c.j.swarm, 40)}`))
      .child(div().line_height(1.4).whitespace_normal().text_color(t.muted).child("Its own worktree, no task claimed. What you write is its first message."))
      .child(box(this.spawnName)).child(box(this.spawnText))
      .when(Boolean(c.said), (el) => el.child(div().line_height(1.4).whitespace_normal().text_color(c.busy ? t.muted : t.blocked).child(c.said)))
      .child(h_flex().gap(8).justify_end()
        .child(look(div().id("spawn-no").px(12).py(5).rounded(8).cursor_pointer(), t).on_click((_e, cx) => { this.ctx = null; cx.notify(); }).child("Cancel"))
        .child(look(div().id("spawn-yes").px(12).py(5).rounded(8).cursor_pointer(), t, "solid").on_click((_e, cx) => this.spawn(cx)).child(c.busy ? "Starting…" : "Start")));
  }

  spawn(cx) {
    const c = this.ctx, name = this.spawnName.value().trim(), text = this.spawnText.value().trim();
    if (c?.step !== "spawn" || c.busy) return;
    if (!/^[A-Za-z0-9][A-Za-z0-9._-]*$/.test(name)) { c.said = "A name of letters, digits, dots, dashes."; cx.notify(); return; }
    c.busy = true; c.said = "Starting…"; cx.notify();
    swarm(c.j.folder, c.j.on ?? null, ["spawn", name, ...(text ? ["--", text] : [])], c.j.swarm)
      .catch((e) => ({ code: 1, stderr: String(e?.message ?? e) }))
      .then((r) => {
        if (this.ctx !== c) return;
        if (r.code === 0) this.ctx = null; else { c.busy = false; c.said = line(r.stderr || r.stdout || "swarm spawn failed", 300); }
        cx.notify();
      });
  }

  // A name as a field while it is renamed: Enter renames, Escape or a click elsewhere leaves it.
  field(t, id, input, leave) {
    return div().id(id).flex_1().min_w(0).h(22).px(6).flex().items_center().rounded(6).border(1)
      .border_color(t.ring ?? t.accent).bg(t.background).cursor_text()
      .on_click((_e, cx) => cx.stop_propagation())
      .on_key_down((e, cx) => { if (e.key === "escape") { leave(); cx.stop_propagation(); cx.notify(); } })
      .child(Input.new(input).h_full().text_size(12.5).text_color(t.foreground));
  }
  spaceField(t, s) { return this.field(t, `respace-${s.id}`, this.spaceInput, () => { this.respace = null; }); }
  tabField(t, tab) { return this.field(t, `retitle-${tab}`, this.tabInput, () => { this.retitle = null; }); }

  // Rename split tab `tab` in place, in its outline's head.
  startRetitle(tab, name, cx) {
    const own = this.tabName.get(tab);
    this.retitle = { tab };
    this.tabInput.set_value(own ?? name ?? ""); cx.notify();
    cx.timer.after(50, () => this.tabInput.focus()); // once the field is drawn
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

  // A tab's rows: a split tab's in a thin outline, with the tab's name over it when it was named. A tab of the rail's
  // own rows (not a swarm's) is a drag target: the line shows before or after it, never inside an outline.
  tabOf(t, s, g, draw) {
    if (!g.tab) return g.rows.map(draw);
    const d = this.drag?.live && this.drag.space === s.id ? this.target() : null;
    // Herdr names a tab after its program ("Claude Code"): only a name someone gave heads the outline.
    let name = g.split && this.tabName.get(g.tab);
    if (g.rows.some((r) => r.t.program?.name === name)) name = null;
    const retitling = g.split && this.retitle?.tab === g.tab;
    const part = Boolean(d) && this.anim && d.tab !== g.tab;
    return [v_flex().id(`tab-${g.tab}`).relative().flex_none()
      .when(g.split, (el) => el.rounded(9).border(1).border_color(alpha(t.foreground, 0.16)))
      .when(d?.tab === g.tab, (el) => el.rounded(9).bg(t.selected).shadow_lg().ml(14))
      // Hover still follows the pointer during a press (moves stop reaching rows once the drag is live).
      .on_hover((h, cx) => {
        if (h) this.overTab = { space: s.id, tab: g.tab }; else if (this.overTab?.tab === g.tab) this.overTab = null;
        if (this.drag?.live) cx.notify();
      })
      // II.4d: the rows part where the tab will land (height, 120 ms); the line sits in the gap
      .when(d?.over === g.tab, (el) => el.child(div().absolute().left(4).right(4).h(2).rounded(1).bg(t.working)
        .when(d.after, (l) => l.bottom(part ? 4 : -1)).when(!d.after, (l) => l.top(part ? 4 : -1))))
      .when(part, (el) => el.child(div().id(`gap-a-${g.tab}`).flex_none().h(d.over === g.tab && !d.after ? 10 : 0).transition("height", 120)))
      .when(retitling, (el) => el.child(h_flex().h(26).flex_none().px(3).pt(3).items_center().child(this.tabField(t, g.tab))))
      // Double click: rename the tab, as on any of its rows.
      .when(!retitling && Boolean(name), (el) => el.child(this.ctxMenu(div().id(`tab-name-${g.tab}`).relative().h(18).flex_none().px(8).text_size(11.5).text_color(t.dim)
        .on_mouse_down("left", (e, cx) => { if (e.click_count === 2) this.startRetitle(g.tab, name, cx); })
        .child(div().truncate().child(line(name, 80))), t, `tab:${g.tab}`, () => [
          { id: "rename", text: "Rename tab", act: (cx) => this.startRetitle(g.tab, name, cx) }, "-", this.closeTabItem(g)])))
      .children(g.rows.map(draw))
      .when(part, (el) => el.child(div().id(`gap-b-${g.tab}`).flex_none().h(d.over === g.tab && d.after ? 10 : 0).transition("height", 120)))];
  }

  // A space's lane (design E): its name, how many terminals (resting on it: its tabs, and `hid`, rail B's word for
  // those a swarm above holds, "2 in nx"; nothing when it has none), + New tab on hover
  // (Part II.2); then its rows by tab. The shown space's name is bright; a click on another's shows it. `fly`: the
  // collapsed rail's hover card, always open and not marked as shown. `sw`: the card's swarm (swarmOf).
  space(t, s, rows, tabNames, shownTerm, now, fly = false, sw = null, hid = null) {
    const own = sw ? sw.rest : rows, on = s.active && !fly && !this.swarmTerm; // a swarm terminal shown lights its lane instead
    const tabs = hid ? tabGroups(rows).filter((g) => g.tab).length : s.tabs.length;
    const groups = tabGroups(own), meta = own.length || "";
    const stop = (_e, cx) => cx.stop_propagation();
    const draw = (r) => this.row(t, r, tabNames.get(r.t.address), !fly && r.t.address === shownTerm, now, { card: !fly });
    const away = this.drag?.live && this.drag.space !== s.id; // no command moves a tab to another space
    return v_flex().id(`${fly ? "fly" : "space"}-${s.id}`).flex_none().when(!fly, (el) => el.mt(9)).when(away, (el) => el.opacity(0.45))
      .child(h_flex().id(`head-${s.id}`).h(24).mb(3).flex_none().pl(8).pr(2).gap(6).items_center().rounded(9).cursor_pointer()
        .hover((st) => st.bg(t.hover))
        .when(!fly, (el) => el.on_hover((h, cx) => this.settle("hot", h, s.id, cx)))
        .on_click(() => { if (this.respace === s.id) return; if (viewShown(layout())) showAll(run, false); else if (!on) run("space.select", { id: s.id }); })
        .when(!fly, (el) => el.on_mouse_down("right", (_e, cx) => { cx.stop_propagation(); this.spaceMenu = s.id; cx.notify(); }))
        .child(!fly && this.respace === s.id ? this.spaceField(t, s)
          : div().flex_shrink_1().min_w(0).max_w(150).truncate().font_semibold().text_color(on || fly ? t.foreground : alpha(t.foreground, 0.7)).child(line(s.name, 80)))
        .child(div().id(`space-n-${s.id}`).flex_1().min_w(0).truncate().text_size(11.5).text_color(alpha(t.foreground, 0.74))
          .when(Boolean(meta), (el) => el.tooltip(`${tabs} ${tabs === 1 ? "tab" : "tabs"}${hid ? `, ${hid}` : ""}`)).child(meta))
        .when(!fly && (this.hot === s.id || this.spaceMenu === s.id), (el) => el.child(this.spaceMenuOf(t, s)))
        .when(!fly && this.hot === s.id, (el) => el.child(h_flex().id(`add-${s.id}`).size(18).flex_none().items_center().justify_center()
          .rounded(6).text_color(t.dim).hover((st) => st.bg(alpha(t.foreground, 0.13)).text_color(t.foreground))
          .on_mouse_down("left", stop).on_click((_e, cx) => { cx.stop_propagation(); this.newTab(s); })
          .child(svg("mods/workspace-chrome/plus.svg").size(12)))))
      .when(Boolean(sw), (el) => el.child(this.block(t, s, sw, tabNames, shownTerm, now, fly)))
      .child(v_flex().flex_none().when(!fly, (el) => el.pl(6)).children(this.capped(t, s.id, groups, (g) => this.tabOf(t, s, g, draw), (g) => g.tab ?? g.rows[0].t.address).flat()));
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
    const trigger = v_flex().id(`tile-${s.id}`).relative().flex_none().items_center().gap(6).cursor_pointer()
      .on_click(() => run("space.select", { id: s.id }))
      .child(h_flex().size(40).items_center().justify_center().rounded(10).border(1)
        .bg(s.active ? t.selected : t.raised).border_color(s.active ? t.accent : t.border)
        .text_size(12).font_semibold().text_color(roll.length ? t.foreground : t.muted).child(abbrev(line(s.name, 80))))
      .child(h_flex().h(7).gap(3).items_center().children(roll.map((k) => mark(t, k, 7))));
    return HoverCard.new(`hover-${s.id}`).anchor("top_left").open_delay(150).trigger(this.ctxMenu(trigger, t, `tile:${s.id}`, () => this.spaceItems(s, false)))
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
    const el = this.draw(cx);
    if (!this.anim) return el;
    for (const a of this.marks.keys()) if (!this.ent.now.has(`row:${a}`)) this.marks.delete(a);
    const now = Date.now();
    for (const [k, g] of this.ghosts) if (now - g.at > 400) this.ghosts.delete(k); // its list wasn't drawn
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
    const ags = agents(), all = looked(terminals(), ags);
    this.agentAddrs = new Set(ags.map((x) => x.address));
    this.pinned = new Set(ags.filter((x) => x.pinned).map((x) => x.address));
    const byAddr = new Map(all.filter((x) => x.state === "live").map((x) => [x.address, x]));
    const ps = panes();
    const sp = this.sp = spaces();
    if (!((sp.find((s) => s.active)?.machine ?? "") in this.load)) this.poll(cx); // a machine not read yet
    const shownTerm = focused()?.terminal ?? null;
    // The question whose options are open; its prompt box is read once per hc msg (boxFor).
    this.hotAsk = this.replying?.a ?? this.askRow ?? this.askPop ?? null;
    const hot = this.hotAsk && byAddr.get(this.hotAsk);
    this.hotBox = hot?.status === "blocked" ? boxFor(this.boxes, hc, this.hotAsk, line(hot.report?.msg, 300), cx) : null;
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
    this.railW = find(layout(), "sidebar")?.size?.px ?? 268;
    const narrow = this.railW < NARROW;
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
    // "Show all" of spaces that are gone (a swarm's, "sw:", stay).
    if (sp.length) for (const set of [this.all, this.more]) for (const id of set) if (!ids.has(id.replace(/^b:/, "")) && !id.startsWith("m:") && !id.startsWith("sw:")) set.delete(id);
    // An agent alone in its tab: the tab's change time is the app's own, kept while the rail isn't shown.
    const tabOf = new Map(sp.flatMap((s) => s.tabs).map((tab) => [tab.id, tab]));
    const changedAt = new Map(ps.filter((p) => p.terminal && tabOf.get(p.tab)?.panes === 1).map((p) => [p.terminal, tabOf.get(p.tab).changed_at]));
    const swRows = [...swOf.values()].flatMap((sw) => sw.block.filter((it) => it.r).flatMap((it) => [it.r, ...it.kids]));
    this.swarmTerm = !narrow && swRows.some((r) => r.t.address === shownTerm);
    this.track([...swRows, ...[...rowsBy.values()].flat()], now, (a) => changedAt.get(a) ?? null, cx);
    setAgentOrder([...swRows, ...[...rowsBy.values()].flat()].filter((r) => AGENT.has(r.mark) && r.pane).map((r) => r.t.address));
    // Pinned (terminal.pin): each pinned row, with what hangs under it, leaves its space for the Pinned lane at the top.
    const pinnedRows = [];
    if (!narrow && this.pinned.size) for (const [id, rows] of rowsBy) {
      const keep = [], where = line(sp.find((s) => s.id === id)?.name, 60);
      for (let i = 0; i < rows.length; i++) {
        if (!this.pinned.has(rows[i].t.address)) { keep.push(rows[i]); continue; }
        const d = rows[i].lines.length;
        let j = i + 1;
        while (j < rows.length && rows[j].lines.length > d) j++;
        pinnedRows.push(...rows.slice(i, j).map((r) => ({ ...r, lines: r.lines.slice(d), split: false, pin: where })));
        i = j - 1;
      }
      rowsBy.set(id, keep);
    }

    // A heading per machine (rail B: always); spaces() lists this computer's first. Under each, its swarms' lanes, then its
    // spaces'.
    const many = ms.length > 1;
    // An unreachable machine's spaces: dimmed, without rows or marks (their state is unknown).
    const dim = (el) => div().flex_none().opacity(0.45).child(el);
    const items = ms.filter((mc) => !mc.hidden).flatMap((mc) => {
      const off = mc.state === "unreachable";
      // Past SPACES spaces, the first ones and the shown one, then a line that shows the rest.
      // a space whose every terminal is in a swarm's lane has nothing of its own to show (tiles keep every space)
      const left = narrow ? mc.spaces : mc.spaces.filter((s) => !hidBy.has(s.id) || rowsBy.get(s.id)?.length);
      const key = `m:${mc.name ?? ""}`, cut = left.length > SPACES && !this.more.has(key);
      const shown = cut ? left.filter((s, i) => i < SPACES - 1 || s.active).slice(0, SPACES) : left;
      const more = cut ? [this.moreLine(t, `more-spaces-${this.mid(mc.name)}`, narrow ? `+${left.length - shown.length}`
        : `${left.length - shown.length} more spaces`, key)] : [];
      if (narrow) {
        const rule = div().id(`machine-${this.mid(mc.name)}`).w(32).h(1).flex_none().bg(t.border);
        return [...(mc.name ? [rule] : []), ...shown.map((s) => off ? dim(this.tile(t, s, [], tabNames, shownTerm, now, null))
          : this.tile(t, s, rowsBy.get(s.id), tabNames, shownTerm, now, swBy.get(s.id))), ...more];
      }
      const none = many && mc.name && !mc.spaces.length && !off ? [h_flex().id(`nospace-${this.mid(mc.name)}`).h(26).flex_none().px(10).gap(6).items_center().text_size(12).text_color(t.dim)
        .child("No spaces open here ·").child(this.act(t, `newspace-${this.mid(mc.name)}`, "New space", () => run("space.new", { machine: mc.name })))] : [];
      const mine = off ? [] : sums.filter((j) => (j.on ?? null) === mc.name && swOf.has(keyOf(j)));
      const lanes = [...mine.map((j) => this.swarmLane(t, j, swOf.get(keyOf(j)), tabNames, shownTerm, now)),
        ...shown.map((s) => off ? dim(this.space(t, s, [], tabNames, shownTerm, now))
          : this.space(t, s, rowsBy.get(s.id), tabNames, shownTerm, now, false, null, hidBy.get(s.id) ?? null))];
      const count = mc.spaces.reduce((n, s) => n + (rowsBy.get(s.id)?.length ?? 0), 0)
        + mine.reduce((n, j) => n + swOf.get(keyOf(j)).block.reduce((m, it) => m + (it.r ? 1 + it.kids.length : 0), 0), 0);
      return [...this.heading(t, mc, now, count), ...none, ...lanes, ...more];
    });

    if (narrow) return v_flex().size_full().min_h(0).pt(10).gap(14).items_center().bg(t.chrome).text_size(13)
      .child(this.button(t, "rail-expand", "chevron-right", () => this.toggle(true)))
      .child(v_flex().id("rail-tiles").flex_1().min_h(0).w_full().pb(12).gap(14).items_center().overflow_y_scrollbar().children(items));
    const pinLane = pinnedRows.length ? [v_flex().id("pinned").flex_none()
      .child(h_flex().h(24).mb(3).flex_none().pl(8).items_center().font_semibold().text_color(t.foreground).child("Pinned"))
      .child(v_flex().flex_none().pl(6).children(pinnedRows.map((r) => this.row(t, r, tabNames.get(r.t.address), r.t.address === shownTerm, now))))] : [];
    const shownSpace = sp.find((s) => s.active);
    const rail = v_flex().id("rail").relative().size_full().min_h(0).bg(t.chrome).text_size(13).track_focus(this.keys)
      // A release drops where the line shows; one outside the rail is seen at the next press, which cancels.
      .on_mouse_up("left", (_e, cx) => { if (this.drag) this.endDrag(cx, true); })
      .on_mouse_down_out((_e, cx) => { if (this.drag) this.endDrag(cx, false); })
      .on_key_down((e, cx) => { if (e.key === "escape" && this.drag) { cx.stop_propagation(); this.endDrag(cx, false); } })
      .on_mouse_move((e, cx) => {
        const dr = this.drag;
        if (dr && !dr.live && Math.abs(e.position.y - dr.y) >= 4) { dr.live = true; dr.pane = focused()?.pane ?? null; this.keys.focus(); cx.notify(); }
      })
      .when(sums.length > 1 || shownAll, (el) => el.child(this.allRow(t, sums, shownAll)))
      .child(v_flex().id("rail-list").flex_1().min_h(0).px(8).pt(8).pb(12).gap(2).overflow_y_scrollbar().children([...pinLane, ...items]))
      .children([this.trouble(t, [...broken, ...this.failed.values()])].filter(Boolean));
    // Right click on the rail's own ground.
    return this.ctxMenu(rail, t, "rail", () => [
      { id: "space", text: "New space", act: () => run("space.new") },
      shownSpace && { id: "tab", text: "New tab", act: () => this.newTab(shownSpace) },
      "-",
      { id: "collapse", text: "Collapse rail", act: () => this.toggle(false) },
      { id: "settings", text: "Settings", act: () => openOverlay({ mod: "rw-settings", kind: "dialog", width: 860, height: 620 }) }]);
  }
}
