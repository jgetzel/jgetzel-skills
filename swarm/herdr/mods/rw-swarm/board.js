// The swarm view of the unified redesign (Swarm Panels Canvas, page "Unified redesign": U-Dir8-rail with U-Dir3-peek's
// peek and U-Dir4-inbox's inbox, and their notes boards). The rail holds the agents; this view holds the board by repo,
// then state, other swarms' tasks quieter, and an Inbox tab of what needs you. A task's click opens the peek (its
// properties, its history from `task show --json`, the answer box) and selects it; the selection is shared with rw-rail
// (tree.js SELECT): an agent picked there lights its tasks here, a task picked here lights its holder there.
// Data: `state --json --view swarms` (tasks[], repos[], needs[] machine-wide), read again only when `events --since`
// returns something (or every 30 s, for ages); rows are placed at fixed heights so a changed task moves to its new
// place, its glyph stamps, and new and gone rows arrive and leave (kit.js motions).

import { div } from "gpui-kit";
import { v_flex, h_flex, InputState, Input, TextView } from "gpui-base";
import { panes, run, shared, setShared, settings, window as win, exec } from "herdr";
import * as kit from "./kit.js";
import { SELECT, addrOf, answerArgs, cancelArgs, childrenArgs, completeArgs, kidsAskOf, dropDepArgs, nudgeArgs, parentArgs, dur, line, prioName, repoName, showAll, stateWord, placeWord, evCells,
  barOf, isClosed, labelCounts, stateCounts, labelGroups, parentTree } from "./tree.js";

// The Board's groups, by state: the key is the glyph's word (kit.taskGlyph); a Ready task waiting on a dep keeps its place in Ready.
const STATES = [["prog", "In Progress"], ["block", "Needs Input"], ["land", "In Review"], ["ready", "Ready"], ["back", "Backlog"], ["done", "Completed today"]];
const WORD = { block: "Needs Input", prog: "In Progress", land: "In Review", ready: "Ready", back: "Backlog", done: "Completed" };
// The Group chip's choices (shared() keeps the pick); a group or parent opens to its first 25 rows, 100 more at a time, a render draws at most 140.
const GROUPS = [["repo", "repo, then state"], ["label", "label"], ["parent", "parent"]];
const GROUP = "rw-swarm.group";
const CAP = 25, CAP_MORE = 100, CAP_ALL = 140, LABELS_SHOWN = 12, INDENT = 16;
const BAR = ["completed", "in_review", "in_progress", "needs_input", "ready", "backlog"];
const ROWP = kit.ROW - 4; // a parent row's glass capsule
const segsOf = (counts) => BAR.map((s) => [s, counts[s] ?? 0]);
const QUIET_READ = 30000; // the board is read again this often without events: its ages and leases move
const LEASE = 7200; // a claim's default lease (2h): the lease bar's full width
const PEEK = 420, IB = 68, NARROW = 760;
const kilo = (n) => (n >= 1000 ? `${Math.round(n / 1000)}k` : String(n ?? 0));
const hhmm = (sec) => (sec ? new Date(sec * 1000).toTimeString().slice(0, 5) : "");
const hash = (x) => { let h = 0; for (const c of String(x)) h = (h * 31 + c.charCodeAt(0)) | 0; return (h >>> 0).toString(36); };
const who = (a) => (a === "human" ? "you" : a ?? "someone");
const openUrl = (url) => url && /^https:\/\//.test(url) && exec(win()?.platform === "macos" ? "open" : "xdg-open", [url]);

// A task's board state: Needs Input, In Progress, In Review, Ready, Backlog, Completed; Cancelled and Duplicate: none.
export function stateOf(k) {
  switch (k.state) {
    case "needs_input": return "block";
    case "in_progress": return "prog";
    case "in_review": return "land";
    case "completed": return "done";
    case "backlog": return "back";
    case "ready": return "ready";
    default: return null;
  }
}
// An agent's kit status from its swarms[] row.
const statusOf = (a) => (!a ? "idle" : a.status === "blocked" ? "asks" : a.hung ? "hung" : a.task?.state === "in_review" ? "landing"
  : a.status === "working" ? "working" : "idle");
// The choices a question offers, from its last sentence's "or": "A, or B?" gives A and B; none past four or 80 chars.
export function choicesOf(q) {
  const last = String(q ?? "").trim().split(/(?<=[.!?])\s+/).pop() ?? "";
  if (!/\bor\b/.test(last) || !last.endsWith("?")) return [];
  const xs = last.replace(/\?$/, "").split(/,?\s+or\s+/).map((x) => x.trim()).filter(Boolean);
  if (xs.length < 2 || xs.length > 4 || xs.some((x) => x.length > 80)) return [];
  return xs.map((x) => x[0].toUpperCase() + x.slice(1));
}
// What a task event says in the peek's history, after who did it.
function evWords(e) {
  const x = e.text ? line(e.text, 200) : "";
  const LABEL = { add: "created", claim: "claimed", spawn: "spawned", renew: "lease renewed", release: "released", block: "question", answer: "answered", unblock: "unblocked", note: "note",
    edit: "edited", land: "to the lander", unland: "from the lander", ci: "CI", pr: "PR", done: "done", drop: "cancelled" };
  return LABEL[e.kind] ? [LABEL[e.kind], x || null] : [e.kind + (x ? " " + x : ""), null];
}
// The state a task is in after event `e` (the history's spine takes its colour); null: unchanged.
const afterEv = (e) => ({ add: "ready", release: "ready", unheld: "ready", ready: "ready", claim: "prog", spawn: "prog", unblock: "prog", answer: "prog",
  unland: "prog", block: "block", land: "land", done: "done", drop: "dropped", held: "back", backlog: "back" })[e.kind] ?? null;

export class SwarmBoard {
  // `swarm(args)`: the swarm CLI for the shown swarm, as rw-swarm's main.js runs it.
  constructor(swarm) {
    this.swarm = swarm;
    this.d = null; this.raw = null; this.err = null; this.flash = null; this.last = null; this.readAt = 0; this.busy = false;
    this.tab = null; this.peek = null; this.pick = null; // the Board's peeked task, the Inbox's picked item (its key)
    this.show = null; this.showFor = null; this.showing = null; // `task show --json` of the peeked or picked task
    this.others = "quiet"; this.doneShown = true; this.inboxAll = false;
    const g = shared(GROUP); this.group = GROUPS.some(([id]) => id === g) ? g : "repo"; // the Board's grouping: repo, label or parent
    this.openBy = new Map(); this.dfltOff = false; this.more = new Map(); this.allLabels = false; // which groups and parents are open, rows past the cap shown
    this.labelFilter = null; this.labelPick = false;
    this.setP = null; this.kidsAsk = null; // the task whose parent is being picked; a refused done or drop, to run again with --children
    this.parentIn = InputState.new({ placeholder: "Find a task" });
    this.parentIn.on("change", (_e, cx) => cx.notify());
    this.lists = {}; this.lastList = null; this.gone = false; // per list: what the last render placed, gone rows still leaving
    this.ans = InputState.new({ placeholder: "Your answer" });
    this.ans.on("submit", (_e, cx) => this.answer(cx));
    this.note = InputState.new({ placeholder: "A note on this task, for its holder" });
    this.note.on("submit", (_e, cx) => this.post(cx));
  }

  // ---- reading ------------------------------------------------------------------------------------------------------
  // One poll: the events since the last; the board again when there are some, or QUIET_READ passed, or `force`.
  tick(cx, w, force = false) {
    const key = `${w.on ?? ""}|${w.swarm ?? ""}`;
    if (key !== this.wKey) { this.wKey = key; this.d = null; this.raw = null; this.last = null; this.tab = null; this.peek = null; this.pick = null; this.show = null; this.showFor = null; }
    if (this.busy || !w.swarm) return;
    this.busy = true;
    cx.spawn(async (cx) => {
      let notify = false;
      try {
        let again = force || !this.d || Date.now() - this.readAt > QUIET_READ;
        const e = await this.swarm(["events", "--json", ...(this.last == null ? ["--limit", "1"] : ["--since", String(this.last)])]);
        if (e.code === 0) {
          const j = JSON.parse(e.stdout), first = this.last == null;
          this.last = j.last ?? this.last;
          const evs = first ? [] : j.events ?? [];
          if (evs.length) {
            again = true;
            const id = this.showFor;
            if (id != null && evs.some((x) => x.task === id)) this.showFor = null; // the open history reads again
          }
        }
        if (again) {
          const r = await this.swarm(["state", "--json", "--view", "swarms"]);
          if (r.code !== 0) throw new Error(line(r.stderr || r.stdout, 300) || `swarm exited ${r.code}`);
          this.readAt = Date.now();
          if (r.stdout !== this.raw) { this.raw = r.stdout; this.d = JSON.parse(r.stdout); notify = true; }
          if (this.err) { this.err = null; notify = true; }
        }
        const want = this.wantShow();
        if (want != null && want !== this.showFor) { await this.readShow(want); notify = true; }
      } catch (err) { this.err = line(err?.message ?? err, 300) || "swarm state failed"; notify = true; }
      this.busy = false;
      if (notify) cx.notify();
    });
  }
  // The task whose history shows: the peeked one, or the picked inbox item's.
  wantShow() {
    if (this.tab === "board") return this.peek;
    return this.items()?.find((n) => n.key === this.pick)?.task ?? null;
  }
  // Read task `id`'s history now (a pick shouldn't wait for the next poll).
  loadShow(cx, id) {
    if (id == null || this.showFor === id || this.showing === id) return;
    this.show = null;
    cx.spawn(async (cx) => { try { await this.readShow(id); } catch { this.showing = null; } cx.notify(); });
  }
  async readShow(id) {
    this.showing = id;
    const r = await this.swarm(["task", "show", String(id), "--json"]);
    if (this.showing !== id) return;
    this.show = r.code === 0 ? JSON.parse(r.stdout) : null; this.showFor = id;
  }
  // One swarm command for the user: what it refused shows under the head; the board reads again after it.
  act(cx, args, ok) {
    this.flash = null; this.kidsAsk = null; cx.notify();
    cx.spawn(async (cx) => {
      try {
        const r = await this.swarm(args);
        if (r.code === 0) ok?.(); else {
          const text = r.stderr || r.stdout;
          this.flash = line(text, 300).replace(/^swarm: /, "") || `swarm exited ${r.code}`;
          // done or drop of a task with open sub-issues is refused without --children: offer the two answers
          this.kidsAsk = kidsAskOf(r, args);
        }
      } catch (e) { this.flash = line(e?.message ?? e, 300); }
      this.showFor = null; cx.notify();
      if (this.sw) this.tick(cx, { on: this.on, swarm: this.sw.name }, true);
    });
  }
  answer(cx) {
    const text = this.ans.value().trim(), id = this.tab === "board" ? this.peek : this.items()?.find((n) => n.key === this.pick)?.task;
    if (text && id != null) this.act(cx, answerArgs(id, text), () => this.ans.set_value(""));
  }
  post(cx) {
    const text = this.note.value().trim();
    if (text && this.peek != null) this.act(cx, ["post", "--", `#${this.peek}`, text], () => this.note.set_value(""));
  }
  focus(name) {
    const a = this.agentsBy?.get(name);
    if (!a?.hc) return;
    showAll(run, false);
    const addr = addrOf(a.hc, this.on), p = panes().find((x) => x.terminal === addr);
    if (p) run("pane.focus", { pane: p.pane }); else run("terminal.peek", { terminal: addr });
  }

  // ---- the model ----------------------------------------------------------------------------------------------------
  // The shown swarm, its repos and members, every agent by name, and each task's board state.
  model(w) {
    const d = this.d;
    this.on = w.on ?? null;
    const sw = (d.swarms ?? []).find((x) => x.name === w.swarm) ?? { name: w.swarm, repos: [], agents: [], needs: [] };
    this.sw = sw;
    this.agentsBy = new Map((d.swarms ?? []).flatMap((s) => (s.agents ?? []).map((a) => [a.name, { ...a, swarm: s.name }])));
    this.scope = (sw.repos ?? []).map((r) => (typeof r === "string" ? r : r.path));
    this.members = new Set((sw.agents ?? []).map((a) => a.name).concat(sw.comms ? [sw.comms] : []));
    this.repoBy = new Map((d.repos ?? []).map((r) => [r.path, r]));
    const tasks = (d.tasks ?? []);
    this.taskBy = new Map(tasks.map((k) => [k.id, { ...k, st: stateOf(k), wait: k.state === "ready" && (k.waiting ?? []).length > 0 }]));
    this.parentIds = new Set(tasks.map((k) => k.parent).filter((p) => p != null));
    const day = new Date(); day.setHours(0, 0, 0, 0);
    this.midnight = day.getTime() / 1000;
  }
  // Whose a task is: the shown swarm's, another swarm's (quiet), or the shown swarm's for lack of anyone else's.
  quiet(k) {
    if (k.holder?.agent) return (k.holder.swarm ?? null) !== this.sw.name;
    const by = k.created_by ? this.agentsBy.get(k.created_by) : null;
    return Boolean(by && by.swarm !== this.sw.name);
  }
  mine(k) {
    const rs = (k.repos ?? []).map((r) => r.repo);
    return rs.some((r) => this.scope.includes(r)) || k.holder?.swarm === this.sw.name || this.members.has(k.created_by)
      || (!rs.length && !k.holder && !(k.created_by && this.agentsBy.has(k.created_by)));
  }
  // The repo groups: the swarm's repos, then the others its tasks touch, then No repo; each with its tasks by state.
  scoped(k) { return this.mine(k) && (this.others !== "hidden" || !this.quiet(k)); }
  today(k) { return this.doneShown && (k.updated ?? 0) >= this.midnight; }
  matcher() { const l = this.labelFilter; return l ? (k) => (k.labels ?? []).includes(l) : null; }
  // The tasks the Board lists: the swarm's (others quiet or hidden), Completed only today, under the label filter.
  shown() {
    const hit = this.matcher();
    return [...this.taskBy.values()].filter((k) => k.st && this.scoped(k) && (k.st !== "done" || this.today(k)) && (!hit || hit(k)));
  }
  groups() {
    const ks = this.shown();
    const paths = [...this.scope], has = new Set(paths);
    for (const k of ks) for (const r of k.repos ?? []) if (!has.has(r.repo) && !this.quiet(k)) { paths.push(r.repo); has.add(r.repo); }
    const of = new Map(paths.map((p) => [p, []]));
    for (const k of ks) for (const p of new Set((k.repos ?? []).map((r) => r.repo))) of.get(p)?.push(k);
    const gs = paths.map((p) => ({ path: p, ks: of.get(p) }));
    const none = ks.filter((k) => !(k.repos ?? []).length);
    if (none.length) gs.push({ path: null, ks: none });
    return gs;
  }
  // What needs you in the swarm's repos (or the whole machine), newest first, each with a stable key.
  items() {
    if (!this.d || !this.sw) return null;
    const now = this.d.now ?? Date.now() / 1000;
    return (this.d.needs ?? []).map((n) => {
      const k = n.task != null ? this.taskBy.get(n.task) : null, a = n.agent ? this.agentsBy.get(n.agent) : null;
      const repos = n.repo ? [n.repo] : (k?.repos ?? []).map((r) => r.repo);
      const ts = n.since ?? (k ? k.updated : null) ?? (a ? now - (a.idle_s ?? 0) : null);
      return { ...n, swarm: n.swarm ?? a?.swarm ?? k?.holder?.swarm ?? null, k, a, repos, ts,
        key: [n.kind, n.task ?? "", n.agent ?? "", n.repo ?? "", n.path ?? ""].join(":") };
    }).filter((n) => this.inboxAll || n.swarm === this.sw.name || n.repos.some((r) => this.scope.includes(r)) || (n.kind === "sub-issues-done" && n.k && this.mine(n.k)))
      .sort((x, y) => (y.ts ?? 0) - (x.ts ?? 0));
  }

  // ---- drawing ------------------------------------------------------------------------------------------------------
  // The view: the head, then the Inbox or the Board. `w` where() of rw-swarm; `width` the view's; `board` the bar's
  // Board section (it opens on the Board; Overview opens on the Inbox while something needs you).
  draw(t, cx, m, { w, width, board }) {
    if (this.gone) { this.gone = false; this.tab = null; } // shown again: it opens as it opens
    this.m = m; this.width = width ?? 1200; this.monoF = settings().font_family;
    if (!this.d) {
      if (!this.busy) this.tick(cx, w);
      return v_flex().id("sb-reading").flex_1().items_center().justify_center().text_size(kit.TYPE.body)
        .text_color(this.err ? t.blocked : t.dim).child(this.err ? `Couldn't read the swarm: ${this.err}` : "Reading the swarm…");
    }
    this.model(w);
    const items = this.items();
    if (this.tab == null) this.tab = board ? "board" : items.length ? "inbox" : "board";
    if (board && this.boardWas !== true) this.tab = "board";
    this.boardWas = board;
    this.sel = shared(SELECT) ?? null;
    const body = this.tab === "inbox" ? this.inbox(t, cx, items) : this.boardTab(t, cx);
    return v_flex().id("sb").flex_1().min_h(0).w_full().bg(t.background).text_color(t.foreground).text_size(kit.TYPE.body)
      .child(this.head(t, items))
      .when(Boolean(this.flash || this.err), (el) => el.child(div().id("sb-flash").flex_none().px(14).py(6).border_b(1).border_color(t.border)
        .text_size(kit.TYPE.meta).text_color(t.blocked).whitespace_normal().child(this.flash ?? `Couldn't read it again: ${this.err}`)))
      .when(Boolean(this.kidsAsk), (el) => el.child(h_flex().id("sb-kids").flex_none().px(14).py(6).gap(8).items_center().border_b(1).border_color(t.border)
        .child(div().text_size(kit.TYPE.meta).text_color(t.dim).child(`#${this.kidsAsk.id} sub-issues`))
        .child(kit.button(t, "sb-kids-cancel", "Cancel them", (cx) => this.act(cx, childrenArgs(this.kidsAsk.args, "cancel")), { small: true, kind: "danger" }))
        .child(kit.button(t, "sb-kids-keep", "Keep them open", (cx) => this.act(cx, childrenArgs(this.kidsAsk.args, "keep")), { small: true }))
        .child(kit.button(t, "sb-kids-no", "Leave it", (cx) => { this.kidsAsk = null; this.flash = null; cx.notify(); }, { small: true, kind: "ghost" }))))
      .child(body);
  }

  // The head: the swarm's tag and name, the tabs (Inbox with its count, Board), its knobs and Talk to its communicator.
  head(t, items) {
    const sw = this.sw, st = sw.staffing ?? {}, n = items.length, m = this.m, c = kit.colors(t);
    const tab = (id, label, count) => h_flex().id(`sb-tab-${id}`).h(28).px(10).gap(6).flex_none().items_center().rounded(kit.R.ctl)
      .cursor_pointer().text_color(this.tab === id ? t.foreground : t.dim).when(this.tab === id, (el) => el.bg(t.selected))
      .hover((s) => s.text_color(t.foreground)).on_click((_e, cx) => { this.tab = id; this.showFor = null; this.tick(cx, { on: this.on, swarm: sw.name }); cx.notify(); })
      .child(label).when(count != null, (el) => el.child(div().id(`sb-count-${count}`).font_family(this.mono()).text_size(kit.TYPE.meta)
        .text_color(count ? c.asks : t.dim).opacity(m.isNew(`count:${count}`) ? 0 : 1).when(m.on, (e) => e.transition("opacity", kit.MOTION.arrive))
        .child(String(count))));
    const knob = (id, label, v, set) => h_flex().id(`sb-knob-${id}`).h(22).px(6).gap(6).flex_none().items_center().rounded(kit.R.ctl)
      .border(1).border_color(t.border).text_size(kit.TYPE.meta).text_color(t.dim).child(label)
      .child(div().id(`sb-${id}-dn`).w(14).text_center().cursor_pointer().hover((s) => s.text_color(t.foreground))
        .on_click((_e, cx) => set(cx, Math.max(0, (v ?? 0) - 1))).child("−"))
      .child(div().font_family(this.mono()).text_color(t.foreground).child(v == null ? "–" : String(v)))
      .child(div().id(`sb-${id}-up`).w(14).text_center().cursor_pointer().hover((s) => s.text_color(t.foreground))
        .on_click((_e, cx) => set(cx, (v ?? 0) + 1)).child("+"));
    const flag = (id, label, on, f) => h_flex().id(`sb-flag-${id}`).h(22).px(6).gap(6).flex_none().items_center().rounded(kit.R.ctl)
      .border(1).border_color(on ? t.working + "88" : t.border).text_size(kit.TYPE.meta).text_color(t.dim).cursor_pointer()
      .hover((s) => s.bg(t.hover)).on_click((_e, cx) => f(cx)).child(label)
      .child(div().font_family(this.mono()).text_color(on ? t.working : t.foreground).child(on ? "on" : "off"));
    const wide = this.width >= NARROW;
    return h_flex().id("sb-head").h(48).flex_none().px(14).gap(8).items_center().min_w(0).border_b(1).border_color(t.border)
      .child(kit.swarmTag(t, sw.name)).child(div().flex_none().text_size(kit.TYPE.title).font_medium().child(`Swarm ${sw.name}`))
      .when(wide, (el) => el.child(div().flex_none().text_size(kit.TYPE.meta).text_color(t.dim)
        .child(this.scope.map(repoName).join(", ") || (this.on ?? "This computer"))))
      .child(h_flex().flex_none().gap(2).ml(8).child(tab("inbox", "Inbox", n)).child(tab("board", "Board", null)))
      .child(div().flex_1())
      .when(wide, (el) => el
        .child(knob("min", "Auto-spawn", st.min, (cx, v) => this.act(cx, ["limits", "--min", String(v)])))
        .child(knob("max", "Max", st.max, (cx, v) => this.act(cx, ["limits", "--max", String(v)])))
        .child(flag("away", "Away", Boolean(sw.away), (cx) => this.act(cx, sw.away ? ["away", "--back"] : ["away"]))))
      .when(Boolean(sw.comms && this.agentsBy.get(sw.comms)?.hc), (el) => el.child(kit.button(t, "sb-talk", `Talk to ${sw.comms}`, () => this.focus(sw.comms))));
  }
  mono() { return this.monoF ?? "JetBrains Mono"; }
  // A list's rows at their places (`placed`: {key, top, ...}): the gone ones, drawn fading out where they were until
  // MOTION.leave ends. A list just shown has none.
  settle(name, placed, cx) {
    const now = Date.now(), L = (this.lists[name] ??= { drawn: new Map(), ghosts: new Map() }), keys = new Set(placed.map((x) => x.key));
    if (this.lastList === name) {
      for (const [k, x] of L.drawn) if (!keys.has(k) && !L.ghosts.has(k)) L.ghosts.set(k, { ...x, at: now });
    } else L.ghosts.clear();
    for (const [k, g] of L.ghosts) if (keys.has(k) || now - g.at > kit.MOTION.leave.duration + 40) L.ghosts.delete(k);
    L.drawn = new Map(placed.map((x) => [x.key, x])); this.lastList = name;
    if (L.ghosts.size) cx.timer.after(kit.MOTION.leave.duration + 50, (cx) => cx.notify());
    return [...L.ghosts.values()];
  }

  // ---- Board --------------------------------------------------------------------------------------------------------
  boardTab(t, cx) {
    const narrow = this.width < NARROW + PEEK, peekK = this.peek != null ? this.taskBy.get(this.peek) ?? (this.show?.id === this.peek ? this.show : { id: this.peek, title: "" }) : null;
    if (this.peek != null && !peekK) this.peek = null;
    const list = v_flex().id("sb-board").flex_1().min_w(0).min_h(0).child(this.filters(t)).child(this.list(t, cx));
    if (this.peek == null) return h_flex().flex_1().min_h(0).items_stretch().child(list);
    const peek = this.peekPane(t, peekK);
    return narrow ? h_flex().flex_1().min_h(0).items_stretch().child(peek.flex_1()) : h_flex().flex_1().min_h(0).items_stretch().child(list).child(peek.w(PEEK).flex_none());
  }
  filters(t) {
    const chip = (id, k, v, f) => h_flex().id(`sb-f-${id}`).h(24).px(8).gap(5).flex_none().items_center().rounded(kit.R.ctl).border(1)
      .border_color(t.border).text_size(kit.TYPE.meta).cursor_pointer().hover((s) => s.bg(t.hover))
      .when(Boolean(f), (el) => el.on_click((_e, cx) => { f(); cx.notify(); }))
      .child(div().text_color(t.dim).child(k)).child(v);
    const sel = this.sel, grouped = this.group !== "repo", lf = this.labelFilter;
    const cycle = () => { this.group = GROUPS[(GROUPS.findIndex(([id]) => id === this.group) + 1) % GROUPS.length][0]; setShared(GROUP, this.group); };
    const labels = this.labelPick ? labelCounts([...this.taskBy.values()].filter((k) => this.scoped(k))).slice(0, 16) : [];
    return v_flex().id("sb-filters").flex_none().border_b(1).border_color(t.border)
      .child(h_flex().flex_none().min_h(40).px(14).py(6).gap(6).items_center().flex_wrap()
        .child(chip("swarm", "Swarm", kit.swarmTag(t, this.sw.name)))
        .child(chip("others", "Other swarms", this.others === "quiet" ? "quieter" : "hidden", () => { this.others = this.others === "quiet" ? "hidden" : "quiet"; }))
        .child(chip("group", "Group", GROUPS.find(([id]) => id === this.group)[1], cycle))
        .child(chip("label", "Label", lf ?? "None", () => { if (lf) { this.labelFilter = null; this.labelPick = false; } else this.labelPick = !this.labelPick; }))
        .child(chip("done", "Completed today", this.doneShown ? "shown" : "hidden", () => { this.doneShown = !this.doneShown; }))
        .when(Boolean(sel), (el) => el.child(chip("sel", sel.from === "task" ? `#${sel.task}` : sel.agent, "clear", () => this.unselect())))
        .child(div().flex_1())
        .when(grouped, (el) => el.child(chip("collapse", "Collapse all", "", () => { this.openBy.clear(); this.dfltOff = true; })))
        .child(chip("list", "Also as", "a list, new task", () => this.view({ section: "board", board: "list" })))
        .child(chip("graph", "Also as", "a graph", () => this.view({ section: "board", board: "graph" }))))
      .when(labels.length > 0, (el) => el.child(h_flex().id("sb-label-pick").px(14).pb(8).gap(6).flex_wrap().children(labels.map(([l, n]) =>
        this.labelChip(t, l, n, `sb-lp-${hash(l)}`, () => { this.labelFilter = l; this.labelPick = false; })))));
  }
  // A label: a glass pill with its dot, its count when it has one; clickable when `on` is given.
  labelChip(t, l, n = null, id = null, on = null) {
    const el = h_flex().h(18).px(7).gap(5).flex_none().items_center().rounded(9).bg(kit.alpha(t.foreground, 0.1)).text_size(kit.TYPE.meta).text_color(kit.alpha(t.foreground, 0.85))
      .child(div().size(6).flex_none().rounded(3).bg(kit.repoColor(t, l))).child(div().max_w(120).truncate().child(line(l, 20)))
      .when(n != null, (e) => e.child(div().font_family(this.mono()).text_color(t.dim).child(String(n))));
    return on ? el.id(id).cursor_pointer().hover((s) => s.bg(kit.alpha(t.foreground, 0.2))).on_click((_e, cx) => { on(); cx.notify(); }) : el;
  }
  // The older Board screens (List with New task, Completed and Cancelled; Graph) stay in main.js.
  view(o) {
    setShared("rw-swarm.view", { ...(shared("rw-swarm.view") ?? {}), ...o, page: null });
  }
  unselect() { setShared(SELECT, null); this.peek = null; this.setP = null; }
  // Click a task: it is picked (its holder lights in the rail) and peeked; click it again to let go.
  pickTask(cx, k) {
    if (this.peek === k.id) { this.unselect(); return cx.notify(); }
    setShared(SELECT, { from: "task", task: k.id, agent: k.holder?.agent ?? null, swarm: k.holder?.swarm ?? null });
    this.peek = k.id; this.setP = null; this.ans.set_value(""); this.note.set_value("");
    this.loadShow(cx, k.id);
    cx.notify();
  }
  selOf(k) {
    const s = this.sel;
    if (!s) return null;
    if (s.from === "task") return k.id === s.task;
    return Boolean(k.holder?.agent && k.holder.agent === s.agent && (k.holder.swarm ?? null) === (s.swarm ?? null));
  }
  // A group is open when toggled so, else by its default (the first label group; no parent), unless Collapse all came since.
  isOpen(key, dflt = false) { return this.openBy.get(key) ?? (dflt && !this.dfltOff); }
  toggle(key, dflt = false) { this.openBy.set(key, !this.isOpen(key, dflt)); }
  // `ks` capped to what `key` shows: the rest and the row that shows 100 more.
  capped(key, ks) { const n = this.more.get(key) ?? CAP; return [ks.slice(0, n), ks.length - n, n]; }
  moreRow(t, key, rest, n, indent = 0, label = "More") {
    return h_flex().id(`sb-more-${hash(key)}`).h(kit.ROW_C).pl(22 + indent).pr(14).gap(8).items_center().text_size(kit.TYPE.meta).text_color(t.dim).cursor_pointer()
      .hover((s) => s.text_color(t.foreground)).on_click((_e, cx) => { if (key === "labels") this.allLabels = true; else this.more.set(key, n + CAP_MORE); cx.notify(); })
      .child(label).child(kit.countBadge(t, rest));
  }
  // A group header of the label and parent views: its chevron, a glass capsule with the name, its count and state bar.
  groupHead(t, id, name, n, segs, open, on, dot = null) {
    return h_flex().id(id).h(kit.HEAD).px(14).gap(8).flex_none().items_center().cursor_pointer().on_click((_e, cx) => { on(); cx.notify(); })
      .child(div().w(12).flex_none().text_color(t.dim).text_size(kit.TYPE.meta).child(open ? "▾" : "▸"))
      .child(kit.glass(h_flex().h(22).px(10).gap(6).min_w(0).items_center().rounded(11).text_size(kit.TYPE.meta).font_medium().text_color(t.foreground), t)
        .when(Boolean(dot), (el) => el.child(div().size(7).flex_none().rounded(4).bg(dot))).child(div().truncate().child(name)))
      .child(kit.countBadge(t, n)).child(div().flex_1()).child(kit.stateBar(t, segs, 96));
  }
  stateOrder(ks) {
    const rank = new Map(STATES.map(([s], i) => [s, i]));
    return [...ks].sort((a, b) => (rank.get(a.st) ?? 9) - (rank.get(b.st) ?? 9) || (a.place ?? 1e9) - (b.place ?? 1e9) || a.id - b.id);
  }
  // Every header and row at its place: a moved task slides there, a new one fades in, a gone one fades out in place.
  list(t, cx) {
    const m = this.m, items = [];
    let y = 0;
    const push = (key, h, el) => { items.push({ key, top: y, h, el }); y += h; };
    if (this.group === "label") this.labelRows(t, push); else if (this.group === "parent") this.parentRows(t, push); else this.repoRows(t, push);
    if (this.group !== "repo" && items.length > CAP_ALL) { items.length = CAP_ALL; const l = items[CAP_ALL - 1]; y = l.top + l.h; }
    if (!items.length) items.push({ key: "empty", top: 0, h: 48, el: () => div().px(22).py(14).text_color(t.dim).child(this.labelFilter ? "No tasks with this label" : "No tasks on this swarm's board") });
    const ghosts = this.settle("board", items, cx);
    const place = (x, gone) => {
      const fresh = !gone && m.isNew(`place:${x.key}`);
      const el = div().id(`sb-at-${x.key}`).absolute().left(0).top(x.top).w_full().h(x.h).opacity(gone || fresh ? 0 : 1).child(x.el());
      return m.on ? el.transition("top", kit.MOTION.move).transition("opacity", gone ? kit.MOTION.leave : kit.MOTION.arrive) : el;
    };
    return v_flex().id("sb-list").flex_1().min_h(0).overflow_y_scrollbar()
      .child(div().id("sb-rows").relative().w_full().flex_none().h(y + 24)
        .children([...items.map((x) => place(x, false)), ...ghosts.map((x) => place(x, true))]));
  }
  repoRows(t, push) {
    for (const g of this.groups()) {
      const gk = g.path ? hash(g.path) : "none";
      push(`g:${gk}`, kit.HEAD, () => this.repoHead(t, g));
      for (const [st, label] of STATES) {
        const ks = g.ks.filter((k) => k.st === st).sort((a, b) => (a.place ?? 1e9) - (b.place ?? 1e9) || a.id - b.id); // Ready and Backlog by place
        if (!ks.length) continue;
        push(`s:${gk}:${st}`, kit.ROW_C, () => kit.stateHeader(t, `sb-st-${gk}-${st}`, st, label, ks.length));
        for (const k of ks) push(`r:${gk}:${k.id}`, kit.ROW, () => this.row(t, k, g.path, gk));
      }
    }
  }
  // By label: a group per label, the most open tasks first, then Unlabelled; a task with two labels is under both (it says so).
  labelRows(t, push) {
    const gs = labelGroups(this.shown()), named = gs.filter((g) => g.label != null), none = gs.find((g) => g.label == null);
    const lf = this.labelFilter, list = [...(lf ? named.filter((g) => g.label === lf) : this.allLabels ? named : named.slice(0, LABELS_SHOWN)), ...(none && !lf ? [none] : [])];
    list.forEach((g, i) => {
      const key = `l:${g.label ?? "\0none"}`, gk = hash(key), open = this.isOpen(key, i === 0);
      push(`lg:${gk}`, kit.HEAD, () => this.groupHead(t, `sb-lg-${gk}`, g.label ?? "Unlabelled", g.ks.length, segsOf(g.counts), open, () => this.toggle(key, i === 0),
        g.label != null ? kit.repoColor(t, g.label) : t.dim));
      if (!open) return;
      const [rows, rest, n] = this.capped(key, this.stateOrder(g.ks));
      for (const k of rows) push(`r:${gk}:${k.id}`, kit.ROW, () => this.row(t, k, null, gk, { drop: g.label }));
      if (rest > 0) push(`mr:${gk}`, kit.ROW_C, () => this.moreRow(t, key, rest, n));
    });
    if (!lf && !this.allLabels && named.length > LABELS_SHOWN) push("lg:more", kit.ROW_C, () => this.moreRow(t, "labels", named.length - LABELS_SHOWN, 0, -8, "More labels"));
  }
  // By parent: the parents as a tree, the most sub-issues first, closed at first; then the tasks with no parent and no children.
  parentRows(t, push) {
    const hit = this.matcher(), tr = parentTree([...this.taskBy.values()].filter((k) => this.scoped(k)), { keep: (k) => k.st === "done" && this.today(k), match: hit });
    this.tree = tr;
    push("sec:parents", kit.ROW_C, () => this.section(t, "sb-sec-parents", "Parents", tr.roots.length));
    const walk = (k, depth) => {
      const kids = tr.kids.get(k.id) ?? [], key = `p:${k.id}`, open = kids.length > 0 && this.isOpen(key);
      push(`pr:${k.id}:${depth}`, kit.ROW, () => this.parentRow(t, k, depth, tr, open, kids.length > 0));
      if (!open) return;
      const [rows, rest, n] = this.capped(key, kids);
      for (const c of rows) {
        if (tr.kids.has(c.id)) walk(c, depth + 1);
        else push(`r:p${k.id}:${c.id}`, kit.ROW, () => this.row(t, c, null, `p${k.id}`, { indent: (depth + 1) * INDENT }));
      }
      if (rest > 0) push(`mr:${key}`, kit.ROW_C, () => this.moreRow(t, key, rest, n, (depth + 1) * INDENT));
    };
    for (const k of tr.roots) walk(k, 0);
    if (tr.none.length) {
      const open = this.isOpen("np");
      push("g:np", kit.HEAD, () => this.groupHead(t, "sb-g-np", "No parent", tr.none.length, segsOf(stateCounts(tr.none)), open, () => this.toggle("np")));
      if (open) {
        const [rows, rest, n] = this.capped("np", this.stateOrder(tr.none.filter((k) => k.st)));
        for (const k of rows) push(`r:np:${k.id}`, kit.ROW, () => this.row(t, k, null, "np"));
        if (rest > 0) push("mr:np", kit.ROW_C, () => this.moreRow(t, "np", rest, n));
      }
    }
  }
  section(t, id, label, n) {
    return h_flex().id(id).h(kit.ROW_C).px(14).gap(8).items_center().text_size(10.5).text_color(t.dim)
      .child(div().child(label.toUpperCase())).child(div().font_family(this.mono()).text_size(kit.TYPE.meta).child(String(n)));
  }
  // A parent: chevron (opens it), its glyph, id, title, its labels with how many sub-issues carry each, and its progress.
  parentRow(t, k, depth, tr, open, kids) {
    const c = kit.colors(t), info = tr.info(k), sel = this.selOf(k), closed = isClosed(k), prog = k.progress;
    const labels = [...info.labels].sort((a, b) => b[1] - a[1] || (a[0] < b[0] ? -1 : 1)).slice(0, 3);
    const chev = div().id(`sb-pc-${k.id}`).size(20).flex_none().flex().items_center().justify_center().text_color(t.dim).text_size(kit.TYPE.meta)
      .when(kids, (el) => el.cursor_pointer().hover((s) => s.text_color(t.foreground)).on_click((_e, cx) => { cx.stop_propagation(); this.toggle(`p:${k.id}`); cx.notify(); }))
      .child(kids ? (open ? "▾" : "▸") : "");
    const body = kit.glass(h_flex().id(`sb-pr-${k.id}`).flex_1().min_w(0).h(ROWP).pl(6).pr(10).gap(8).items_center().rounded(9)
      .text_size(kit.TYPE.body).cursor_pointer().hover((s) => s.bg(kit.alpha(t.foreground, 0.2))).on_click((_e, cx) => this.pickTask(cx, k)), t, sel ? 0.2 : 0.12)
      .child(chev).child(kit.taskGlyph(t, kit.glyphOf(k.state), 12))
      .child(div().w(34).flex_none().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(`#${k.id}`))
      .child(div().flex_1().min_w(0).truncate().text_color(closed ? t.dim : t.foreground).child(k.title ?? ""))
      .when(closed, (el) => el.child(kit.chipText(t, stateWord(k.state))))
      .children(this.width >= NARROW ? labels.map(([l, n]) => this.labelChip(t, l, n)) : [])
      .when(Boolean(prog), (el) => el.child(div().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).flex_none().child(`${prog.done}/${prog.total}`)))
      .child(kit.stateBar(t, barOf(prog, info.leaves), 56));
    return h_flex().size_full().pl(8 + depth * INDENT).pr(8).items_center().child(body);
  }
  repoHead(t, g) {
    const r = g.path ? this.repoBy.get(g.path) : null, c = kit.colors(t);
    const locks = r?.locks ?? [], holders = [...new Set(locks.map((l) => l.agent).filter(Boolean))];
    const meta = g.path ? [r?.base ?? "no base", `${locks.length} ${locks.length === 1 ? "lock" : "locks"}${holders.length === 1 ? ` held by ${holders[0]}` : ""}`].join(", ")
      : "claim only, never auto-spawned";
    const ci = r?.ci?.state, ciEl = ci ? h_flex().flex_none().gap(4).items_center().text_size(kit.TYPE.meta).font_normal()
      .text_color(ci === "green" ? c.done : ci === "red" ? c.asks : t.dim)
      .child(kit.taskGlyph(t, ci === "green" ? "done" : ci === "red" ? "block" : "prog", 10, this.m, `ci:${g.path}:${ci}:${r.ci.sha ?? ""}`))
      .child(`CI ${ci}`) : null;
    const open = g.ks.filter((k) => k.st !== "done").length;
    const right = [...(r?.swarms ?? []).map((s) => kit.swarmTag(t, s)),
      div().flex_none().text_size(kit.TYPE.meta).font_normal().text_color(t.dim).child(`${open} open`)];
    return kit.repoHeader(t, `sb-g-${g.path ? hash(g.path) : "none"}`, { repo: g.path, name: g.path ? repoName(g.path) : "No repo", meta, right: [ciEl, ...right].filter(Boolean) });
  }
  // A task's row; `o.drop`: the label whose group it is in (not repeated), `o.indent`: px of tree depth.
  row(t, k, path, gk, o = {}) {
    const c = kit.colors(t), sel = this.selOf(k), quiet = this.quiet(k);
    const who0 = k.holder?.agent ?? k.assignee ?? null, a = who0 ? this.agentsBy.get(who0) : null;
    const deps = (k.undone ?? []).slice(0, 2).map((d) => { const o = this.taskBy.get(d), dead = o && (o.state === "cancelled" || o.state === "duplicate");
      return h_flex().h(18).px(5).gap(4).flex_none().items_center().rounded(kit.R.tag).border(1).border_color(dead ? c.asks + "88" : t.border).text_size(10).text_color(dead ? c.asks : t.dim)
        .child(kit.taskGlyph(t, kit.glyphOf(o?.state ?? "ready"), 10)).child(div().font_family(this.mono()).when(dead, (e) => e.line_through()).child(`#${d}`)); });
    const place = placeWord(k), note = k.st === "ready" || k.st === "back"
      ? h_flex().gap(6).items_center().children([place ? kit.chipText(t, place) : null, ...deps, k.st === "back" && k.note ? kit.noteChip(t, line(k.note, 60)) : null].filter(Boolean)) : null;
    const tags = (k.repos ?? []).filter((r) => r.repo !== path).map((r) => kit.repoTag(t, r.repo, repoName(r.repo).slice(0, 6)));
    const ls = [...new Set(k.labels ?? [])], other = ls.filter((l) => l !== o.drop);
    if (this.group !== "repo") tags.unshift(...other.slice(0, 2).map((l) => this.labelChip(t, l)), ...(ls.length > 1 && o.drop != null ? [kit.chipText(t, `×${ls.length}`)] : []));
    if (k.st === "block") tags.push(kit.button(t, `sb-ans-${gk}-${k.id}`, "Answer", (cx) => { cx.stop_propagation(); this.pickTask(cx, k); }, { kind: "danger", small: true }));
    const age = (k.updated ?? 0) >= this.midnight ? hhmm(k.updated) : k.updated ? new Date(k.updated * 1000).toDateString().slice(4, 10) : "";
    const el = kit.issueRow(t, this.m, { id: k.id, key: `${gk}:${k.id}`, title: k.title, priority: k.priority, state: k.wait ? "wait" : k.st }, {
      onClick: (cx) => this.pickTask(cx, k), sel, note, age, tags: [h_flex().flex_none().gap(4).items_center().children(tags)],
      assignees: who0 ? [{ name: who0, swarm: k.holder?.swarm ?? a?.swarm, status: statusOf(a) }] : [] });
    const out = quiet && sel !== true ? el.opacity(sel === false ? 0.4 : 0.42) : el;
    return o.indent ? h_flex().size_full().child(div().w(o.indent).flex_none()).child(out.flex_1().min_w(0)) : out;
  }

  // ---- Peek ---------------------------------------------------------------------------------------------------------
  // A task's properties, its history oldest first (its question, when it waits on you, where new entries arrive), and a
  // note to its holder.
  peekPane(t, k) {
    const c = kit.colors(t), m = this.m, id = k.id, st = k.st ?? stateOf(k), h = k.holder?.agent ?? k.assignee ?? k.owner ?? null;
    const a = h ? this.agentsBy.get(h) : null, show = this.showFor === id ? this.show : null;
    const repos = (k.repos ?? []).map((r) => (typeof r === "string" ? { repo: r } : r));
    const stateLine = h_flex().gap(8).items_center().flex_wrap().child(div().text_color(st === "block" ? c.asks : t.foreground).child(stateWord(k.state)))
      .children([placeWord(k) ? kit.chipText(t, placeWord(k)) : null, ["block", "prog", "land"].includes(st) && h ? kit.assignee(t, { name: h, swarm: k.holder?.swarm ?? a?.swarm, status: statusOf(a) }) : null,
        st === "back" && k.note ? kit.noteChip(t, line(k.note, 80)) : null, k.state === "duplicate" && k.dup_of != null ? kit.chipText(t, `duplicate of #${k.dup_of}`) : null].filter(Boolean));
    const fresh = m.isNew(`peek:${id}`);
    const crumbs = show?.ancestors ?? [];
    const head = v_flex().id("sb-pk-head").flex_none().px(16).py(14).gap(8).border_b(1).border_color(t.border)
      .when(crumbs.length > 0, (el) => el.child(h_flex().id("sb-pk-crumbs").gap(4).items_center().flex_wrap().text_size(kit.TYPE.meta).text_color(t.dim)
        .children(crumbs.flatMap((a, i) => [h_flex().id(`sb-crumb-${a.id}`).gap(5).items_center().min_w(0).cursor_pointer().hover((s) => s.text_color(t.foreground))
          .on_click((_e, cx) => this.pickTask(cx, this.taskBy.get(a.id) ?? { id: a.id, holder: null }))
          .child(kit.taskGlyph(t, kit.glyphOf(a.state), 10)).child(div().font_family(this.mono()).child(`#${a.id}`)).child(div().max_w(110).truncate().child(line(a.title ?? "", 24))),
          div().child("›")]))))
      .child(h_flex().gap(6).items_center()
        .children(repos.map((r) => kit.repoTag(t, r.repo, repoName(r.repo).slice(0, 6))))
        .child(div().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(`#${id}`)).child(div().flex_1())
        .when(Boolean(a?.hc), (el) => el.child(kit.button(t, "sb-pk-term", "Open terminal", () => this.focus(h), { small: true })))
        .child(kit.button(t, "sb-pk-copy", "Copy id", (cx) => cx.write_to_clipboard?.(`#${id}`), { small: true }))
        .child(kit.button(t, "sb-pk-close", "Close", (cx) => { this.unselect(); cx.notify(); }, { kind: "ghost", small: true })))
      .child(div().text_size(kit.TYPE.head).font_medium().whitespace_normal().child(k.title ?? ""))
      .child(h_flex().gap(6).items_center().text_color(st === "block" ? c.asks : t.dim).child(kit.taskGlyph(t, k.wait && st === "ready" ? "wait" : st, 12, m, `pk:${id}:${st}`)).child(stateLine));
    const prop = (label, v) => h_flex().gap(12).items_start().min_w(0)
      .child(div().w(86).flex_none().text_color(t.dim).child(label)).child(h_flex().flex_1().min_w(0).gap(6).items_center().flex_wrap().children([v].flat()));
    const blocks = [...this.taskBy.values()].filter((x) => (x.after ?? []).includes(id) && x.st && x.st !== "done").map((x) => `#${x.id}`);
        const lease = k.lease_left_s;
    const props = v_flex().id("sb-pk-props").flex_none().px(16).py(12).gap(8)
      .child(prop("State", [kit.taskGlyph(t, st), div().child(stateWord(k.state))]))
      .child(prop("Priority", div().child(prioName(k.priority) ?? "Medium")))
      .when(k.place != null, (el) => el.child(prop(k.state === "backlog" ? "Backlog" : "Queue", div().font_family(this.mono()).child(String(k.place)))))
      .when(repos.length > 0, (el) => el.child(prop("Repos", v_flex().gap(4).children(repos.map((r) => h_flex().gap(6).items_center().flex_wrap()
        .child(kit.repoTag(t, r.repo, repoName(r.repo).slice(0, 6))).child(div().child(repoName(r.repo)))
        .when(Boolean(r.base), (e) => e.child(div().text_size(kit.TYPE.meta).text_color(t.dim).child(`base ${r.base}`)))
        .when(Boolean(r.worktree), (e) => e.child(div().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(repoName(r.worktree)))))))))
      .child(prop("Assignee", h ? [kit.assignee(t, { name: h, swarm: k.holder?.swarm ?? a?.swarm, status: statusOf(a) }),
        ...(a?.ctx ? [div().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(kilo(a.ctx))] : [])] : div().text_color(t.dim).child("Nobody")))
      .when(lease != null, (el) => el.child(prop("Lease", [div().w(90).h(3).flex_none().rounded(2).bg(t.border).overflow_hidden()
        .child(kit.grow(div().h_full().bg(lease < 600 ? c.working : t.dim), m, (lease / LEASE) * 100)),
        div().text_size(kit.TYPE.meta).text_color(t.dim).child(lease > 0 ? `${dur(lease * 1000)} left` : "lapsed")])))
      .child(prop("Parent", this.parentProp(t, k, show)))
      .when(this.setP === id, (el) => el.child(this.parentPicker(t, k, show)))
      .when((k.parents ?? []).length > 0, (el) => el.child(prop("Filed from", k.parents.map((d) => kit.chipText(t, `#${d}`)))))
      .when(Boolean(k.progress), (el) => el.child(prop("Progress", [div().font_family(this.mono()).child(`${k.progress.done}/${k.progress.total}`),
        kit.stateBar(t, barOf(k.progress, (show?.sub_issues ?? []).filter((x) => !isClosed(x))), 96)])))
      .child(prop("Waiting on", (k.after ?? []).length ? (k.after).map((d) => kit.chipText(t, `#${d}`)) : div().text_color(t.dim).child("Nothing")))
      .when(blocks.length > 0, (el) => el.child(prop("Needed by", blocks.map((d) => kit.chipText(t, d)))))
      .when((k.labels ?? []).length > 0, (el) => el.child(prop("Labels", k.labels.map((l) => h_flex().h(16).px(4).flex_none().items_center()
        .rounded(kit.R.tag).border(1).border_color(t.border).font_family(this.mono()).text_size(10).text_color(t.dim).child(l)))))
      .when(Boolean(k.created_by), (el) => el.child(prop("Created by", div().child(who(k.created_by)))));
    const body = v_flex().id(`sb-pk-${id}`).flex_none().gap(0).opacity(fresh ? 0 : 1).when(m.on, (e) => e.transition("opacity", kit.MOTION.arrive))
      .child(props).when((show?.sub_issues ?? []).length > 0, (el) => el.child(this.subIssues(t, k, show))).child(this.history(t, k, st, show, h)).child(this.composer(t, id));
    return v_flex().id("sb-peek").min_h(0).min_w(0).border_l(1).border_color(t.border)
      .when(this.width < NARROW + PEEK, (el) => el.child(h_flex().id("sb-pk-back").flex_none().h(32).px(14).items_center().cursor_pointer()
        .text_size(kit.TYPE.meta).text_color(t.dim).hover((s) => s.text_color(t.foreground)).on_click((_e, cx) => { this.unselect(); cx.notify(); }).child("‹ Board")))
      .child(head).child(v_flex().id("sb-pk-scroll").flex_1().min_h(0).overflow_y_scrollbar().child(body));
  }
  // The Parent property: the parent as a chip with Change and Remove, or None with Set parent.
  parentProp(t, k, show) {
    const pid = k.parent ?? show?.parent ?? null, p = pid != null ? this.taskBy.get(pid) : null;
    if (pid == null) return [div().text_color(t.dim).child("None"), kit.button(t, "sb-pk-setp", "Set parent", () => this.openPicker(k.id), { small: true, kind: "ghost" })];
    return [kit.taskGlyph(t, kit.glyphOf(p?.state ?? "ready"), 12), div().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(`#${pid}`),
      div().id("sb-pk-parent").min_w(0).max_w(190).truncate().cursor_pointer().hover((s) => s.text_color(t.dim)).on_click((_e, cx) => this.pickTask(cx, p ?? { id: pid, holder: null })).child(p?.title ?? show?.parent_title ?? ""),
      kit.button(t, "sb-pk-chp", "Change", () => this.openPicker(k.id), { small: true, kind: "ghost" }),
      kit.button(t, "sb-pk-rmp", "Remove parent", (cx) => this.act(cx, parentArgs(k.id, null)), { small: true, kind: "ghost" })];
  }
  openPicker(id) { this.setP = this.setP === id ? null : id; this.parentIn.set_value(""); }
  // Open tasks to pick as the parent of `k`, filtered by what is typed; the ones its body mentions as #N come first, then goals (tasks with sub-issues).
  parentChoices(k, show) {
    const q = this.parentIn.value().trim().toLowerCase(), said = new Set([...String(show?.body ?? "").matchAll(/#(\d+)/g)].map((m) => Number(m[1])));
    const below = (x) => { for (let p = x.parent, n = 0; p != null && n < 60; p = this.taskBy.get(p)?.parent, n++) if (p === k.id) return true; return false; };
    return [...this.taskBy.values()].filter((x) => x.id !== k.id && x.id !== k.parent && !isClosed(x) && !below(x) && (!q || `#${x.id} ${x.title ?? ""}`.toLowerCase().includes(q)))
      .sort((a, b) => Number(said.has(b.id)) - Number(said.has(a.id)) || Number(this.parentIds.has(b.id)) - Number(this.parentIds.has(a.id)) || b.id - a.id)
      .slice(0, 8).map((x) => ({ x, said: said.has(x.id) }));
  }
  parentPicker(t, k, show) {
    const field = div().id("sb-parent-field").flex_1().min_w(120).h(28).px(10).flex().items_center().rounded(kit.R.ctl).border(1).border_color(t.border).bg(t.background)
      .cursor_text().on_mouse_down("left", (_e, cx) => cx.stop_propagation()).on_key_down((e, cx) => { if (e.key === "escape") { this.setP = null; cx.notify(); } })
      .child(Input.new(this.parentIn).h_full().text_size(kit.TYPE.body).text_color(t.foreground));
    return kit.glass(v_flex().id("sb-parent-pick").gap(4).p(6).rounded(9).min_w(0), t, 0.08)
      .child(h_flex().gap(6).items_center().child(field).child(kit.button(t, "sb-parent-x", "Close", (cx) => { this.setP = null; cx.notify(); }, { small: true, kind: "ghost" })))
      .children(this.parentChoices(k, show).map(({ x, said }) => h_flex().id(`sb-pp-${x.id}`).h(26).px(6).gap(8).items_center().rounded(kit.R.ctl).cursor_pointer().hover((s) => s.bg(t.hover))
        .on_click((_e, cx) => this.act(cx, parentArgs(k.id, x.id), () => { this.setP = null; }))
        .child(kit.taskGlyph(t, kit.glyphOf(x.state), 12)).child(div().w(34).flex_none().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(`#${x.id}`))
        .child(div().flex_1().min_w(0).truncate().child(x.title ?? "")).when(said, (el) => el.child(kit.chipText(t, "mentioned")))));
  }
  // The Sub-issues section: its direct children with their state glyphs, and how far they are.
  subIssues(t, k, show) {
    const kids = show.sub_issues ?? [], [rows, rest, n] = this.capped(`si:${k.id}`, kids), prog = show.progress ?? k.progress;
    return v_flex().id("sb-subs").flex_none().px(16).py(10).gap(2).border_t(1).border_color(t.border)
      .child(h_flex().h(26).gap(8).items_center().child(div().text_color(t.dim).child("Sub-issues")).child(kit.countBadge(t, kids.length)).child(div().flex_1())
        .when(Boolean(prog), (el) => el.child(div().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(`${prog.done}/${prog.total}`))
          .child(kit.stateBar(t, barOf(prog, kids.filter((x) => !isClosed(x))), 80))))
      .children(rows.map((c) => h_flex().id(`sb-si-${c.id}`).h(26).gap(8).items_center().min_w(0).cursor_pointer().hover((s) => s.text_color(t.dim))
        .on_click((_e, cx) => this.pickTask(cx, this.taskBy.get(c.id) ?? { id: c.id, holder: null }))
        .child(kit.taskGlyph(t, kit.glyphOf(c.state), 12)).child(div().w(34).flex_none().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(`#${c.id}`))
        .child(div().flex_1().min_w(0).truncate().text_color(isClosed(c) ? t.dim : t.foreground).child(c.title ?? ""))
        .when(Boolean(c.owner), (el) => el.child(div().flex_none().text_size(kit.TYPE.meta).text_color(t.dim).child(c.owner)))))
      .when(rest > 0, (el) => el.child(this.moreRow(t, `si:${k.id}`, rest, n)));
  }
  // The history: an entry per event on a spine in the colour of the state it left the task in; the open question with
  // its choices and the answer box; then "Now".
  history(t, k, st, show, h, withAsk = true) {
    const c = kit.colors(t), m = this.m, col = (s) => ({ prog: c.working, block: c.asks, land: c.landing, done: c.done })[s] ?? t.dim;
    const evs = show?.events ?? [];
    let cur = "ready";
    const ctx = { prio: new Map(), list: new Map() };
    const rows = evs.map((e) => {
      const cs = evCells(e.kind, e.text, k.id, ctx);
      cur = afterEv(e) ?? cur;
      const [words, more] = evWords(e), quietEv = e.kind === "renew";
      const el = h_flex().id(`sb-ev-${e.id}`).relative().flex_none().gap(8).items_start().min_w(0).py(quietEv ? 3 : 6)
        .child(div().absolute().top(0).bottom(0).left(5).w(1).bg(col(cur)))
        .child(div().absolute().top(quietEv ? 7 : 10).left(2).size(8).rounded(4).bg(col(cur)))
        .child(div().w(12).flex_none())
        .child(v_flex().flex_1().min_w(0).gap(4)
          .child(h_flex().gap(4).min_w(0).text_color(quietEv ? t.dim : t.foreground).text_size(quietEv ? kit.TYPE.meta : kit.TYPE.body)
            .child(div().flex_none().font_medium().child(who(e.agent))).child(cs ? kit.cells(t, cs) : div().min_w(0).whitespace_normal().text_color(t.dim).child(words)))
          .when(Boolean(more) && !cs, (el) => el.child(div().px(8).py(6).rounded(kit.R.ctl).bg(t.surface).text_size(kit.TYPE.body).whitespace_normal()
            .child(TextView.markdown(`sb-ev-md-${e.id}`, more)))))
        .child(div().flex_none().font_family(this.mono()).text_size(10).text_color(t.dim).child(hhmm(e.ts)));
      return el.opacity(m.isNew(`ev:${e.id}`) ? 0 : 1).when(m.on, (x) => x.transition("opacity", kit.MOTION.arrive));
    });
    const q = (this.d.needs ?? []).find((n) => n.kind === "ask" && n.task === k.id);
    const ask = withAsk && st === "block" ? this.askCard(t, k, q?.question ?? evs.filter((e) => e.kind === "block").pop()?.text ?? "", h) : null;
    const since = k.updated ? dur(Date.now() - k.updated * 1000) : "";
    const now = h_flex().id("sb-ev-now").flex_none().gap(8).items_center().py(6)
      .child(div().w(12).flex_none().flex().justify_center().child(div().size(8).rounded(4).bg(col(st))))
      .child(h_flex().flex_1().gap(8).items_center().text_color(st === "block" ? c.asks : t.dim).child(div().child("Now")).child(div().text_color(t.foreground).child(WORD[st] ?? stateWord(k.state)))
        .when(Boolean(since), (el) => el.child(div().font_family(this.mono()).text_size(kit.TYPE.meta).child(since))));
    return v_flex().id("sb-history").flex_none().px(16).py(12).gap(0).border_t(1).border_color(t.border)
      .when(!show, (el) => el.child(div().py(6).text_size(kit.TYPE.meta).text_color(t.dim).child("Reading its history…")))
      .children(rows).when(Boolean(ask), (el) => el.child(div().py(6).child(ask))).child(now);
  }
  askCard(t, k, question, h) {
    const choices = choicesOf(question);
    const field = div().id("sb-ans-field").flex_1().min_w(120).h(28).px(10).flex().items_center().rounded(kit.R.ctl).border(1)
      .border_color(t.border).bg(t.background).cursor_text().on_mouse_down("left", (_e, cx) => cx.stop_propagation())
      .on_key_down((e, cx) => { if (e.key === "escape") { this.ans.set_value(""); cx.notify(); } })
      .child(Input.new(this.ans).h_full().text_size(kit.TYPE.body).text_color(t.foreground));
    const age = k.updated ? dur(Date.now() - k.updated * 1000) : "";
    return v_flex().gap(6)
      .child(kit.askSurface(t, `sb-ask-${k.id}`, { agent: h, task: k.id, age, question, field,
        onSend: (cx) => this.answer(cx), onOpen: this.agentsBy.get(h)?.hc ? () => this.focus(h) : null }))
      .when(choices.length > 0, (el) => el.child(h_flex().gap(6).flex_wrap().children(choices.map((x, i) =>
        kit.button(t, `sb-choice-${k.id}-${i}`, x, (cx) => { this.ans.set_value(x); cx.notify(); }, { small: true })))));
  }
  composer(t, id) {
    return h_flex().id("sb-composer").flex_none().px(16).py(10).gap(8).items_center().border_t(1).border_color(t.border)
      .child(div().id("sb-note-field").flex_1().min_w(120).h(28).px(10).flex().items_center().rounded(kit.R.ctl).border(1)
        .border_color(t.border).bg(t.background).cursor_text().on_mouse_down("left", (_e, cx) => cx.stop_propagation())
        .on_key_down((e, cx) => { if (e.key === "escape") { this.note.set_value(""); cx.notify(); } })
        .child(Input.new(this.note).h_full().text_size(kit.TYPE.body).text_color(t.foreground)))
      .child(kit.button(t, `sb-post-${id}`, "Post", (cx) => this.post(cx)));
  }

  // ---- Inbox --------------------------------------------------------------------------------------------------------
  // What needs you, newest first: each item leads with the glyph it is about, names its task, repos and agent; the
  // picked one shows beside the list with the action that clears it. An item that clears leaves; the rest move up.
  inbox(t, cx, items) {
    const m = this.m;
    if (this.pick && !items.some((n) => n.key === this.pick)) this.pick = null;
    if (!this.pick && items.length && this.width >= NARROW) this.pick = items[0].key;
    const narrow = this.width < NARROW, picked = items.find((n) => n.key === this.pick);
    const placed = items.map((n, i) => ({ key: `ib:${n.key}`, top: i * IB, n }));
    const ghosts = this.settle("inbox", placed, cx);
    const place = (x, gone) => {
      const fresh = !gone && m.isNew(`place:${x.key}`);
      const el = div().id(`sb-at-${x.key}`).absolute().left(0).top(x.top).w_full().h(IB).opacity(gone || fresh ? 0 : 1).child(this.item(t, x.n));
      return m.on ? el.transition("top", kit.MOTION.move).transition("opacity", gone ? kit.MOTION.leave : kit.MOTION.arrive) : el;
    };
    const chip = h_flex().id("sb-ib-scope").h(24).px(8).gap(5).flex_none().items_center().rounded(kit.R.ctl).border(1).border_color(t.border)
      .text_size(kit.TYPE.meta).cursor_pointer().hover((s) => s.bg(t.hover)).on_click((_e, cx) => { this.inboxAll = !this.inboxAll; cx.notify(); })
      .child(div().text_color(t.dim).child("Scope")).child(this.inboxAll ? "the whole machine" : this.scope.map(repoName).join(", ") || this.sw.name);
    const list = v_flex().id("sb-ib").min_h(0).min_w(0)
      .child(h_flex().id("sb-ib-head").flex_none().min_h(40).px(14).gap(8).items_center().border_b(1).border_color(t.border)
        .child(div().font_medium().child("Needs you")).child(div().text_size(kit.TYPE.meta).text_color(t.dim).child("Newest first"))
        .child(div().flex_1()).child(chip))
      .child(v_flex().id("sb-ib-list").flex_1().min_h(0).overflow_y_scrollbar()
        .child(items.length ? div().id("sb-ib-rows").relative().w_full().flex_none().h(items.length * IB)
          .children([...placed.map((x) => place(x, false)), ...ghosts.map((x) => place(x, true))])
          : div().px(14).py(14).text_color(t.dim).child("Nothing needs you. The board is one tab over.")));
    if (narrow) return picked ? v_flex().flex_1().min_h(0).child(h_flex().id("sb-ib-back").flex_none().h(32).px(14).items_center().cursor_pointer()
      .text_size(kit.TYPE.meta).text_color(t.dim).on_click((_e, cx) => { this.pick = null; cx.notify(); }).child("‹ Inbox")).child(this.detail(t, picked))
      : list.flex_1();
    return h_flex().flex_1().min_h(0).items_stretch().child(list.w(380).flex_none().border_r(1).border_color(t.border))
      .child(picked ? this.detail(t, picked) : div().flex_1());
  }
  // An item as fields: a lead (the task's number and title, an agent, a path), its glyph word, and chips (a state word, what it waits on).
  itemWords(n, t) {
    const k = n.k, task = n.task != null ? `#${n.task}` : "", lead = k ? `${task} ${k.title ?? ""}`.trim() : task, c = kit.colors(t), red = (s) => kit.chipText(t, s).text_color(c.asks);
    switch (n.kind) {
      case "ask": return [lead || n.agent || "", "asks", []];
      case "hung": return [n.agent ?? "", "hung", [red("hung"), ...(n.stay ? [kit.chipText(t, line(n.stay, 40))] : [])]];
      case "lander": return [lead, "land", [kit.chipText(t, "In Review"), ...(n.lander ? [kit.chipText(t, n.lander)] : [])]];
      case "dep-cancelled": return [lead, "wait", (n.deps ?? []).map((d) => h_flex().h(18).px(5).gap(4).flex_none().items_center().rounded(kit.R.tag).border(1).border_color(c.asks + "88").text_size(10).text_color(c.asks)
        .child(kit.taskGlyph(t, "cancel", 10)).child(div().child("waiting on")).child(div().font_family(this.mono()).line_through().child(`#${d}`)))];
      case "lock": return [n.path ?? "", "idle", [kit.chipText(t, "locked"), kit.chipText(t, n.agent && !this.agentsBy.has(n.agent) ? "holder gone" : "past its lease")]];
      case "ctx": return [n.agent ?? "", "working", [kit.chipText(t, `context ${kilo(n.ctx)}`)]];
      case "ci-red": return [repoName(n.repo), "block", [red("CI red")]];
      case "sub-issues-done": return [lead, "done", [kit.chipText(t, "sub-issues done"), ...(n.progress ? [kit.chipText(t, `${n.progress.done}/${n.progress.total}`)] : [])]];
      default: return [`${n.kind}${task ? ` ${task}` : ""}`, "idle", []];
    }
  }
  glyph(t, n, kind) {
    return ["asks", "hung", "working", "idle", "landing"].includes(kind) ? kit.agentGlyph(t, kind) : kit.taskGlyph(t, kind, 12, this.m, `ib:${n.key}:${kind}`);
  }
  item(t, n) {
    const [words, kind, chips] = this.itemWords(n, t), on = this.pick === n.key, k = n.k;
    const held = !k && n.agent ? this.agentsBy.get(n.agent)?.task : null, sub = held ? `#${held.id} ${held.title ?? ""}` : "";
    const age = n.ts ? dur(Date.now() - n.ts * 1000) : "";
    return h_flex().id(`sb-ib-${hash(n.key)}`).size_full().px(14).py(8).gap(10).items_start().border_b(1).border_color(t.border)
      .cursor_pointer().when(on, (el) => el.bg(t.selected)).when(!on, (el) => el.hover((s) => s.bg(t.hover)))
      .on_click((_e, cx) => { this.pick = n.key; this.ans.set_value(""); this.loadShow(cx, n.task); cx.notify(); })
      .child(div().pt(3).flex_none().child(this.glyph(t, n, kind)))
      .child(v_flex().flex_1().min_w(0).gap(2)
        .child(div().truncate().text_color(kind === "asks" || n.kind === "ci-red" ? kit.colors(t).asks : t.foreground).child(words))
        .child(div().truncate().text_size(kit.TYPE.meta).text_color(t.dim).child(sub))
        .child(h_flex().gap(6).items_center().children(chips).children(n.repos.slice(0, 3).map((r) => kit.repoTag(t, r, repoName(r).slice(0, 6))))
          .when(Boolean(n.agent), (el) => el.child(kit.assignee(t, { name: n.agent, swarm: n.swarm, status: statusOf(n.a) })))))
      .child(div().flex_none().font_family(this.mono()).text_size(10).text_color(t.dim).child(age));
  }
  // The picked item: what it is about, the action that clears it, and its task's history and properties.
  detail(t, n) {
    const [words, kind, chips] = this.itemWords(n, t), k = n.k, c = kit.colors(t);
    const acts = [];
    const term = (name, label) => this.agentsBy.get(name)?.hc ? kit.button(t, `sb-d-term-${name}`, label, () => this.focus(name)) : null;
    const openTask = (id) => kit.button(t, `sb-d-open-${id}`, "Open on the board", (cx) => {
      const x = this.taskBy.get(id); this.tab = "board"; if (x) this.pickTask(cx, x); else cx.notify(); });
    switch (n.kind) {
      case "hung": case "ctx":
        acts.push(kit.button(t, `sb-d-nudge`, "Nudge", (cx) => this.act(cx, nudgeArgs(n.agent)), { kind: "primary" }), term(n.agent, "Open its terminal")); break;
      case "lander": acts.push(openTask(n.task), term(n.lander, "Open the lander's terminal")); break;
      case "dep-cancelled": if (k) acts.push(kit.button(t, "sb-d-rmdep", "Remove dependency", (cx) => this.act(cx, dropDepArgs(k, n.deps ?? [])), { kind: "primary" }),
        kit.button(t, "sb-d-cancel", "Cancel task", (cx) => this.act(cx, cancelArgs(n.task))), openTask(n.task)); break;
      case "lock": acts.push(term(n.agent, "Open the holder's terminal")); break;
      case "ci-red": if (n.url) acts.push(kit.button(t, "sb-d-run", "Open the run", () => openUrl(n.url), { kind: "primary" })); break;
      case "ask": if (n.task != null) acts.push(openTask(n.task)); break;
      case "sub-issues-done": if (n.task != null) acts.push(kit.button(t, "sb-d-complete", "Complete", (cx) => this.act(cx, completeArgs(n.task)), { kind: "primary" }),
        kit.button(t, "sb-d-open", "Open", (cx) => { const x = this.taskBy.get(n.task); this.tab = "board"; if (x) this.pickTask(cx, x); else cx.notify(); })); break;
    }
    const meter = n.kind === "ctx" && n.limit ? h_flex().gap(8).items_center().child(div().w(160).h(3).rounded(2).bg(t.border).overflow_hidden()
      .child(kit.grow(div().h_full().bg(c.working), this.m, (n.ctx / n.limit) * 100))).child(div().text_size(kit.TYPE.meta).text_color(t.dim)
      .child(`${kilo(n.ctx)} of ${kilo(n.limit)}, the nudge mark`)) : null;
    const show = k && this.showFor === k.id ? this.show : null;
    return v_flex().id(`sb-d-${hash(n.key)}`).flex_1().min_w(0).min_h(0).overflow_y_scrollbar()
      .child(v_flex().flex_none().px(16).py(14).gap(8).border_b(1).border_color(t.border)
        .child(h_flex().gap(8).items_center().flex_wrap().child(this.glyph(t, n, kind)).child(div().font_medium().text_size(kit.TYPE.title).whitespace_normal().child(words)).children(chips))
        .when(Boolean(k), (el) => el.child(h_flex().gap(6).items_center().flex_wrap()
          .child(div().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(`#${k.id}`)).child(div().child(k.title ?? ""))
          .children(n.repos.map((r) => kit.repoTag(t, r, repoName(r).slice(0, 6))))
          .when(Boolean(k.holder?.agent), (e) => e.child(kit.assignee(t, { name: k.holder.agent, swarm: k.holder.swarm, status: statusOf(this.agentsBy.get(k.holder.agent)) })))))
        .when(n.kind === "ask" && Boolean(k), (el) => el.child(this.askCard(t, k, n.question ?? "", n.agent)))
        .when(Boolean(meter), (el) => el.child(meter))
        .when(n.kind === "sub-issues-done" && Boolean(n.progress), (el) => el.child(h_flex().gap(8).items_center()
          .child(div().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(`${n.progress.done}/${n.progress.total}`)).child(kit.stateBar(t, barOf(n.progress, []), 160))))
        .when(acts.filter(Boolean).length > 0, (el) => el.child(h_flex().gap(8).flex_wrap().children(acts.filter(Boolean)))))
      .when(Boolean(k), (el) => el.child(this.history(t, k, k.st, show, k.holder?.agent ?? n.agent, n.kind !== "ask")));
  }
}
