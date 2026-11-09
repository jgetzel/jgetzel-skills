import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex } from "gpui-base";
import { spaces, panes, focused, exec, theme, layout, run, appHome, window, settings, watchFolder } from "herdr";

// Locally mods/swarm is a symlink into the repo, so this is the swarm CLI of the same checkout; on another
// machine it is that machine's installed skill. `state --json` is read-only; `args` pick the view.
const swarmState = (cwd, on, args) => on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB python3 "$HOME/.claude/skills/swarm/swarm" state --json "$@"', "sh", ...args], { cwd, on })
  : exec("env", ["-u", "SWARM_DB", "python3", `${appHome()}/mods/swarm/../../../swarm`, "state", "--json", ...args], { cwd });
// POLL: the fastest rate, while the db changes. QUIET_POLL: a watched local db that hasn't changed (idle
// timers, cache countdowns and the machine reading still move). REMOTE_POLL: other machines, unwatched.
const POLL = 3000, QUIET_POLL = 30000, REMOTE_POLL = 10000, PR_POLL = 60000;
const CTX_MAX = 600000, FINISH = 350000, HANDOFF = 550000; // the context bar's scale and its two ticks
// [id, label, label width in px at 11.5]: the segment highlight slides between computed lefts
const TABS = [["overview", "Overview", 52], ["agents", "Agents", 40], ["board", "Board", 32], ["activity", "Activity", 46], ["system", "System", 42]];
const RED = new Set(["overlap", "conflict", "conflict-error", "pressure", "ci-red", "orphan-kill", "lock-violation", "blocked", "task-blocked"]);
const QUIET = new Set(["post", "wake", "heavy-start", "status", "digest", "startable", "deny-cold", "heavy-count"]);

function find(node, id) {
  if (node?.id === id) return node;
  for (const child of node?.children ?? []) { const f = find(child, id); if (f) return f; }
  return null;
}
function location() {
  const space = spaces().find(s => s.active), f = focused();
  const pane = f?.pane ? panes().find(p => p.pane === f.pane) : null;
  return { cwd: pane?.cwd || f?.cwd || space?.folder, on: space?.machine ?? null };
}
// Focus address of an agent's terminal: remote spaces name terminals "machine/tN". null when it is gone
// (ended, hc rm'd, or relaunched into a new terminal). shortcut: if panes() carries no terminal ids, trust a.hc.
function focusAddr(a) {
  if (!a.hc || a.status === "ended") return null;
  const addr = location().on ? `${location().on}/${a.hc}` : a.hc, ps = panes();
  return !ps.some(p => p.terminal) || ps.some(p => p.terminal === addr) ? addr : null;
}
const locKey = () => { const l = location(); return `${l.on}:${l.cwd}`; };
const ago = s => s == null ? "" : s >= 3600 ? `${Math.floor(s / 3600)}h${String(Math.floor(s % 3600 / 60)).padStart(2, "0")}m` : s >= 60 ? `${Math.floor(s / 60)}m` : `${Math.max(0, s)}s`;
const hhmm = ts => { const d = new Date(ts * 1000); return `${String(d.getHours()).padStart(2, "0")}:${String(d.getMinutes()).padStart(2, "0")}`; };
const iso = s => s ? Math.floor(Date.parse(s) / 1000) : 0;
const base = p => p ? p.split("/").filter(Boolean).pop() : "";
const kilo = n => n >= 1000 ? `${Math.round(n / 1000)}k` : String(n);
const plural = (n, w) => `${n} ${w}${n === 1 ? "" : "s"}`;
// One display line: first non-empty line (rows are fixed-height; a newline would overlap neighbours).
const one = x => String(x ?? "").split("\n").map(l => l.trim()).find(Boolean) ?? "";
// Push events carry branch and subject (state --json since #39); older ones only the shell command.
const pushBranch = e => {
  if (e.branch) return e.branch;
  const m = /git push([^\n;&|]*)/.exec(e.data ?? "");
  return m ? m[1].trim().split(/\s+/).filter(w => w && !w.startsWith("-")).pop() ?? "" : "";
};
// What an event says, as one line: { k: short kind, text, sub: dim tail, red }.
function evLine(e) {
  const d = one(e.data);
  switch (e.kind) {
    case "push": return { k: "push", text: `pushed ${pushBranch(e)}`.trim(), sub: one(e.subject) };
    case "claim": return { k: "claim", text: `claimed ${d}` };
    case "done": return { k: "done", text: `done ${d}` };
    case "task-add": return { k: "board", text: `added ${d}` };
    case "spawn": return { k: "spawn", text: `spawned ${d}` };
    case "end": return { k: "ended", text: d ? `ended · ${d}` : "ended" };
    case "ci-red": return { k: "CI", text: `main CI red${d ? ` · run ${d}` : ""}`, red: true };
    case "compact": return { k: "context", text: "compacted context" };
    case "heavy-start": return { k: "heavy", text: d };
    default: return { k: e.kind, text: [d, e.path].filter(Boolean).join(" "), red: RED.has(e.kind) };
  }
}
// Done-task evidence split into a chip (PR / no-op), a short sha and the rest.
function evidence(s) {
  s = one(s);
  const pr = /PR #(\d+)/.exec(s)?.[1], sha = /\b(?=[0-9]*[a-f])[0-9a-f]{7,40}\b/.exec(s)?.[0];
  const chip = pr ? `PR #${pr}` : /^no-?op/i.test(s) ? "no-op" : /already/i.test(s) ? "already fixed" : null;
  const rest = s.replace(/PR #\d+( merged)?:?\s*/, "").replace(sha ?? "\0", "").replace(/^[\s:;·,()-]+/, "").trim();
  return { chip, sha: sha?.slice(0, 8), rest };
}
// shortcut: wrapped-text height from an average glyph width; a real measure would need a layout pass.
const lines = (text, px, charW) => Math.max(1, Math.ceil(String(text ?? "").length * charW / Math.max(60, px)));
const openUrl = url => exec(window()?.platform === "macos" ? "open" : "xdg-open", [url]);

export default class Swarm extends View {
  init(_props, cx) {
    this.s = null; this.prs = null; this.runs = null; this.error = null;
    this.seen = new Set(); this.fresh = new Set(); this.delay = new Map(); this.open = {}; this.width = 860;
    this.tab = "overview"; this.sel = null; this.push = null; this.boardFilter = "all"; this.actFilter = "all";
    this.refresh(cx); this.copyIcons(cx);
    // Data timers only; each tick returns at once while the panel isn't shown or nothing is due.
    cx.timer.every(POLL, cx => { if (this.visible() && this.due()) this.refresh(cx); });
    cx.timer.every(PR_POLL, cx => { if (this.visible()) this.refreshPrs(cx); });
  }

  // svg() refuses a path that leaves Herdr's home, and mods/swarm is a symlink into the repo: copy the
  // icons to a real folder there. Until it lands (or if it fails) an icon is an empty box of its size.
  copyIcons(cx) {
    const src = `${appHome()}/mods/swarm/icons`, dst = `${appHome()}/swarm-icons`;
    cx.spawn(async cx => {
      const r = await exec("sh", ["-c", 'mkdir -p "$2" && cp -f "$1"/*.svg "$2"/', "sh", src, dst]).catch(() => null);
      if (r?.code === 0) { this.iconDir = "swarm-icons"; cx.notify(); }
    });
  }

  visible() {
    const root = layout(), body = find(root, "panel-body"), panel = find(root, "panel");
    if (!body?.children?.some(c => c.content?.mod === "swarm")) return true; // a pane or another layout: shown when alive
    return panel && !panel.hidden && body.active === "swarm";
  }

  // What the open view asks state --json for: the tab, and on Agents the agent in the detail pane.
  view() { return `${this.tab}:${this.tab === "agents" ? this.detailName ?? "" : ""}`; }
  due() {
    const age = Date.now() - (this.at ?? 0);
    return locKey() !== this.loc || this.view() !== this.polled || this.dirty
      || age > (this.on ? REMOTE_POLL : this.watching ? QUIET_POLL : POLL);
  }

  refresh(cx) {
    if (this.loading) return;
    const { cwd, on } = location();
    this.loc = locKey();
    if (!cwd) { this.s = null; this.error = "No folder"; return; }
    const view = this.view(), args = ["--view", this.tab, ...(this.tab === "agents" && this.detailName ? ["--agent", this.detailName] : [])];
    this.loading = true; this.at = Date.now(); this.dirty = false; this.polled = view;
    cx.spawn(async cx => {
      try {
        const r = await swarmState(cwd, on, args);
        if (r.code !== 0) throw new Error(r.stderr.trim() || `swarm exited ${r.code}`);
        const s = JSON.parse(r.stdout);
        const now = location();
        if (now.cwd !== cwd || now.on !== on) return; // moved to another folder meanwhile; the next render asks again
        const same = s.db === this.s?.db && on === this.on;
        if (!same) {
          if (this.s) { this.seen.clear(); this.sel = null; this.push = null; } // another repo: its agents, not the last one's
          this.prs = null; this.runs = null; this.prsAt = 0; this.cwd = cwd; this.on = on; this.refreshPrs(cx);
        }
        // A view sends only its sections; the others keep their last values (empty at first) until their tab asks.
        this.s = { messages: [], events: [], locks: [], ...(same ? this.s : null), ...s }; this.error = null;
        if (on) this.watching = null; else if (s.agents) this.watch(s.db.replace(/\/[^/]*$/, ""), cx);
      } catch (e) { this.error = String(e.message ?? e); }
      finally { this.loading = false; cx.notify(); }
    });
  }

  // Marks the data stale when the db folder changes; the POLL tick does the asking. Our own reads touch
  // only the -shm index, so those don't count.
  watch(dir, cx) {
    if (this.watching === dir) return;
    this.watching = dir;
    cx.spawn(async () => {
      try {
        while (this.watching === dir) if ((await watchFolder(dir)).some(p => !p.endsWith("-shm"))) this.dirty = true;
      } catch { if (this.watching === dir) this.watching = null; } // unwatchable: back to polling every POLL
    });
  }

  // CI runs feed the needs-you strip on every tab; PRs only show on Agents and System.
  refreshPrs(cx) {
    const cwd = this.cwd, on = this.on, prs = this.tab === "agents" || this.tab === "system";
    if (!cwd || this.prLoading) return;
    this.prLoading = true;
    cx.spawn(async cx => {
      try {
        if (prs) {
          const pr = await exec("gh", ["pr", "list", "--limit", "30", "--json", "number,title,headRefName,isDraft,reviewDecision,statusCheckRollup,url"], { cwd, on });
          this.prs = pr.code === 0 ? JSON.parse(pr.stdout) : null;
        }
        const ci = await exec("gh", ["run", "list", "--branch", "main", "--limit", "6", "--json", "databaseId,status,conclusion,displayTitle,createdAt,url"], { cwd, on });
        this.runs = ci.code === 0 ? JSON.parse(ci.stdout) : null;
      } catch { this.prs = null; this.runs = null; } // no gh: those parts just say so
      finally { this.prLoading = false; this.prAt = Date.now(); if (prs) this.prsAt = this.prAt; cx.notify(); }
    });
  }

  // ---- motion -------------------------------------------------------------------------------
  // A key first drawn this frame sits at its start value (transparent, offset, empty bar); a frame later
  // it moves to its target, staggered 35 ms by its order among new keys (max 12).
  enter(k, stagger = true) {
    const first = !this.seen.has(k);
    if (first && !this.fresh.has(k)) { this.delay.set(k, stagger ? Math.min(this.fresh.size, 12) * 35 : 0); this.fresh.add(k); }
    return { first, delay: this.delay.get(k) ?? 0 };
  }

  // Positioned list: rows sit at computed tops and slide (top/height transitions) when they move
  // between groups, re-sort or open; a row new to the panel fades in, staggered.
  list(id, rows) {
    let y = 0;
    const kids = rows.map(r => {
      const k = `${id}:${r.key}`, { first, delay } = this.enter(k);
      const el = div().id(k).absolute().left(0).w_full().top(y).h(r.h).overflow_hidden()
        .opacity(first ? 0 : 1).transition("opacity", { duration: 260, delay, easing: "ease-out" })
        .transition("top", { duration: 320, easing: "ease-in-out" }).transition("height", { duration: 220, easing: "ease-out" })
        .child(r.el);
      y += r.h;
      return el;
    });
    return div().id(`list-${id}`).relative().w_full().h(y).transition("height", { duration: 260, easing: "ease-out" }).children(kids);
  }

  // Switching tabs re-runs the staggered entrance of the new tab's rows (context bars fill only once).
  go(tab, cx, sel) {
    if (tab !== this.tab) { this.seen = new Set([...this.seen].filter(k => k.startsWith("bar:"))); this.delay.clear(); }
    this.tab = tab; this.push = null;
    if (sel !== undefined) this.sel = sel;
    cx.notify();
  }

  // ---- small parts --------------------------------------------------------------------------
  chip(t, text, color, fill) {
    return div().px(5).h(16).flex_none().flex().items_center().rounded(4).text_size(10).whitespace_nowrap().border_1()
      .border_color(fill ? color : color ? color + "66" : t.border).bg(fill ? color + "22" : t.background).text_color(color ?? t.muted).child(text);
  }
  dot(color, n = 8) { return div().size(n).rounded(n / 2).flex_none().bg(color); }
  k(t, text) { return div().text_size(10).text_color(t.dim).flex_none().child(text.toUpperCase()); }
  mono(el) { return el.font_family(settings().font_family ?? "JetBrains Mono"); }
  chev(t, dir) { return div().flex_none().text_size(11).text_color(t.dim).child({ right: "›", up: "⌃", down: "⌄" }[dir]); }
  btn(t, id, label, onClick) {
    return h_flex().id(id).h(24).px(10).gap(5).flex_none().items_center().rounded(6).border_1().border_color(t.border).bg(t.surface)
      .text_size(11).cursor_pointer().hover(s => s.bg(t.hover)).on_click((_e, cx) => { cx.stop_propagation(); onClick(cx); }).child(label);
  }
  card(t, id, red) {
    return v_flex().id(id).w_full().min_w(0).px(12).py(10).gap(7).rounded(8).bg(t.surface).border_1().border_color(red ? t.blocked + "88" : t.border);
  }
  sec(t, label, note, right) {
    return h_flex().h(26).px(4).pt(6).gap(6).items_center().min_w(0)
      .child(div().text_size(10.5).font_semibold().text_color(t.muted).flex_none().child(label.toUpperCase()))
      .when(Boolean(note), el => el.child(div().text_size(10.5).truncate().min_w(0).text_color(t.dim).child(note)))
      .child(div().flex_1()).when(Boolean(right), el => el.child(right));
  }
  link(t, id, text, onClick) {
    return div().id(id).flex_none().text_size(10.5).text_color(t.dim).cursor_pointer().hover(s => s.text_color(t.foreground))
      .on_click((_e, cx) => { cx.stop_propagation(); onClick(cx); }).child(text);
  }

  statusColor(t, s) { return { working: t.working, idle: t.idle, blocked: t.blocked, ended: t.dim }[s] ?? t.unknown; }
  statusText(t, a) {
    return div().text_size(10.5).flex_none().text_color(a.status === "idle" ? t.dim : this.statusColor(t, a.status))
      .child(a.status === "idle" ? `idle ${ago(a.idle_s)}` : a.status);
  }
  cacheChip(t, a, long) {
    if (a.status === "ended") return null;
    if (a.cold_guarded) return this.chip(t, "cold-guarded", t.ansi3, true);
    const left = a.cache === "warm" && a.cold_at ? a.cold_at - this.s.now : null;
    return a.cache === "warm" ? this.chip(t, `warm${long ? " cache" : ""}${left > 0 ? ` · ${ago(left)}` : ""}`, t.ansi2)
      : this.chip(t, long ? "cold cache" : "cold", t.ansi4);
  }
  lastEvent(a) {
    const e = a.events?.find(e => !QUIET.has(e.kind));
    if (!e) return "";
    const l = evLine(e);
    return `${l.text}${l.sub ? ` · ${l.sub}` : ""} · ${hhmm(e.ts)}`;
  }

  // Context bar on a 0..600k scale with ticks at the 350k finish note and the 550k hand-off; it fills
  // 0 -> value once per key (a lane, or the detail pane for one agent).
  ctxBar(t, key, n, big) {
    const pct = Math.min(100, (n / CTX_MAX) * 100), { first } = this.enter(`bar:${key}`, false), h = big ? 6 : 4;
    const tick = (at, color) => div().absolute().left(`${(at / CTX_MAX) * 100}%`).top(big ? -4 : -2).w(1).h(h + (big ? 8 : 4)).bg(color);
    return div().relative().flex_1().min_w(0).h(h).rounded(h / 2).bg(t.selected)
      .child(div().id(`bar:${key}`).absolute().left(0).top(0).h(h).rounded(h / 2).bg(n >= HANDOFF ? t.blocked : n >= FINISH ? t.ansi3 : t.ansi4)
        .w(first ? "0%" : `${pct}%`).transition("width", { duration: 400, easing: "ease-out" }))
      .child(tick(FINISH, t.dim)).child(tick(HANDOFF, t.blocked));
  }
  ctxLabels(t, n) {
    return div().relative().w_full().h(14).text_size(10.5).text_color(t.dim)
      .child(div().absolute().left(0).text_color(n ? t.foreground : t.dim).child(n ? kilo(n) : "0"))
      .child(div().absolute().left(`${(FINISH / CTX_MAX) * 100}%`).pl(4).child(this.width < 760 ? "350k" : "350k finish"))
      .child(div().absolute().right(`${(1 - HANDOFF / CTX_MAX) * 100}%`).pr(4).text_color(t.blocked).child(this.width < 760 ? "550k" : "550k hand off"));
  }

  // ---- derived data -------------------------------------------------------------------------
  derive() {
    const s = this.s;
    const comms = s.comms ?? null;
    const order = { blocked: 0, working: 1, idle: 2 };
    const live = s.agents.filter(a => a.status !== "ended" && a.name !== comms)
      .sort((a, b) => (order[a.status] ?? 3) - (order[b.status] ?? 3) || a.name.localeCompare(b.name));
    const ended = s.agents.filter(a => a.status === "ended" && a.name !== comms).sort((a, b) => (b.ended ?? 0) - (a.ended ?? 0));
    const count = st => s.tasks.filter(k => k.state === st).length;
    const done = (this.runs ?? []).filter(r => r.status === "completed");
    let reds = 0;
    while (reds < done.length && done[reds].conclusion === "failure") reds++;
    // shortcut: the CI fixer is the claimed task that mentions red/CI; a ci-red -> task link in the db would be exact.
    const fix = s.tasks.find(k => (k.state === "claimed" || k.state === "blocked") && /\b(red|ci)\b/i.test(k.title));
    const told = id => s.messages.filter(m => m.kind === "system" && m.body.startsWith(`main CI is red (run ${id}`)).length;
    return { comms, commsAgent: s.agents.find(a => a.name === comms), live, ended, count, reds, redRuns: done.slice(0, reds), fix, told };
  }

  // What needs the user, most urgent first: a red main, a blocked task, an agent stuck on a prompt.
  needs(t, d) {
    const s = this.s, out = [];
    if (d.reds) {
      const r = d.redRuns[0], heavy = d.fix && s.agents.find(a => a.name === d.fix.owner)?.events?.find(e => e.kind === "heavy-start");
      out.push({ key: "ci", title: "main CI red", go: "system",
        detail: `run ${r.databaseId} · ${hhmm(iso(r.createdAt))}${d.reds > 1 ? ` · ${d.reds} red runs since ${hhmm(iso(d.redRuns[d.reds - 1].createdAt))}` : ""}`,
        short: hhmm(iso(r.createdAt)), owner: d.fix ? `${d.fix.owner} is on it (#${d.fix.id})` : "nobody on it", heavy: heavy ? `heavy run ${hhmm(heavy.ts)}` : null });
    }
    for (const k of s.tasks.filter(k => k.state === "blocked"))
      out.push({ key: `t${k.id}`, title: `#${k.id} blocked`, detail: one(k.question) || k.title, short: "", owner: k.owner, go: "board" });
    for (const a of d.live.filter(a => a.status === "blocked" && !s.tasks.some(k => k.state === "blocked" && k.owner === a.name)))
      out.push({ key: `a${a.name}`, title: `${a.name} is blocked`, detail: "a prompt or question needs you", short: "", owner: "", go: "agents", sel: a.name });
    return out;
  }

  // Needs-you strip: on every tab while something needs the user; its height eases 0 <-> 40.
  strip(t, d) {
    const n = this.needs(t, d), x = n[0], narrow = this.width < 520;
    return div().id("needs").flex_none().mx(12).h(x ? 50 : 0).pt(x ? 10 : 0).overflow_hidden().transition("height", { duration: 220, easing: "ease-out" })
      .when(Boolean(x), el => el.child(h_flex().id(`needs-${x.key}`).h(40).px(12).gap(10).items_center().min_w(0).rounded(8)
        .border_1().border_color(t.blocked + "88").bg(t.blocked + "14").cursor_pointer().hover(s => s.bg(t.blocked + "1f"))
        .on_click((_e, cx) => this.go(x.go, cx, x.sel))
        .child(this.dot(t.blocked)).child(div().flex_none().text_size(12).font_semibold().text_color(t.blocked).child(x.title))
        .when(!narrow, el => el.child(div().min_w(0).flex_shrink(1).truncate().text_size(10.5).text_color(t.dim).child(x.detail)))
        .child(div().flex_1().min_w(0).truncate().text_size(10.5).text_color(t.muted).child(x.owner ?? ""))
        .when(!narrow && Boolean(x.heavy), el => el.child(this.chip(t, x.heavy, t.ansi3, true)))
        .when(narrow && Boolean(x.short), el => el.child(div().flex_none().text_size(10.5).text_color(t.dim).child(x.short)))
        .when(n.length > 1, el => el.child(this.chip(t, `+${n.length - 1}`, t.blocked)))
        .child(this.chev(t, "right"))));
  }

  nav(t, d) {
    const s = this.s, narrow = this.width < 520, tiny = this.width <= 340;
    const active = d.count("blocked") + d.count("claimed") + d.count("open");
    const alert = d.reds > 0 || s.conflicts.length > 0 || s.pressure.some(p => !p.end) || s.machine?.high;
    const counts = { agents: d.live.length, board: active };
    let x = 3;
    const segs = TABS.map(([id, label, w]) => {
      const n = counts[id], width = w + (tiny ? 10 : narrow ? 18 : 24) + (!tiny && n ? 8 + String(n).length * 6 : 0) + (id === "system" && alert ? 12 : 0);
      const seg = { id, label, n, left: x, width };
      x += width + 2;
      return seg;
    });
    const on = segs.find(g => g.id === this.tab) ?? segs[0];
    const below = this.tab === "activity" || (this.tab === "board" && this.width < 760); // filters get their own row
    const right = this.tab === "overview" ? div().text_size(10.5).text_color(t.dim).child(this.at ? `updated ${hhmm(this.at / 1000)}` : "")
      : this.tab === "agents" ? div().text_size(10.5).text_color(t.dim).child("blocked, working, then idle")
      : this.tab === "system" ? div().text_size(10.5).text_color(t.dim).child(this.prAt ? `polled ${hhmm(this.prAt / 1000)}` : "")
      : this.filters(t, d);
    const seg = div().relative().flex_none().h(30).w(x + 3).rounded(8).bg(t.surface).border_1().border_color(t.border)
      .child(div().id("seg-on").absolute().top(2).left(on.left).w(on.width).h(24).rounded(5).bg(t.selected)
        .transition("left", { duration: 180, easing: "ease-out" }).transition("width", { duration: 180, easing: "ease-out" }))
      .children(segs.map(g => h_flex().id(`tab-${g.id}`).absolute().top(2).left(g.left).w(g.width).h(24).gap(6).justify_center().items_center().rounded(5)
        .text_size(11.5).cursor_pointer().text_color(g.id === this.tab ? t.foreground : t.muted).when(g.id === this.tab, el => el.font_semibold())
        .hover(st => st.text_color(t.foreground)).on_click((_e, cx) => this.go(g.id, cx))
        .child(g.label)
        .when(!tiny && Boolean(g.n), el => el.child(div().text_size(10).font_normal().text_color(t.dim).child(String(g.n))))
        .when(g.id === "system" && Boolean(alert), el => el.child(this.dot(t.blocked, 6)))));
    return v_flex().flex_none().mx(12).mt(10).gap(8)
      .child(h_flex().gap(10).items_center().min_w(0).child(seg).child(div().flex_1()).when(!below && !narrow, el => el.child(right)))
      .when(below, el => el.child(this.filters(t, d)));
  }

  filters(t, d) {
    const s = this.s, board = this.tab === "board";
    const opts = board
      ? [["all", "All", s.tasks.length], ["active", "Active", d.count("blocked") + d.count("claimed") + d.count("open")], ["done", "Done", d.count("done")], ["dropped", "Dropped", d.count("dropped")]]
      : [["all", "All"], ["you", "Needs you", this.actRows(t, d, "you").length], ["tasks", "Tasks"], ["code", "Code"], ["agents", "Agents"], ["messages", "Messages"], ["machine", "Machine"]];
    const cur = board ? this.boardFilter : this.actFilter;
    // Activity: Summary | Full log first, the filters, then the key's toggle at the end.
    const view = (id, label, log, tip) => div().id(id).h(20).px(8).flex().items_center().rounded(3).text_size(11).cursor_pointer().tooltip(tip)
      .bg(Boolean(this.actLog) === log ? t.selected : t.background).text_color(Boolean(this.actLog) === log ? t.foreground : t.muted)
      .hover(st => st.bg(t.hover)).on_click((_e, cx) => { this.actLog = log; cx.notify(); }).child(label);
    return h_flex().gap(4).items_center().flex_wrap()
      .when(!board, el => el.child(h_flex().flex_none().mr(6).p(1).gap(1).rounded(5).border_1().border_color(t.border)
        .child(view("v-sum", "Summary", false, "What happened, in plain words. Routine events are left to the full log."))
        .child(view("v-log", "Full log", true, "Every event and message, with its raw kind. Nothing folded or hidden."))))
      .children(opts.map(([id, label, n]) => h_flex().id(`f-${id}`).h(22).px(9).gap(5).items_center().rounded(4).border_1().border_color(t.border)
        .bg(id === cur ? t.selected : t.background).text_size(11).text_color(id === cur ? t.foreground : t.muted).cursor_pointer().hover(st => st.bg(t.hover))
        .on_click((_e, cx) => { if (board) this.boardFilter = id; else this.actFilter = id; cx.notify(); })
        .child(board ? `${label} ${n}` : label).when(!board && n != null && n > 0, el => el.child(div().text_size(10).text_color(id === "you" ? t.blocked : t.dim).child(String(n))))))
      .when(!board, el => el.child(div().flex_1()).child(this.link(t, "key-toggle", this.open.key ? "Hide key" : "What these mean", cx => { this.open.key = !this.open.key; cx.notify(); }).pl(8)));
  }

  // ---- lanes (Overview, Agents) -------------------------------------------------------------
  // A lane: status line, task, last event, context bar. Heights are fixed so the list can slide them;
  // `open` (narrow only) unfolds the detail inline, `compact` (640) drops the model chip and last event.
  lane(t, a, { sel, open, compact, onClick, prefix }) {
    const narrow = this.width < 520;
    const r3 = !compact && !open && Boolean(a.events?.length);
    const r4 = a.ctx_tokens > 0 && !open;
    let h = 20 + 18 + 5 + 16 + (r3 ? 5 + 14 : 0) + (r4 ? 5 + 8 : 0);
    const branch = a.branch ?? (a.worktree ? base(a.worktree) : null);
    const push = a.events?.find(e => e.kind === "push");
    const files = a.files.slice(0, 4), latest = (a.events ?? []).slice(0, 4);
    const task = open && a.task && this.s.tasks.find(k => k.id === a.task.id);
    if (open) h += 6 + (task ? 5 + 16 : 0) + (a.ctx_tokens ? 5 + 6 + 5 + 14 : 0) + 8 + 14 + 3 + 18 + (files.length ? 7 + 14 + 3 + files.length * 18 : 0) + (latest.length ? 7 + 14 + 3 + latest.length * 20 : 0) + 8 + 24;
    const el = v_flex().id(`${prefix}-${a.name}`).mb(6).h(h - 6).px(10).py(9).gap(5).rounded(8).overflow_hidden()
      .bg(sel || open ? t.hover : t.surface).border_1().border_color(a.status === "blocked" ? t.blocked : sel || open ? t.input : t.border)
      .cursor_pointer().hover(s => s.bg(t.hover)).on_click((_e, cx) => onClick(cx))
      .child(h_flex().h(18).flex_none().gap(6).items_center().min_w(0)
        .child(this.dot(this.statusColor(t, a.status)).when(a.status === "working", el => el.loop("opacity", { from: 0.35, to: 1, period: 1400 })))
        .child(div().font_semibold().text_size(12.5).flex_none().child(a.name))
        .child(this.statusText(t, a)).child(div().flex_1())
        .when(!compact && Boolean(a.model), el => el.child(this.chip(t, a.model)))
        .child(this.cacheChip(t, a) ?? div())
        .when(narrow, el => el.child(this.chev(t, open ? "up" : "down"))))
      .child(div().h(16).flex_none().text_size(11.5).truncate().text_color(a.task ? t.foreground : t.dim)
        .child(a.task ? `#${a.task.id} ${a.task.title}` : `no task${a.files.length ? ` · ${plural(a.files.length, "file")} edited` : ""}`))
      .when(r3, el => el.child(div().h(14).flex_none().text_size(10.5).truncate().text_color(t.dim).child(this.lastEvent(a))))
      .when(r4, el => el.child(h_flex().h(8).flex_none().gap(6).items_center().child(this.ctxBar(t, `${prefix}-${a.name}`, a.ctx_tokens))
        .child(div().w(34).flex_none().text_size(10.5).text_color(t.dim).text_right().child(kilo(a.ctx_tokens)))));
    if (open) {
      el.child(v_flex().flex_none().gap(5).pt(1)
        .when(Boolean(task), el => el.child(h_flex().h(16).gap(6).items_center().text_size(10.5).text_color(t.dim)
          .child(this.chip(t, task.state, task.state === "blocked" ? t.blocked : t.ansi3, true))
          .child(task.lease_left != null ? (task.lease_left > 0 ? `lease ${ago(task.lease_left)} left` : "lease expired") : "")))
        .when(a.ctx_tokens > 0, el => el.child(v_flex().gap(5).pt(5).child(h_flex().h(6).child(this.ctxBar(t, `open-${a.name}`, a.ctx_tokens, true))).child(this.ctxLabels(t, a.ctx_tokens)))))
        .child(v_flex().flex_none().mt(2).pt(7).border_t(1).border_color(t.border).gap(0)
          .child(div().h(14).mb(3).child(this.k(t, "Branch")))
          .child(h_flex().h(18).gap(6).items_center().text_size(11).min_w(0)
            .child(this.mono(div().truncate().min_w(0).child(branch ?? "main")))
            .child(div().flex_1()).child(div().flex_none().text_color(t.dim).child(push ? `pushed ${hhmm(push.ts)}` : "")))
          .when(files.length > 0, el => el.child(div().h(14).mt(7).mb(3).child(this.k(t, `Files · ${a.files.length}`)))
            .children(files.map(f => this.fileRow(t, f))))
          .when(latest.length > 0, el => el.child(div().h(14).mt(7).mb(3).child(this.k(t, "Latest")))
            .children(latest.map(e => { const l = evLine(e); return h_flex().h(20).gap(8).text_size(11).min_w(0)
              .child(div().w(34).flex_none().text_color(t.dim).child(hhmm(e.ts))).child(div().flex_1().min_w(0).truncate().text_color(l.red ? t.blocked : t.muted).child(l.text)); })))
          .child(h_flex().mt(8).h(24).gap(6)
            .child(this.btn(t, `push-${a.name}`, "Open agent", cx => { this.push = a.name; cx.notify(); }))
            .when(Boolean(focusAddr(a)), el => el.child(this.btn(t, `focus2-${a.name}`, "Focus terminal ↗", () => run("agent.focus", { terminal: focusAddr(a) }))))));
    }
    return { key: a.name, h, el };
  }

  fileRow(t, f) {
    const i = f.lastIndexOf("/") + 1;
    return this.mono(h_flex().h(18).min_w(0).text_size(10.5).truncate()
      .child(div().flex_none().text_color(t.dim).child(f.slice(0, i))).child(div().truncate().min_w(0).text_color(t.muted).child(f.slice(i))));
  }

  endRow(t, a) {
    const el = h_flex().h(24).px(4).gap(6).items_center().rounded(5).text_size(11).min_w(0).hover(s => s.bg(t.surface))
      .child(this.dot(t.dim, 6)).child(div().flex_none().text_color(t.muted).child(a.name))
      .child(div().truncate().min_w(0).text_size(10.5).text_color(t.dim).child([a.model, a.ended ? hhmm(a.ended) : null].filter(Boolean).join(" · ")))
      .child(div().flex_1())
      .child(div().flex_none().text_size(10.5).text_color(a.ctx_tokens >= FINISH ? t.ansi3 : t.dim).child(a.ctx_tokens ? kilo(a.ctx_tokens) : ""));
    return { key: `end-${a.name}`, h: 24, el };
  }

  // ---- Agents tab ---------------------------------------------------------------------------
  commsRow(t, d, onClick, selected) {
    const c = d.commsAgent;
    return h_flex().id("comms-row").flex_none().h(34).px(10).gap(8).items_center().min_w(0).rounded(8)
      .bg(selected ? t.hover : t.surface).border_1().border_color(selected ? t.input : t.border).cursor_pointer().hover(s => s.bg(t.hover))
      .on_click((_e, cx) => onClick(cx))
      .child(this.k(t, "Comms")).child(div().flex_none().font_semibold().text_size(12.5).child(d.comms))
      .child(div().flex_1().min_w(0).truncate().text_size(10.5).text_color(t.dim)
        .child([c?.worktree ? `⎇ ${base(c.worktree)}` : "main checkout", c && this.width >= 520 ? this.lastEvent(c) : null].filter(Boolean).join(" · ")));
  }

  // Wide: lanes | selected agent (master-detail). Narrow: lanes open inline; Open agent pushes the detail.
  agents(t, d) {
    const narrow = this.width < 520;
    if (narrow) this.detailName = this.push;
    if (narrow && this.push) {
      const a = this.s.agents.find(x => x.name === this.push);
      if (a) {
        const { first } = this.enter(`push:${a.name}`, false);
        return v_flex().id(`pushed-${a.name}`).relative().w_full().gap(8).p(10)
          .left(first ? 24 : 0).opacity(first ? 0 : 1).transition("left", { duration: 200, easing: "ease-out" }).transition("opacity", { duration: 200, easing: "ease-out" })
          .child(h_flex().child(this.btn(t, "back", "‹ Agents", cx => { this.push = null; this.seen.delete(`push:${a.name}`); cx.notify(); })))
          .child(this.detail(t, d, a));
      }
    }
    const showEnded = this.open.ended ? d.ended : d.ended.slice(0, 10);
    const pick = name => cx => {
      if (narrow) this.open[`lane:${name}`] = !this.open[`lane:${name}`];
      else { this.sel = name; this.seen.delete(`det:${name}`); this.seen.delete(`bar:det-${name}`); } // crossfade + refill
      cx.notify();
    };
    const sel = narrow ? null : (this.sel && this.s.agents.some(a => a.name === this.sel) ? this.sel : d.live[0]?.name ?? d.comms ?? d.ended[0]?.name);
    const master = v_flex().w_full().gap(0).min_w(0)
      .when(Boolean(d.comms), el => el.child(this.commsRow(t, d, pick(d.comms), sel === d.comms)))
      .child(this.sec(t, "Live", String(d.live.length)))
      .child(this.list("lanes", d.live.map(a => this.lane(t, a, { prefix: "lane", sel: sel === a.name, open: narrow && this.open[`lane:${a.name}`], compact: this.width < 760 && !narrow, onClick: pick(a.name) }))))
      .when(d.ended.length > 0, el => el
        .child(this.sec(t, "Ended", `${d.ended.length} · newest first`, this.width >= 520 ? div().text_size(10.5).text_color(t.dim).child("at end") : null))
        .child(this.list("ended", showEnded.map(a => this.endRow(t, a))))
        .when(d.ended.length > 10, el => el.child(this.link(t, "ended-more", this.open.ended ? "Show fewer" : `Show all ${d.ended.length}`, cx => { this.open.ended = !this.open.ended; cx.notify(); }).px(4).py(6))));
    if (narrow) return div().p(10).child(master);
    this.detailName = sel; // the next poll brings its messages
    const a = this.s.agents.find(x => x.name === sel);
    return h_flex().id("agents-md").size_full().min_h(0).p(12).gap(14).items_start()
      .child(v_flex().id("agents-list").w(this.width >= 760 ? 316 : 260).flex_none().h_full().min_h(0).overflow_y_scrollbar().child(master))
      .child(v_flex().id("agents-det").flex_1().min_w(0).h_full().min_h(0).overflow_y_scrollbar().when(Boolean(a), el => el.child(this.detail(t, d, a))));
  }

  detail(t, d, a) {
    const s = this.s, isComms = a.name === d.comms, { first } = this.enter(`det:${a.name}`, false);
    const task = a.task && s.tasks.find(k => k.id === a.task.id);
    const branch = a.branch ?? (a.worktree ? base(a.worktree) : isComms ? "main" : null);
    const pr = branch && this.prs?.find(p => p.headRefName === branch);
    const push = a.events?.find(e => e.kind === "push");
    const n = a.ctx_tokens;
    const msgs = (a.messages ?? []).slice(0, 6), tl = (a.events ?? []).slice(0, 10);
    const lastDone = s.tasks.filter(k => k.state === "done" && k.owner === a.name).pop();
    const section = (label, note) => h_flex().gap(8).items_center().child(this.k(t, label)).when(Boolean(note), el => el.child(div().text_size(10.5).text_color(t.dim).child(note)));
    return v_flex().id(`det-${a.name}`).relative().w_full().min_w(0).px(16).py(14).gap(14).rounded(10).bg(t.surface).border_1().border_color(t.border)
      .top(first ? 4 : 0).opacity(first ? 0 : 1).transition("top", { duration: 160, easing: "ease-out" }).transition("opacity", { duration: 160, easing: "ease-out" })
      .child(v_flex().gap(4)
        .child(h_flex().gap(8).items_center().min_w(0)
          .child(this.dot(this.statusColor(t, a.status), 10).when(a.status === "working", el => el.loop("opacity", { from: 0.35, to: 1, period: 1400 })))
          .child(div().flex_none().text_size(17).font_semibold().child(a.name))
          .when(!isComms, el => el.child(div().flex_none().text_color(t.muted).child(a.status === "idle" ? `idle ${ago(a.idle_s)}` : a.status)))
          .when(Boolean(a.model), el => el.child(this.chip(t, a.model)))
          .when(!isComms, el => el.child(this.cacheChip(t, a, true) ?? div()))
          .child(div().flex_1())
          .when(Boolean(focusAddr(a)), el => el.child(this.btn(t, `focus-${a.name}`, this.width < 760 && this.width >= 520 ? "↗" : "Focus terminal ↗", () => run("agent.focus", { terminal: focusAddr(a) })))))
        .child(div().pl(18).text_size(10.5).text_color(t.dim).whitespace_normal()
          .child([isComms ? "the comms" : null, a.started ? `started ${hhmm(a.started)}` : null, a.ended ? `ended ${hhmm(a.ended)}` : null, a.hc ? `terminal ${a.hc}` : null,
            isComms ? "no idle or cache timer: it only sees swarm activity" : null].filter(Boolean).join(" · "))))
      .child(task
        ? v_flex().gap(5).px(12).py(10).rounded(8).bg(t.background).border_1().border_color(task.state === "blocked" ? t.blocked + "88" : t.border)
          .child(h_flex().gap(6).items_center().text_size(10.5).text_color(t.dim)
            .child(this.chip(t, task.state, task.state === "blocked" ? t.blocked : t.ansi3, true)).child(`#${task.id}`).child(div().flex_1())
            .child(task.lease_left != null ? (task.lease_left > 0 ? `lease ${ago(task.lease_left)} left` : "lease expired") : ""))
          .child(div().text_size(13).line_height("18px").whitespace_normal().child(task.title))
          .when(task.state === "blocked" && Boolean(task.question), el => el.child(div().text_size(11.5).text_color(t.blocked).whitespace_normal().child(`? ${one(task.question)}`)))
        : h_flex().h(34).px(10).items_center().rounded(7).border_1().border_dashed().border_color(t.border).text_size(11.5).text_color(t.dim)
          .child(isComms ? "No task. The communicator works from the main checkout." : `No task.${lastDone ? ` Last done #${lastDone.id}.` : ""}`))
      .child(v_flex().gap(7)
        .child(h_flex().gap(8).items_end().child(this.k(t, "Context")).child(div().text_size(15).font_semibold().child(n ? kilo(n) : "–"))
          .child(div().text_size(10.5).text_color(t.dim).child(!n ? "no reading for this session" : n >= HANDOFF ? "past the 550k hand-off" : n >= FINISH ? "past the 350k finish note" : "of the 350k finish note")))
        .when(n > 0, el => el.child(h_flex().h(6).child(this.ctxBar(t, `det-${a.name}`, n, true))).child(this.ctxLabels(t, 0))))
      .child(v_flex().gap(4)
        .child(section("Branch and PR"))
        .child(h_flex().h(22).gap(8).items_center().text_size(11.5).min_w(0)
          .child(div().flex_none().text_color(t.dim).child("⎇")).child(this.mono(div().flex_none().text_size(11).child(branch ?? "–")))
          .child(div().truncate().min_w(0).text_color(t.dim).child(a.worktree ? "worktree" : "checkout")).child(div().flex_1())
          .child(div().flex_none().text_color(t.dim).child(push ? `pushed ${hhmm(push.ts)}${push.subject ? ` · ${one(push.subject)}` : ""}` : "")))
        .child(pr ? this.prRow(t, pr, false)
          : div().h(22).text_size(11.5).text_color(t.dim).child(this.prs == null ? (this.prLoading ? "…" : "PRs unknown (gh not available)") : "No open PR from this branch")))
      .when(a.files.length > 0, el => el.child(v_flex().gap(0).child(h_flex().pb(4).child(section("Files", String(a.files.length)))).children(a.files.slice(0, 12).map(f => this.fileRow(t, f)))))
      .when(msgs.length > 0, el => el.child(v_flex().gap(3).child(section("Messages", "first line only"))
        .children(msgs.map(m => v_flex().gap(3).px(8).py(6).rounded(6).when(Boolean(m.urgent), el => el.bg(t.blocked + "14"))
          .child(h_flex().gap(6).items_center().text_size(10.5)
            .child(div().w(34).flex_none().text_color(t.dim).child(hhmm(m.ts)))
            .child(div().flex_none().text_color(t.muted).child(m.frm === a.name ? `→ ${m.dest === "all" ? "@all" : m.dest}` : `${m.frm} →`))
            .when(Boolean(m.urgent), el => el.child(this.chip(t, "urgent", t.blocked, true)))
            .when(!m.urgent && m.kind !== "dm", el => el.child(this.chip(t, m.kind))))
          .child(div().pl(40).h(16).truncate().text_size(11.5).child(one(m.body)))))))
      .when(tl.length > 0, el => el.child(v_flex().gap(0).child(h_flex().pb(3).child(section("Timeline")))
        .children(tl.map(e => { const l = evLine(e); return h_flex().h(22).gap(8).items_center().text_size(11).min_w(0)
          .child(div().w(34).flex_none().text_color(t.dim).child(hhmm(e.ts)))
          .child(div().w(52).flex_none().truncate().text_color(t.dim).child(l.k))
          .child(div().flex_1().min_w(0).truncate().text_color(l.red ? t.blocked : t.muted).child(`${l.text}${l.sub ? ` · ${l.sub}` : ""}`)); }))));
  }

  // ---- Board tab ----------------------------------------------------------------------------
  boardRows(t, d) {
    const s = this.s, narrow = this.width < 520, f = this.boardFilter, rows = [];
    const by = st => s.tasks.filter(k => k.state === st);
    const head = (key, label, color, n, note) => ({ key, h: 30, el: h_flex().h(30).pt(4).gap(6).items_center().child(this.dot(color, 6)).child(this.sec(t, label, note ? `${n} · ${note}` : String(n)).px(0).pt(0).flex_1()) });
    const big = k => {
      const blocked = k.state === "blocked", c = blocked ? t.blocked : k.state === "claimed" ? t.ansi3 : t.muted;
      const after = k.waiting ? k.deps.filter(i => s.tasks.find(x => x.id === i)?.state !== "done") : [];
      const dim = blocked ? t.blocked : t.dim;
      // #N in a subline is a link: it highlights that task's row (shortcut: a plain scroll div has no scroll-to, so a row off screen isn't scrolled into view).
      const refs = (label, ids) => h_flex().flex_none().gap(4).child(label).children(ids.map(i => div().id(`ref-${k.id}-${label}-${i}`).cursor_pointer().hover(st => st.text_color(t.foreground))
        .on_click((_e, cx) => { cx.stop_propagation(); this.hl = i; if (!s.tasks.some(x => x.id === i && ["open", "claimed", "blocked"].includes(x.state))) this.boardFilter = "all"; cx.notify(); }).child(`#${i}`)));
      const sub = h_flex().gap(6).min_w(0).overflow_hidden().text_size(10.5).text_color(dim)
        .when(blocked, el => el.child(div().truncate().min_w(0).child(`? ${one(k.question)}`)))
        .when(after.length > 0, el => el.child(refs("after", after)))
        .when(k.blocks?.length > 0, el => el.child(refs("blocks", k.blocks)))
        .child(div().truncate().min_w(0).child([blocked ? null : `added by ${k.created_by ?? "?"}`, blocked ? null : k.model].filter(Boolean).join(" · ")));
      const el = h_flex().id(`task-${k.id}`).h(52).px(12).gap(12).items_center().min_w(0).rounded(7).bg(blocked ? t.blocked + "14" : this.hl === k.id ? t.selected : t.surface)
        .border_1().border_color(blocked ? t.blocked + "66" : this.hl === k.id ? t.input : t.border).opacity(k.waiting ? 0.6 : 1)
        .when(Boolean(k.owner), el => el.cursor_pointer().hover(st => st.bg(t.hover)).on_click((_e, cx) => this.go("agents", cx, k.owner)))
        .child(div().w(2).h(30).rounded(1).flex_none().bg(c))
        .child(v_flex().flex_1().min_w(0).gap(3)
          .child(h_flex().gap(6).min_w(0).child(div().flex_none().text_size(11).text_color(t.dim).child(`#${k.id}`)).child(div().flex_1().min_w(0).truncate().text_size(12.5).child(k.title)))
          .child(sub))
        .when(Boolean(k.owner), el => el.child(v_flex().flex_none().items_end().gap(3)
          .child(div().font_semibold().text_size(12).child(k.owner))
          .child(div().text_size(10.5).text_color(t.dim).child(k.lease_left != null ? (k.lease_left > 0 ? `lease ${ago(k.lease_left)} left` : "lease expired") : ""))))
        .when(Boolean(k.owner), el => el.child(this.chev(t, "right")));
      return { key: `t${k.id}`, h: 58, el: div().pb(6).child(el) };
    };
    if (f === "all" || f === "active") {
      const blocked = by("blocked"), claimed = by("claimed"), open = by("open");
      const ready = open.filter(k => !k.waiting), waiting = open.filter(k => k.waiting);
      for (const [st, ks, c] of [["blocked", blocked, t.blocked], ["claimed", claimed, t.ansi3], ["ready", ready, t.muted], ["waiting", waiting, t.dim]]) {
        if (!ks.length) continue;
        rows.push(head(`h-${st}`, st, c, ks.length));
        for (const k of ks) rows.push(big(k));
      }
      const none = [["blocked", blocked, t.blocked], ["open", open, t.muted]].filter(([, ks]) => !ks.length);
      if (none.length) rows.push({ key: "h-none", h: 30, el: h_flex().h(30).px(4).gap(16).items_center().min_w(0)
        .children(none.map(([st, , c]) => h_flex().flex_none().gap(6).items_center().child(this.dot(c, 6)).child(div().text_size(10.5).font_semibold().text_color(t.muted).child(st.toUpperCase())).child(div().text_size(10.5).text_color(t.dim).child("0"))))
        .when(!narrow, el => el.child(div().truncate().min_w(0).text_size(10.5).text_color(t.dim).child(`Nothing ${none.map(([st]) => st).join(" or ")}.${none.some(([st]) => st === "blocked") ? " A blocked task shows first, with its question." : ""}`))) });
    }
    if (f === "all" || f === "done") {
      const done = by("done").reverse(), shown = this.open.done ? done : done.slice(0, f === "done" ? 40 : 15);
      rows.push(head("h-done", "done", t.ansi2, done.length, narrow ? "newest first" : "newest first · click a row for its full evidence"));
      if (!narrow) rows.push({ key: "th", h: 24, el: this.doneGrid(t, h_flex().h(24).text_size(10).text_color(t.dim), ["#", "TASK", "AGENT", "EVIDENCE"].map(x => div().child(x))) });
      for (const k of shown) rows.push(this.doneRow(t, k));
      if (shown.length < done.length) rows.push({ key: "done-more", h: 30, el: this.link(t, "done-more", `Show ${done.length - shown.length} more done`, cx => { this.open.done = true; cx.notify(); }).px(10).py(8) });
    }
    if (f === "all" || f === "dropped") {
      const dropped = by("dropped").reverse();
      if (dropped.length) {
        const show = f === "dropped" || this.open.dropped;
        rows.push({ key: "h-dropped", h: 40, el: h_flex().h(36).mt(4).pt(8).px(4).gap(8).items_center().min_w(0).border_t(1).border_color(t.border)
          .child(this.dot(t.dim, 6)).child(div().flex_none().text_size(10.5).font_semibold().text_color(t.muted).child("DROPPED")).child(div().flex_none().text_size(10.5).text_color(t.dim).child(String(dropped.length)))
          .child(this.mono(div().truncate().min_w(0).text_size(10.5).text_color(t.dim).child(dropped.map(k => `#${k.id}`).join(" "))))
          .child(div().flex_1())
          .when(f !== "dropped", el => el.child(this.link(t, "dropped-toggle", show ? "Hide" : "Show", cx => { this.open.dropped = !show; cx.notify(); }))) });
        if (show) for (const k of dropped) rows.push(this.doneRow(t, k));
      }
    }
    if (!rows.length) rows.push({ key: "none", h: 30, el: div().px(4).py(8).text_size(11).text_color(t.dim).child("No tasks") });
    return rows;
  }

  // Done table: # | task | agent | evidence at 860; 640 drops the agent column and the evidence text.
  doneGrid(t, row, cells) {
    const W = this.width, wide = W >= 760, narrow = W < 520;
    const [id, title, agent, ev] = cells;
    return row.px(10).gap(12).items_center().min_w(0)
      .child(div().w(40).flex_none().child(id)).child(div().flex_1().min_w(0).child(title))
      .when(wide, el => el.child(div().w(64).flex_none().min_w(0).child(agent)))
      .when(!narrow, el => el.child(div().w(wide ? 280 : 130).flex_none().min_w(0).child(ev)));
  }

  doneRow(t, k) {
    const W = this.width, wide = W >= 760, narrow = W < 520, key = `b:${k.id}`, open = this.open[key];
    const e = evidence(k.evidence), dropped = k.state === "dropped";
    const toggle = (_e, cx) => { this.open[key] = !open; cx.notify(); };
    const evCell = h_flex().gap(6).items_center().min_w(0)
      .when(Boolean(e.chip), el => el.child(this.chip(t, e.chip, e.chip.startsWith("PR") ? t.ansi2 : null)))
      .when(Boolean(e.sha), el => el.child(this.mono(div().flex_none().text_size(10.5).text_color(t.dim).child(e.sha))))
      .when(wide && Boolean(e.rest), el => el.child(div().truncate().min_w(0).text_size(10.5).text_color(t.dim).child(e.rest)));
    if (narrow) {
      const h = open ? 16 + lines(k.title, W - 60, 6.1) * 16 + 4 + lines(k.evidence, W - 60, 5.6) * 15 + 4 + 14 : 42;
      const el = v_flex().id(`d-${k.id}`).h(h - 4).px(10).py(6).gap(2).rounded(6).min_w(0).cursor_pointer().hover(s => s.bg(t.surface))
        .when(open, el => el.bg(t.surface).border_1().border_color(t.border)).on_click(toggle)
        .child(h_flex().gap(6).min_w(0).child(div().flex_none().text_size(10.5).text_color(t.dim).child(`#${k.id}`))
          .child(div().flex_1().min_w(0).text_size(11.5).text_color(dropped ? t.muted : t.foreground).when(open, el => el.whitespace_normal().line_height("16px")).when(!open, el => el.truncate()).child(k.title)))
        .when(!open, el => el.child(h_flex().gap(6).min_w(0).text_size(10.5).text_color(t.dim).child(div().flex_none().child(k.owner ?? "")).child(evCell)))
        .when(open, el => el.child(div().text_size(10.5).line_height("15px").whitespace_normal().text_color(t.dim).child(one(k.evidence) || "no evidence"))
          .child(div().text_size(10.5).text_color(t.dim).child([k.owner, `added by ${k.created_by ?? "?"}`].filter(Boolean).join(" · "))));
      return { key: `d${k.id}`, h, el };
    }
    const titleW = W - 24 - 20 - 40 - (wide ? 64 + 280 + 36 : 130 + 24);
    const h = open ? 18 + lines(k.title, titleW, 6.1) * 16 + 5 + lines(k.evidence, titleW, 5.6) * 15 + 5 + 14 + 2 : 30;
    const row = h_flex().id(`d-${k.id}`).h(h - (open ? 2 : 0)).rounded(6).cursor_pointer().hover(s => s.bg(t.surface)).on_click(toggle)
      .when(open, el => el.items_start().py(8).bg(t.surface).border_1().border_color(t.border));
    return { key: `d${k.id}`, h, el: this.doneGrid(t, row, [
      div().text_size(11.5).text_color(t.dim).child(`#${k.id}`),
      open ? v_flex().gap(5).min_w(0).child(div().text_size(11.5).line_height("16px").whitespace_normal().child(k.title))
          .child(div().text_size(10.5).line_height("15px").whitespace_normal().text_color(t.dim).child(one(k.evidence) || "no evidence"))
          .child(div().h(14).text_size(10.5).text_color(t.dim).child(`added by ${k.created_by ?? "?"}`))
        : div().truncate().text_size(11.5).text_color(dropped ? t.muted : t.foreground).child(k.title),
      div().truncate().text_size(11.5).text_color(t.muted).child(k.owner ?? ""),
      h_flex().gap(6).items_center().min_w(0).child(evCell.flex_1()).when(open, el => el.child(this.chev(t, "up"))),
    ]) };
  }

  // ---- Activity tab -------------------------------------------------------------------------
  // Summary: one plain sentence per event, problems in color, routine noise left to the log. A post fanned
  // out to N agents is one row, a memory-pressure episode is one row, and FOLD runs fold into one.
  // Log: every event and message state --json sent, with its raw kind, nothing folded.
  actRows(t, d, filter, log = false) {
    const items = this.actItems(d, log);
    return items.filter(i => filter === "all" || (filter === "you" ? KIND[i.kind].level === "you" && i.open : KIND[i.kind].group === filter));
  }
  // Built once per snapshot and view: Herdr's engine is slow enough that a frame can't afford it twice.
  actItems(d, log) {
    const s = this.s, c = this.actCache;
    if (c?.s === s && c.log === log) return c.items;
    const items = [], groups = new Map();
    for (const m of s.messages) {
      const kind = m.urgent ? "urgent" : m.kind === "system" || m.kind === "notice" ? "notice" : m.kind === "all" ? "all" : "msg";
      if (!log && !KIND[kind].show) continue;
      const g = `${m.frm}|${m.ts}|${m.body}`;
      if (groups.has(g)) { groups.get(g).dests.push(m.dest); continue; }
      const it = { key: `m${m.id}`, ts: m.ts, who: m.frm, kind, raw: m.kind, dests: [m.dest], text: one(m.body) };
      groups.set(g, it); items.push(it);
    }
    for (const m of items) { const n = m.dests.length; m.meta = `to ${n > 1 ? `${n} agents` : m.dests[0] === "all" ? "everyone" : m.dests[0]}`; }
    let episode = null, prev = null;
    for (const e of [...s.events].reverse()) { // oldest first: an episode opens before it closes, and runs fold forward
      if (e.kind === "post") continue; // its message is the row
      const kind = e.kind === "done" && e.agent === "swarm" && /green run/.test(e.data ?? "") ? "ci-green" : KIND[e.kind] ? e.kind : "other";
      const who = e.agent ?? "swarm";
      if (log) {
        const l = evLine(e);
        items.push({ key: `e${e.id}`, ts: e.ts, who, kind, raw: e.kind, text: `${l.text}${l.sub ? ` — ${l.sub}` : ""}` });
        continue;
      }
      if (e.kind === "pressure-end") {
        if (episode) {
          const n = episode.durs.push(e.ts - episode.since), most = ago(Math.max(...episode.durs));
          Object.assign(episode, { open: false, text: n > 1 ? `machine was short on memory ${n} times, up to ${most} each` : `machine was short on memory for ${most}` });
        }
        episode = null;
        continue;
      }
      if (!KIND[kind].show || (e.kind === "pressure" && episode)) continue;
      if (e.kind === "pressure" && prev?.kind === "pressure") { // back-to-back episodes, nothing between: one row
        Object.assign(prev, { open: true, since: e.ts, ts: e.ts, text: `machine is short on memory again (${plural(prev.durs.length, "time")} before)` });
        episode = prev;
        continue;
      }
      const it = { key: `e${e.id}`, ts: e.ts, who, kind, ...this.say(e, kind, d) };
      if (e.kind === "pressure") Object.assign(episode = it, { since: e.ts, durs: [] });
      const f = FOLD[kind];
      if (f && prev?.kind === kind && it.ts - prev.ts < 120 && (!f.same || prev.who === who)) {
        prev.parts.push(it.part); prev.whos.push(who); prev.full.push(`${who} ${it.text}`); prev.ts = it.ts;
        const n = prev.parts.length;
        if (kind === "end") Object.assign(prev, { who: `${n} agents`, text: `${andList(prev.whos)} ended` });
        else prev.text = `${{ spawn: "started", "task-add": "added", drop: "dropped" }[kind]} ${plural(n, kind === "spawn" ? "agent" : "task")}: ${andList(prev.parts)}`;
        continue;
      }
      if (f) Object.assign(it, { parts: [it.part], whos: [who], full: [`${who} ${it.text}`] });
      items.push(it); prev = it;
    }
    items.sort((a, b) => b.ts - a.ts);
    this.actCache = { s, log, items };
    return items;
  }

  // What one event says in the summary: { text, sub, part (its piece of a folded row), open, chip, meta }.
  // `open`: a "you" kind still waits on the user, or a problem is still on.
  say(e, kind, d) {
    const s = this.s, data = one(e.data), m = /^#(\d+)\s*(.*)$/.exec(data);
    const task = id => s.tasks.find(k => k.id === Number(id));
    const ref = m ? `#${m[1]} ${task(m[1])?.title ?? m[2]}`.trim() : data;
    switch (kind) {
      case "task-add": return { text: `added ${ref}`, part: m ? `#${m[1]}` : data };
      case "claim": return { text: `claimed ${ref}` };
      case "done": { const ev = evidence(m?.[2]); return { text: `finished ${ref}`, chip: ev.chip }; }
      case "ci-green": return { text: `main CI is green again (run ${/green run (\d+)/.exec(data)?.[1] ?? "?"})` };
      case "block": return { text: `asked you about #${m?.[1]}: ${m?.[2] ?? ""}`, open: task(m?.[1])?.state === "blocked" };
      case "task-blocked": return { text: `#${e.path} is waiting on you: ${data}`, open: task(e.path)?.state === "blocked" };
      case "blocked": return { text: "stopped at a prompt in its terminal", open: s.agents.find(a => a.name === e.agent)?.status === "blocked" };
      case "unblock": return { text: `unblocked ${ref}` };
      case "release": return { text: `gave back ${ref}` };
      case "drop": return { text: `dropped ${ref}`, part: m ? `#${m[1]}` : data };
      case "reap": return { text: /lease/.test(data) ? `lost ${data.replace(/^task /, "").replace(/ lease expired$/, "")}: its lease ran out` : e.path ? `lost its lock on ${e.path}: it expired` : "is gone: its terminal closed" };
      case "push": return { text: `pushed ${pushBranch(e)}`.trim(), sub: one(e.subject) };
      case "ci-red": return { text: `main CI failed (run ${data})`, meta: d.told(data) ? `told ${plural(d.told(data), "agent")}` : "" };
      case "conflict": return { text: `edits collide with ${data}'s in ${e.path}`, open: s.conflicts.some(c => c.path === e.path && [c.a, c.b].includes(e.agent)) };
      case "lock": return { text: `locked ${e.path}${data ? ` for ${data}` : ""}` };
      case "lock-violation": return { text: `edited ${e.path}, which ${data} locked` };
      case "shared-tree": return { text: `edits in ${data}'s worktree ${base(e.path)}` };
      case "spawn": return { text: `started ${data.replace(/^auto #(\d+)$/, "an agent for #$1")}`, part: data };
      case "takeover": return { text: "relaunched in a fresh session" };
      case "end": return { text: "ended", part: e.agent ?? "?" };
      case "pressure": return { text: "machine is short on memory", open: true };
      case "orphan-kill": return { text: `left a heavy process running; the swarm stopped it: ${data.split(" ").slice(1, -1).join(" ")}` };
      default: return { text: data };
    }
  }

  actColor(t, i) {
    const lv = KIND[i.kind].level;
    return lv === "you" ? (i.open === false ? t.dim : t.blocked) : lv === "warn" ? (i.open === false ? t.muted : t.ansi3) : lv === "good" ? t.ansi2 : t.muted;
  }
  icon(t, i, n = 14) {
    return this.iconDir ? svg(`${this.iconDir}/${KIND[i.kind].icon}.svg`).size(n).flex_none().text_color(this.actColor(t, i)) : div().size(n).flex_none();
  }

  // One row: time, icon, who, (log: raw kind), what, and one tail: needs you / answered / ongoing / PR / to whom.
  // The tooltip says what the kind means and whether you act; a folded row adds each event it holds.
  actRow(t, d, i, log) {
    const W = this.width, narrow = W < 520, fold = W < 640, k = KIND[i.kind], hot = k.level === "you" && i.open;
    const who = i.who === d.comms ? `${i.who} (comms)` : i.who;
    const text = `${fold ? i.who + " " : ""}${i.text}${i.sub ? ` — ${i.sub}` : ""}`;
    const tip = `${k.label}: ${k.what}${i.full?.length > 1 ? `\n\n${i.full.join("\n")}` : text.length > 70 ? `\n\n${text}` : ""}`;
    const tail = log ? null : hot ? this.chip(t, "needs you", t.blocked, true)
      : k.level === "you" ? div().flex_none().text_size(10.5).text_color(t.dim).child("answered")
      : k.level === "warn" && i.open ? this.chip(t, i.kind === "pressure" ? "ongoing" : "unresolved", t.ansi3)
      : i.chip ? this.chip(t, i.chip, i.chip.startsWith("PR") ? t.ansi2 : null) : null;
    const meta = !tail && i.meta && !narrow ? div().flex_none().text_size(10.5).text_color(t.dim).child(i.meta) : null;
    return h_flex().id(`act-${i.key}`).h(26).px(10).gap(10).items_center().min_w(0).rounded(5).tooltip(tip)
      .when(hot, el => el.bg(t.blocked + "14")).hover(st => st.bg(hot ? t.blocked + "1f" : t.surface))
      .child(div().w(34).flex_none().text_size(11).text_color(t.dim).child(hhmm(i.ts)))
      .child(this.icon(t, i))
      .when(!fold, el => el.child(div().w(W < 760 ? 80 : 118).flex_none().truncate().text_size(11).text_color(t.muted).child(who)))
      .when(log && !narrow, el => el.child(this.mono(div().w(96).flex_none().truncate().text_size(10.5).text_color(t.dim).child(i.raw))))
      .child(div().flex_1().min_w(0).truncate().text_size(11.5).text_color(hot || (k.level === "warn" && i.open !== false) || k.group === "messages" ? t.foreground : t.muted).child(text))
      .when(Boolean(tail ?? meta), el => el.child(tail ?? meta));
  }

  // The key: each kind on screen with its icon, name and meaning (the row tooltips say the same).
  actKey(t, items) {
    const kinds = Object.keys(KIND).filter(k => items.some(i => i.kind === k));
    return v_flex().id("act-key").mb(8).px(12).py(10).gap(6).rounded(8).bg(t.surface).border_1().border_color(t.border)
      .child(h_flex().gap(8).items_center().child(div().text_size(12).font_semibold().child("What these mean"))
        .child(div().text_size(10.5).text_color(t.dim).child("kinds in this view")).child(div().flex_1())
        .child(this.link(t, "key-hide", "Hide", cx => { this.open.key = false; cx.notify(); })))
      .when(!kinds.length, el => el.child(div().text_size(11).text_color(t.dim).child("Nothing in this view")))
      .children(kinds.map(k => h_flex().items_start().gap(10).min_w(0)
        .child(div().pt(1).flex_none().child(this.icon(t, { kind: k, open: true })))
        .child(div().w(this.width < 520 ? 92 : 124).flex_none().text_size(11.5).child(KIND[k].label))
        .child(div().flex_1().min_w(0).whitespace_normal().line_height("16px").text_size(11).text_color(t.muted).child(KIND[k].what))));
  }

  activity(t, d) {
    const log = Boolean(this.actLog), all = this.actRows(t, d, this.actFilter, log), rows = [];
    let hour = null;
    for (const i of all.slice(0, 80)) {
      const h = hhmm(i.ts).slice(0, 2);
      if (h !== hour) {
        hour = h;
        rows.push({ key: `hr${i.ts}`, h: 28, el: h_flex().h(28).px(10).pt(8).gap(10).items_center().text_size(10.5).text_color(t.dim).child(`${h}:00`).child(div().flex_1().h(1).bg(t.border)) });
      }
      rows.push({ key: i.key, h: 26, el: this.actRow(t, d, i, log) });
    }
    if (!rows.length) rows.push({ key: "none", h: 30, el: div().px(10).py(8).text_size(11).text_color(t.dim).child(this.actFilter === "you" ? "Nothing needs you right now." : "Nothing here yet") });
    return div().px(12).pt(4).pb(8).when(Boolean(this.open.key), el => el.child(this.actKey(t, all)))
      .child(this.list(`act-${log ? "log" : "sum"}-${this.actFilter}`, rows));
  }

  // ---- System tab ---------------------------------------------------------------------------
  prRow(t, p, withAgent) {
    const r = p.statusCheckRollup ?? [];
    const c = !r.length ? null : r.some(c => ["FAILURE", "ERROR", "CANCELLED", "TIMED_OUT"].includes(c.conclusion ?? c.state)) ? ["failing", t.blocked]
      : r.some(c => c.status && c.status !== "COMPLETED" || c.state === "PENDING") ? ["running", t.ansi3] : ["passing", t.ansi2];
    const agent = withAgent && this.s.agents.find(a => (a.branch ?? base(a.worktree)) === p.headRefName);
    return h_flex().id(`pr-${p.number}`).h(26).px(6).gap(8).items_center().rounded(6).text_size(11.5).min_w(0).cursor_pointer().hover(s => s.bg(t.hover))
      .on_click((_e, cx) => { cx.stop_propagation(); openUrl(p.url); })
      .child(div().text_color(t.dim).flex_none().child(`#${p.number}`))
      .child(div().flex_1().min_w(0).truncate().child(p.title))
      .when(withAgent, el => el.child(div().flex_none().max_w(90).truncate().text_size(10.5).text_color(agent ? t.foreground : t.dim).child(agent ? agent.name : p.headRefName)))
      .when(p.isDraft, el => el.child(this.chip(t, "draft")))
      .when(p.reviewDecision === "APPROVED", el => el.child(this.chip(t, "approved", t.ansi2)))
      .when(p.reviewDecision === "CHANGES_REQUESTED", el => el.child(this.chip(t, "changes", t.ansi3)))
      .when(Boolean(c), el => el.child(this.chip(t, c[0], c[1], true)));
  }

  system(t, d) {
    const s = this.s, m = s.machine, two = this.width >= 700, runs = this.runs;
    const latest = runs?.find(r => r.status === "completed"), red = d.reds > 0;
    const state = !runs ? null : runs[0] && runs[0].status !== "completed" ? ["running", t.ansi3] : !latest ? null : red ? ["red", t.blocked] : latest.conclusion === "success" ? ["green", t.ansi2] : [latest.conclusion, t.ansi3];
    const ci = this.card(t, "ci", red).gap(4)
      .child(h_flex().pb(6).gap(6).items_center().child(div().text_size(12).font_semibold().child("CI on main")).when(Boolean(state), el => el.child(this.chip(t, state[0], state[1], true)))
        .child(div().flex_1()).child(div().text_size(10.5).text_color(t.dim).child(red ? `${plural(d.reds, "red run")} since ${hhmm(iso(d.redRuns.at(-1).createdAt))}` : "")))
      .when(!runs, el => el.child(div().text_size(11).text_color(t.dim).child(this.prLoading ? "…" : "No CI data (gh not available here)")))
      .when(Boolean(runs) && !runs?.length, el => el.child(div().text_size(11).text_color(t.dim).child("No runs on main")))
      .children((runs ?? []).slice(0, 5).map(r => {
        const bad = r.status === "completed" && r.conclusion !== "success", n = d.told(r.databaseId);
        return h_flex().id(`run-${r.databaseId}`).h(30).px(6).gap(10).items_center().rounded(6).text_size(11.5).min_w(0).cursor_pointer().hover(st => st.bg(t.hover))
          .on_click(() => openUrl(r.url))
          .child(div().w(14).flex_none().text_color(r.status !== "completed" ? t.ansi3 : r.conclusion === "failure" ? t.blocked : bad ? t.dim : t.ansi2)
            .child(r.status !== "completed" ? "●" : r.conclusion === "failure" ? "✕" : bad ? "–" : "✓"))
          .when(this.width >= 520, el => el.child(this.mono(div().flex_none().text_size(11).child(String(r.databaseId)))))
          .child(div().w(40).flex_none().text_color(t.dim).child(hhmm(iso(r.createdAt))))
          .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(`${r.displayTitle}${n ? ` · told ${plural(n, "agent")}` : ""}`))
          .child(div().flex_none().text_size(10.5).text_color(t.dim).child("Open run ↗"));
      }))
      .when(red && Boolean(d.fix), el => el.child(h_flex().id("ci-owner").mt(6).h(34).px(8).gap(8).items_center().min_w(0).rounded(7).bg(t.hover).border_1().border_color(t.border)
        .cursor_pointer().on_click((_e, cx) => this.go("agents", cx, d.fix.owner))
        .child(div().flex_none().text_color(t.dim).child("Owner")).child(div().flex_none().font_semibold().child(d.fix.owner))
        .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(`#${d.fix.id} ${d.fix.title}`)).child(this.chev(t, "right"))));
    const prs = this.card(t, "prs").gap(6)
      .child(h_flex().gap(6).items_center().child(div().text_size(12).font_semibold().child("Pull requests")).child(div().flex_1())
        .child(div().text_size(10.5).text_color(t.dim).child(this.prs ? `${this.prs.length} open` : this.prLoading ? "…" : "")))
      .when(!this.prs, el => el.child(div().text_size(11).text_color(t.dim).child(this.prLoading ? "…" : "No PR data (gh not available here)")))
      .when(Boolean(this.prs) && !this.prs?.length, el => el.child(div().text_size(11).text_color(t.dim).child("No open PRs")))
      .children((this.prs ?? []).map(p => this.prRow(t, p, true)));
    const c = d.commsAgent;
    const comms = this.card(t, "comms").gap(6)
      .child(div().text_size(12).font_semibold().child("Comms"))
      .child(d.comms
        ? h_flex().gap(8).items_center().text_size(11.5).min_w(0).child(div().flex_none().font_semibold().text_size(12.5).child(d.comms))
          .child(div().truncate().min_w(0).text_color(t.muted).child([c?.worktree ? `⎇ ${base(c.worktree)}` : "main checkout", c?.hc ? `terminal ${c.hc}` : null, c?.started ? `started ${hhmm(c.started)}` : null].filter(Boolean).join(" · ")))
        : div().text_size(11).text_color(t.dim).child("No comms recorded"))
      .child(div().text_size(10.5).line_height("15px").whitespace_normal().text_color(t.dim)
        .child("Shown apart from the agents and left out of the live count. No idle or cold timer: it only sees swarm activity, so a comms busy with the user would look dead."));
    const tile = (label, value, color) => v_flex().flex_1().min_w(0).px(10).py(8).gap(3).rounded(8).bg(t.background).border_1().border_color(t.border)
      .child(this.k(t, label)).child(div().text_size(15).font_semibold().text_color(color ?? t.foreground).child(value));
    const gb = kb => (kb / 1048576).toFixed(1);
    const machine = this.card(t, "machine").gap(9)
      .child(h_flex().gap(6).items_center().child(div().text_size(12).font_semibold().child("Machine"))
        .when(Boolean(m), el => el.child(this.chip(t, m.high ? "pressure" : "ok", m.high ? t.blocked : t.ansi2, m.high)))
        .child(div().flex_1()).child(div().text_size(10.5).text_color(t.dim).child(this.on ? this.on : "this computer")))
      .when(!m, el => el.child(div().text_size(11).text_color(t.dim).child("No machine reading")))
      .when(Boolean(m), el => el
        .child(h_flex().gap(6).text_size(11.5).child(div().text_color(t.muted).child("Memory")).child(div().flex_1()).child(`${gb(m.avail_kb)}G free`).child(div().text_color(t.dim).child(`of ${gb(m.total_kb)}G`)))
        .child(div().relative().h(6).rounded(3).bg(t.selected).child(div().absolute().left(0).top(0).h(6).rounded(3).bg(t.muted).w(`${Math.round((1 - m.avail_kb / m.total_kb) * 100)}%`)))
        .child(h_flex().gap(8).child(tile("mem pressure", `${m.psi.memory}%`)).child(tile("cpu pressure", `${m.psi.cpu}%`)).child(tile("high", m.high ? "yes" : "no", m.high ? t.blocked : t.ansi2))));
    const heavy = s.events.filter(e => e.kind === "heavy-start").slice(0, 6), run = s.running ?? [];
    const jobs = this.card(t, "heavy").gap(6)
      .child(h_flex().gap(6).items_center().child(div().text_size(12).font_semibold().child("Running now")).child(div().flex_1()).child(div().text_size(10.5).text_color(t.dim).child(run.some(j => j.machine) ? "all machines" : "this machine")))
      .when(!run.length, el => el.child(div().text_size(11).text_color(t.dim).child("No heavy jobs running")))
      .children(run.slice(0, 8).map((j, i) => h_flex().id(`run-${i}`).h(22).gap(8).items_center().text_size(11.5).min_w(0)
        .child(div().w(40).flex_none().text_color(t.dim).child(ago(j.elapsed_s))).child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(`${j.agent} · ${j.command}`))
        .child(div().flex_none().text_color(j.lost ? t.blocked : t.dim).child(j.machine ? `${j.machine}${j.lost ? " lost" : ""}` : `${gb(j.rss_kb)}G`))))
      .child(div().mt(4).text_size(12).font_semibold().child("Recent starts"))
      .when(!heavy.length, el => el.child(div().text_size(11).text_color(t.dim).child("None recently")))
      .children(heavy.map(e => h_flex().h(22).gap(8).items_center().text_size(11.5).min_w(0)
        .child(div().w(34).flex_none().text_color(t.dim).child(hhmm(e.ts))).child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(`${e.agent ?? "?"} · ${one(e.data)}`))));
    const line = (key, text, color) => div().id(key).h(20).truncate().text_size(11).text_color(color ?? t.muted).child(text);
    const calm = !s.locks.length && !s.conflicts.length && !s.pressure.length;
    const locks = this.card(t, "locks").gap(8)
      .child(h_flex().gap(6).items_center().child(div().text_size(12).font_semibold().child("Locks and conflicts")).child(div().flex_1()).child(div().text_size(10.5).text_color(t.dim).child(calm ? "all clear" : "")))
      .child(h_flex().gap(8).child(tile("locks", String(s.locks.length))).child(tile("conflicts", String(s.conflicts.length), s.conflicts.length ? t.blocked : null)).child(tile("episodes", String(s.pressure.length), s.pressure.some(p => !p.end) ? t.blocked : null)))
      .children(s.locks.map(l => line(`lock-${l.path}`, `🔒 ${l.path} · ${l.agent}${l.reason ? " · " + l.reason : ""}`)))
      .children(s.conflicts.map(c => line(`cf-${c.a}-${c.b}-${c.path}`, `⚠ ${c.a} × ${c.b} · ${c.path} · ${ago(s.now - c.since)}`, t.blocked)))
      .children(s.pressure.map(p => line(`pr-${p.start}`, `${hhmm(p.start)}–${p.end ? hhmm(p.end) : "now"} · ${p.line.replace(/^machine: /, "")}`, p.end ? t.dim : t.blocked)));
    const left = v_flex().gap(12).min_w(0).child(ci).child(prs).child(comms), right = v_flex().gap(12).min_w(0).child(machine).child(jobs).child(locks);
    return two ? h_flex().p(12).gap(14).items_start().child(left.flex_grow(1.15).flex_basis(0)).child(right.flex_grow(1).flex_basis(0))
      : v_flex().p(12).gap(12).child(left).child(right);
  }

  // ---- Overview tab -------------------------------------------------------------------------
  overview(t, d) {
    const s = this.s, W = this.width, narrow = W < 520;
    const needs = this.needs(t, d);
    const att = needs.length ? this.card(t, "att", true).gap(9)
      .child(h_flex().gap(8).items_center().child(this.dot(t.blocked)).child(div().text_size(13).font_semibold().child(needs[0].key === "ci" ? "main CI is red" : "Needs you")).when(!d.reds && needs.length > 1, el => el.child(this.chip(t, String(needs.length), t.blocked, true)))
        .when(d.reds > 1, el => el.child(this.chip(t, `${d.reds} red runs`, t.blocked, true))).child(div().flex_1())
        .when(d.reds > 0, el => el.child(div().text_size(10.5).text_color(t.dim).child(`since ${hhmm(iso(d.redRuns.at(-1).createdAt))}`))))
      .children(d.reds ? d.redRuns.slice(0, 2).map((r, i) => h_flex().h(18).gap(8).text_size(11.5).min_w(0)
        .child(div().w(52).flex_none().text_color(t.dim).child(i ? "before" : "latest"))
        .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(`${r.databaseId} · ${hhmm(iso(r.createdAt))} · ${r.displayTitle}${d.told(r.databaseId) ? ` · told ${plural(d.told(r.databaseId), "agent")}` : ""}`)))
        : needs.slice(0, 4).map(x => h_flex().id(`need-${x.key}`).h(18).gap(8).text_size(11.5).min_w(0).cursor_pointer().on_click((_e, cx) => this.go(x.go, cx, x.sel))
          .child(div().flex_none().text_color(t.blocked).child(x.title)).child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(x.detail))))
      .when(d.reds > 0 && Boolean(d.fix), el => el.child(h_flex().id("att-owner").h(34).px(8).gap(8).items_center().min_w(0).rounded(7).bg(t.hover).border_1().border_color(t.border)
        .cursor_pointer().on_click((_e, cx) => this.go("agents", cx, d.fix.owner))
        .child(this.dot(this.statusColor(t, s.agents.find(a => a.name === d.fix.owner)?.status))).child(div().flex_none().font_semibold().text_size(12.5).child(d.fix.owner))
        .child(div().flex_none().text_color(t.dim).child("owns")).child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(`#${d.fix.id} ${d.fix.title}`)).child(this.chev(t, "right")))) : null;
    const agents = v_flex().gap(0).min_w(0)
      .child(this.sec(t, "Live", `${d.live.length} · ${d.ended.length} ended${d.comms ? " · comms not counted" : ""}`, this.link(t, "all-agents", "All agents ›", cx => this.go("agents", cx))))
      .child(this.list("ov-lanes", d.live.map(a => this.lane(t, a, { prefix: "ov", compact: W < 760 && !narrow, onClick: cx => this.go("agents", cx, a.name) }))))
      .when(!d.live.length, el => el.child(div().px(4).py(6).text_size(11).text_color(t.dim).child("No live agents")));
    const n = st => d.count(st), total = s.tasks.length || 1;
    const active = s.tasks.filter(k => ["blocked", "claimed", "open"].includes(k.state)).slice(0, 3);
    const recent = s.tasks.filter(k => k.state === "done").slice(-3).reverse();
    const board = this.card(t, "ov-board").gap(9).cursor_pointer().hover(st => st.border_color(t.input)).on_click((_e, cx) => this.go("board", cx))
      .child(h_flex().gap(6).items_center().child(div().text_size(12).font_semibold().child("Board")).child(div().text_size(10.5).text_color(t.dim).child(`${s.tasks.length} tasks`))
        .child(div().flex_1()).child(div().text_size(10.5).text_color(t.dim).child("Open board ›")))
      .child(h_flex().h(6).gap(2).rounded(3).overflow_hidden()
        .children([["done", t.ansi2], ["blocked", t.blocked], ["claimed", t.ansi3], ["open", t.muted], ["dropped", t.selected]].filter(([st]) => n(st))
          .map(([st, c]) => div().h(6).min_w(4).bg(c).w(`${(n(st) / total) * 100}%`))))
      .child(h_flex().gap(12).flex_wrap().text_size(10.5).text_color(t.muted)
        .children([["done", null], ["blocked", t.blocked], ["claimed", t.ansi3], ["open", null], ["dropped", null]].filter(([st]) => st !== "blocked" || n(st))
          .map(([st, c]) => h_flex().gap(4).child(div().text_color(c ?? t.foreground).child(String(n(st)))).child(st))))
      .children(active.map(k => h_flex().h(34).px(8).gap(8).items_center().min_w(0).rounded(7).bg(k.state === "blocked" ? t.blocked + "14" : t.background).border_1().border_color(t.border)
        .child(div().w(2).h(24).rounded(1).flex_none().bg(k.state === "blocked" ? t.blocked : k.state === "claimed" ? t.ansi3 : t.muted))
        .child(v_flex().flex_1().min_w(0).gap(1)
          .child(h_flex().gap(6).min_w(0).child(div().flex_none().text_size(10.5).text_color(t.dim).child(`#${k.id}`)).child(div().flex_1().min_w(0).truncate().child(k.title)))
          .child(div().truncate().text_size(10.5).text_color(k.state === "blocked" ? t.blocked : t.dim)
            .child(k.state === "blocked" ? `? ${one(k.question)}` : k.owner ? `${k.owner}${k.lease_left > 0 ? ` · lease ${ago(k.lease_left)} left` : ""}` : `open · by ${k.created_by ?? "?"}`)))))
      .when(recent.length > 0, el => el.child(div().pt(2).child(this.k(t, "Latest done"))))
      .children(recent.map(k => { const e = evidence(k.evidence); return h_flex().h(22).gap(8).items_center().text_size(11).min_w(0)
        .child(div().w(26).flex_none().text_size(10.5).text_color(t.dim).child(`#${k.id}`)).child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(k.title))
        .when(Boolean(e.chip), el => el.child(this.chip(t, e.chip, e.chip.startsWith("PR") ? t.ansi2 : null))); }));
    const acts = this.actRows(t, d, "all").slice(0, 8);
    const activity = this.card(t, "ov-act").gap(2)
      .child(h_flex().pb(5).gap(6).items_center().child(div().text_size(12).font_semibold().child("Activity")).child(div().text_size(10.5).text_color(t.dim).child("digested"))
        .child(div().flex_1()).child(this.link(t, "all-act", "All activity ›", cx => this.go("activity", cx))))
      .children(acts.map(i => h_flex().h(22).gap(8).items_center().text_size(11).min_w(0).tooltip(`${KIND[i.kind].label}: ${KIND[i.kind].what}`)
        .child(div().w(34).flex_none().text_color(t.dim).child(hhmm(i.ts))).child(this.icon(t, i, 12))
        .when(W >= 640, el => el.child(div().w(66).flex_none().truncate().text_color(t.muted).child(i.who)))
        .child(div().flex_1().min_w(0).truncate().text_color(KIND[i.kind].level === "you" && i.open ? t.blocked : t.muted).child(`${W < 640 ? i.who + " " : ""}${i.text}${KIND[i.kind].group === "messages" ? ` · ${i.meta}` : ""}`))))
      .when(!acts.length, el => el.child(div().text_size(11).text_color(t.dim).child("Nothing yet")));
    const leftCol = v_flex().gap(8).min_w(0).when(Boolean(att), el => el.child(att)).child(agents);
    const rightCol = v_flex().gap(12).min_w(0).child(board).child(activity);
    if (narrow) return v_flex().p(12).gap(12).child(leftCol).child(rightCol);
    return h_flex().p(12).gap(14).items_start()
      .child(W >= 760 ? leftCol.flex_grow(1.25).flex_basis(0) : leftCol.flex_1())
      .child(W >= 760 ? rightCol.flex_grow(1).flex_basis(0) : rightCol.w(260).flex_none());
  }

  // ---- frame ---------------------------------------------------------------------------------
  render(cx) {
    const t = theme(), el = this.draw(t); // draws first: it settles which agent the detail pane shows
    if (this.visible()) {
      if (!this.loading && this.due()) this.refresh(cx);
      if ((this.tab === "agents" || this.tab === "system") && Date.now() - (this.prsAt ?? 0) > PR_POLL) this.refreshPrs(cx);
    }
    // Keys first drawn in this frame sit at their start values; a frame later they move, staggered.
    if (this.fresh.size && !this.entering) {
      this.entering = true;
      cx.timer.after(40, cx => { for (const k of this.fresh) this.seen.add(k); this.fresh.clear(); this.entering = false; cx.notify(); });
    }
    return el;
  }

  // Widths (this.width from on_size_change): 860 as drawn; below 760 the 640 layout; below 520 one column
  // (the 420 layout); 340 and below the 320 tweaks.
  draw(t) {
    const s = this.s, W = this.width, narrow = W < 520, tiny = W <= 340;
    const root = v_flex().id("swarm").size_full().min_h(0).rounded(10).overflow_hidden().bg(t.background).border_1().border_color(t.border).text_color(t.foreground).text_size(12)
      .on_size_change((size, cx) => { if (Math.abs(size.width - this.width) > 1) { this.width = size.width; cx.notify(); } });
    const note = text => div().px(16).pt(14).text_size(11).text_color(t.dim).child(text);
    if (!s?.agents) {
      return root.child(h_flex().h(44).flex_none().px(16).items_center().border_b(1).border_color(t.border).child(div().font_semibold().text_size(13).child("Swarm")))
        .child(note(this.error ?? (this.loading || !s ? "loading…" : "No live swarm in this repo")));
    }
    const d = this.derive(), m = s.machine;
    const working = d.live.filter(a => a.status === "working").length, claimed = d.count("claimed"), blocked = d.count("blocked");
    const body = this.tab === "agents" ? this.agents(t, d) : this.tab === "board" ? div().px(12).pt(8).pb(12).child(this.list(`board-${this.boardFilter}`, this.boardRows(t, d)))
      : this.tab === "activity" ? this.activity(t, d) : this.tab === "system" ? this.system(t, d) : this.overview(t, d);
    const fixed = this.tab === "agents" && !narrow; // master and detail scroll on their own
    return root
      .child(h_flex().h(44).flex_none().px(16).gap(8).items_center().min_w(0).border_b(1).border_color(t.border)
        .child(div().flex_none().font_semibold().text_size(13).child("Swarm"))
        .child(div().truncate().min_w(0).text_color(t.dim).child(base(this.cwd)))
        .when(Boolean(d.comms) && !tiny, el => el.child(div().flex_none().text_color(t.dim).child("·"))
          .child(h_flex().flex_none().gap(4).text_size(10.5).text_color(t.muted).child("comms").child(div().text_color(t.foreground).child(d.comms))))
        .child(div().flex_1())
        .child(this.chip(t, `${d.live.length} live`))
        .when(!narrow, el => el.child(this.chip(t, `${working} working`)))
        .when(claimed > 0, el => el.child(this.chip(t, `${claimed} claimed`, t.ansi3, true)))
        .when(blocked > 0, el => el.child(this.chip(t, `${blocked} blocked`, t.blocked, true)))
        .when(!narrow, el => el.child(div().flex_none().text_size(10.5).text_color(t.dim).child(`${d.count("done")} of ${s.tasks.length} done`))))
      .child(this.strip(t, d))
      .child(this.nav(t, d))
      .when(!s.active, el => el.child(note("No live swarm in this repo; showing its last state.")))
      .when(Boolean(this.error), el => el.child(note(this.error)))
      .child(fixed ? div().flex_1().min_h(0).mt(2).child(body) : v_flex().id(`body-${this.tab}`).flex_1().min_h(0).mt(2).overflow_y_scrollbar().child(body))
      .child(h_flex().h(30).flex_none().px(16).gap(8).items_center().border_t(1).border_color(t.border).text_size(10.5).text_color(t.dim)
        .child(this.dot(m?.high ? t.blocked : t.ansi2, 6))
        .child(div().truncate().min_w(0).child(m ? `machine ${m.high ? "under pressure" : "ok"} · mem ${m.psi.memory}% · cpu ${m.psi.cpu}%` : "no machine reading"))
        .child(div().flex_1())
        .when(Boolean(m) && !tiny, el => el.child(div().flex_none().child(`${(m.avail_kb / 1048576).toFixed(1)} of ${(m.total_kb / 1048576).toFixed(1)}G free`))));
  }
}

// ---- Activity kinds --------------------------------------------------------------------------
// Every event kind swarm logs and every message kind, as the Activity tab names them:
// [icon in icons/, filter group, label, what it means and whether you act, level, in the summary].
// level: "you" red while it waits on the user (dim once answered), "warn" a problem the agents or swarm
// handle, "good" something finished, "" plain. Kinds missing here (new or old ones) show only in the log.
const KIND = Object.fromEntries(Object.entries({
  "task-add": ["plus", "tasks", "Task added", "Someone put a new task on the board. Nothing for you to do.", "", 1],
  claim: ["play", "tasks", "Claimed", "An agent took a task and is working on it. Nothing for you to do.", "", 1],
  done: ["check", "tasks", "Done", "An agent finished a task and its work is on main. Nothing for you to do.", "good", 1],
  block: ["circle-help", "tasks", "Asked you", "An agent is blocked on a question only you can answer. Answer it in the agent's terminal.", "you", 1],
  "task-blocked": ["circle-help", "tasks", "Waiting on you", "A task is held up by a prompt or question for you. Answer it in the agent's terminal.", "you", 1],
  unblock: ["play", "tasks", "Unblocked", "A blocked task is moving again. Nothing for you to do.", "", 1],
  release: ["undo", "tasks", "Released", "An agent gave a task back to the board for another agent. Nothing for you to do.", "", 1],
  drop: ["x", "tasks", "Dropped", "A task was taken off the board for good. Nothing for you to do.", "", 1],
  reap: ["clock", "tasks", "Taken back", "The swarm took back a task or lock whose holder went quiet, so another agent can pick it up.", "warn", 1],
  "lease-late": ["clock", "tasks", "Lease late", "An agent has held a task past its lease while idle. The comms was told.", "", 0],
  "task-after": ["link", "tasks", "Order set", "A task was set to wait for other tasks to finish first.", "", 0],
  startable: ["info", "tasks", "Startable", "A waiting task became free to claim (older swarms).", "", 0],
  push: ["arrow-up", "code", "Pushed", "An agent pushed a branch to GitHub. Nothing for you to do.", "", 1],
  "ci-red": ["circle-x", "code", "CI red", "main's CI failed. The swarm put a fix task on the board; act only if no agent takes it.", "warn", 1],
  "ci-green": ["circle-check", "code", "CI green", "main's CI passed again and the fix task closed itself.", "good", 1],
  conflict: ["git-merge", "code", "Conflict", "Two agents' uncommitted edits collide. Whoever lands first wins and the other rebases; act only if it lingers.", "warn", 1],
  "conflict-compat": ["git-merge", "code", "Merges cleanly", "Two agents edit the same files, but their changes merge without a conflict.", "", 0],
  "conflict-stale": ["git-merge", "code", "Behind main", "An agent's work conflicts with main itself; it has to merge main first.", "", 0],
  "conflict-error": ["git-merge", "code", "Conflict check failed", "The swarm could not trial-merge two agents' work this time.", "", 0],
  overlap: ["triangle-alert", "code", "Overlap", "Two agents edited the same files (older swarms).", "warn", 0],
  lock: ["lock", "code", "Locked", "An agent reserved a path git can't see. It frees itself when the work lands.", "", 1],
  unlock: ["lock-open", "code", "Unlocked", "A lock was freed, usually because its work landed.", "", 0],
  "deny-lock": ["ban", "code", "Edit refused", "An agent tried to edit a path another agent locked, and was stopped.", "", 0],
  "lock-violation": ["triangle-alert", "code", "Lock broken", "An agent edited a path another agent locked. Both were told and sort it out.", "warn", 1],
  "shared-tree": ["users", "code", "Shared worktree", "Two agents edit in one worktree, so their changes mix. Both were told to split up.", "warn", 1],
  sweep: ["trash", "code", "Worktree removed", "A finished agent's worktree was cleaned up.", "", 0],
  spawn: ["user-plus", "agents", "Started", "A new agent joined the swarm. Nothing for you to do.", "", 1],
  join: ["log-in", "agents", "Joined", "An agent registered with the swarm.", "", 0],
  takeover: ["refresh", "agents", "Relaunched", "An agent handed off to a fresh session of itself. Nothing for you to do.", "", 1],
  blocked: ["circle-help", "agents", "Waiting on you", "An agent is stopped at a prompt in its terminal. Open it and answer.", "you", 1],
  end: ["user-minus", "agents", "Ended", "An agent's work is on main, so the swarm closed it. Nothing for you to do.", "", 1],
  leave: ["log-out", "agents", "Left", "An agent left the swarm.", "", 0],
  compact: ["shrink", "agents", "Compacted", "An agent's context was summarized to free room.", "", 0],
  "ctx-note": ["gauge", "agents", "Context note", "An agent's context passed a size mark and it was told to wrap up or hand off.", "", 0],
  fenced: ["ban", "agents", "Fenced", "An old session of an agent acted after its successor took over, and was ignored.", "", 0],
  wake: ["bell", "messages", "Woke", "An idle agent woke up to read new messages.", "", 0],
  digest: ["info", "messages", "Board nudge", "An idle agent was told there are open tasks.", "", 0],
  "deny-cold": ["ban", "messages", "Message held", "A direct message to an agent with a cold cache went to its inbox instead.", "", 0],
  msg: ["message", "messages", "Message", "One agent wrote to another. Nothing for you to do.", "", 1],
  all: ["megaphone", "messages", "To everyone", "An agent wrote to the whole swarm. Nothing for you to do.", "", 1],
  urgent: ["bell", "messages", "Urgent message", "An agent sent a message that wakes its reader at once.", "warn", 1],
  notice: ["info", "messages", "Swarm notice", "The swarm told an agent something on its own, such as a conflict or an idle nudge.", "", 0],
  pressure: ["gauge", "machine", "Memory pressure", "The machine ran short of memory. Agents were told to prefer light work; act if it lasts.", "warn", 1],
  "pressure-end": ["gauge", "machine", "Pressure over", "The machine has enough memory again.", "", 0],
  "heavy-start": ["cpu", "machine", "Heavy run", "An agent started a build or test.", "", 0],
  "job-start": ["cpu", "machine", "Run started", "An agent started a build or test on another machine.", "", 0],
  "job-end": ["cpu", "machine", "Run finished", "A build or test on another machine finished.", "", 0],
  "remote-clean": ["trash", "machine", "Run cleaned up", "A finished run's copy on another machine was removed.", "", 0],
  "orphan-kill": ["zap", "machine", "Process stopped", "The swarm stopped a heavy process an agent left running. Nothing for you to do.", "warn", 1],
  other: ["dot", "other", "Other", "An event this panel has no description for.", "", 0],
}).map(([k, [icon, group, label, what, level, show]]) => [k, { icon, group, label, what, level, show: Boolean(show) }]));
// Runs of these, within two minutes, fold into one summary row; `same`: only by the same agent.
const FOLD = { spawn: { same: true }, end: {}, "task-add": { same: true }, drop: { same: true } };
const andList = xs => xs.length > 1 ? `${xs.slice(0, -1).join(", ")} and ${xs.at(-1)}` : xs[0] ?? "";
