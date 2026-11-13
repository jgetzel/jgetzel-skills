// Screenshot it from a worktree: swarm/herdr/shot.sh --screen task:5 --width 520 out.png (a private Herdr, never yours).
import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex, HoverCard, TextView, InputState, Input } from "gpui-base";
import { spaces, panes, focused, exec, theme, layout, run, appHome, window, settings, watchFolder, openOverlay, nextCommand, shared, setShared } from "herdr";

// The screen the panel opens on; shot.sh rewrites this line. home | agents | board[:done|dropped] | task:<id> |
// agent:<name> | more:<activity|system>; "+ask" also opens that screen's confirmation, "+new" Board's new-task form.
const SCREEN = "home";
// Locally mods/swarm is a symlink into the repo, so this is the swarm CLI of the same checkout; on another
// machine it is that machine's installed skill. It runs as "human": the user, with the communicator's rights.
const swarm = (cwd, on, args) => on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB SWARM_NAME=human "$HOME/.claude/skills/swarm/swarm" "$@"', "sh", ...args], { cwd, on })
  : exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", `${appHome()}/mods/swarm/../../../swarm`, ...args], { cwd });
// POLL: the fastest rate, while the db changes. QUIET_POLL: a watched local db that hasn't changed (idle
// timers, cache countdowns and the machine reading still move). REMOTE_POLL: other machines, unwatched.
const POLL = 3000, QUIET_POLL = 30000, REMOTE_POLL = 10000, PR_POLL = 60000;
const CTX_MAX = 600000, FINISH = 350000, HANDOFF = 550000; // the context bar's scale and its two ticks
const route = spec => {
  const [s, x] = spec.replace(/\+(ask|new)$/, "").split(":");
  return s === "task" ? { s, id: Number(x) } : s === "agent" ? { s, name: x } : s === "board" ? { s, f: x ?? "active" } : s === "more" ? { s, tab: x ?? "activity" } : { s };
};
const RED = new Set(["overlap", "conflict", "conflict-error", "pressure", "ci-red", "orphan-kill", "lock-violation", "blocked", "task-blocked", "stay-hung"]);

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
const one = x => {
  const t = String(x ?? "");
  for (let i = 0; i <= t.length;) {
    let j = t.indexOf("\n", i); if (j < 0) j = t.length;
    const l = t.slice(i, j).trim();
    if (l) return l;
    i = j + 1;
  }
  return "";
};
// Push events carry branch and subject (state --json since #39); older ones only the shell command.
const pushBranch = e => {
  if (e.branch) return e.branch;
  const m = /git push([^\n;&|]*)/.exec(e.data ?? "");
  return m ? m[1].trim().split(/\s+/).filter(w => w && !w.startsWith("-")).pop() ?? "" : "";
};
// A stayer's hung sign (state --json's stay_sign, from watchd.hung): [chip, what it means, red].
const SIGN = {
  hung: ["hung", "Did not answer the liveness check. The communicator was told to unstick it (hc send) or end it.", true],
  nowaiter: ["no waiter", "Stays, but its waiter is gone, so no message can wake it. The communicator was told.", false],
  unwoken: ["not waking", "A message has sat unread past two watchd ticks. The communicator was told.", false],
};
// The board's "auto-spawn holding: <why>; N task(s) startable[; max M]" as "holding N tasks: <why>".
const held = h => {
  const [why, ...rest] = one(h).replace(/^auto-spawn holding: /, "").split("; "), n = /^(\d+) task/.exec(rest[0] ?? "")?.[1];
  return `holding${n ? ` ${plural(Number(n), "task")}` : ""}: ${why}`;
};
// Kinds whose event carries little or no text: what they say, from the event's first data line.
const SAYS = {
  "stay-hung": () => "is hung: no answer to the liveness check",
  "stay-nowaiter": () => "stays, but has no waiter and can't be woken",
  "stay-unwoken": () => "did not wake on a message",
  "stay-check": () => "was asked if it still stays",
  "spawn-refused": d => `could not start ${d}: the swarm is at its max`,
  "spawn-held": d => `auto-spawn is ${held(d)}`,
  limits: d => `set the limits: ${d.replace(/min (\S+) max (\S+)/, (_, a, b) => `auto-spawn to ${a === "nil" ? "no number" : a}, max ${b === "nil" ? "unset" : b}`)}`,
  block: d => `asked you: ${d.replace(/^#\d+\s*/, "")}`, stay: d => `stays for ${d}`, "stay-end": () => "stopped staying", role: d => `is now ${d}`,
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
    default: return { k: e.kind, text: SAYS[e.kind]?.(d) ?? [d, e.path].filter(Boolean).join(" "), red: RED.has(e.kind) };
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
// Lines `text` takes when wrapped at spaces in `px`, a word longer than a line broken anywhere. Errs high:
// the renderer also breaks after "/" and its glyphs average under `charW`.
function wrapLines(text, px, charW) {
  const per = Math.max(8, Math.floor(px / charW));
  let n = 1, col = 0;
  for (const w of String(text ?? "").split(/\s+/).filter(Boolean)) {
    if (col && col + 1 + w.length > per) { n++; col = 0; }
    if (col) col += 1 + w.length;
    else { n += Math.ceil(w.length / per) - 1; col = w.length % per || per; }
  }
  return n;
}
// URLs, shorter: a GitHub PR or issue link becomes "PR #N" ("issue #N"), and the row's chip when the text
// ends with it; any other link loses its scheme and host.
function shortUrls(s) {
  s = s.replace(/https?:\/\/github\.com\/[\w.-]+\/[\w.-]+\/(pull|issues)\/(\d+)(?:[/#?][^\s)\]]*)?/g, (_, k, n) => `${k === "pull" ? "PR" : "issue"} #${n}`)
    .replace(/\b(PR|issue) \1 #/g, "$1 #")
    .replace(/https?:\/\/[^\s/)\]]+\/([^\s)\]]+)/g, "$1").replace(/https?:\/\//g, "");
  const m = /^(.*?\S)[\s:;,.—-]*\b((?:PR|issue) #\d+)[\s.;:]*$/.exec(s);
  return m ? { text: m[1], chip: m[2] } : { text: s, chip: null };
}
const openUrl = url => exec(window()?.platform === "macos" ? "open" : "xdg-open", [url]);

export default class Swarm extends View {
  init(_props, cx) {
    this.s = null; this.prs = null; this.error = null;
    this.seen = new Set(); this.fresh = new Set(); this.delay = new Map(); this.open = {}; this.width = 520;
    const r0 = route(SCREEN); this.stack = r0.s === "task" ? [{ s: "board", f: "active" }, r0] : r0.s === "agent" ? [{ s: "agents" }, r0] : [r0]; this.flash = null; this.pending = null; this.actFilter = "all";
    // Text fields: Enter sends, Esc clears (field()).
    const input = (placeholder, send) => { const st = InputState.new({ placeholder }); st.on("submit", (_e, cx) => send(cx)); return st; };
    const add = cx => this.addTask(cx);
    this.in = { msg: input("Message this agent", cx => this.sendMsg(cx)), title: input("Title", add), body: input("Description (optional)", add),
      after: input("After tasks, e.g. 3,5", add), model: input("Model, e.g. opus", add) };
    this.urgent = false; this.adding = SCREEN.endsWith("+new"); this.moreOpts = false; this.nudged = new Map();
    this.refresh(cx); this.copyIcons(cx);
    // Data timers only; each tick returns at once while the panel isn't shown or nothing is due.
    cx.timer.every(POLL, cx => { if (this.visible() && this.due()) this.refresh(cx); });
    cx.timer.every(PR_POLL, cx => { if (this.visible()) this.refreshPrs(cx); });
    // The confirm dialog's yes arrives as the mod command "yes".
    cx.spawn(async cx => {
      for (;;) {
        const c = await nextCommand(), p = this.pending;
        if (c === "yes" && p) { this.pending = null; this.act(cx, p.args, p); }
        if (c === "ask") { // shot.sh: the shown screen's confirmation
          const r = this.r, a = this.s?.agents?.find(x => x.name === r.name), k = this.s?.tasks?.find(x => x.id === r.id);
          if (a) this.askEnd(a); else if (k) this.askRelease(k); else if (r.s === "more") this.askWatchd();
        }
      }
    });
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

  get r() { return this.stack.at(-1); }
  // The `state --view` the shown screen reads.
  get tab() { const r = this.r; return r.s === "more" ? r.tab : r.s === "home" ? "overview" : r.s === "task" || r.s === "board" ? "board" : "agents"; }
  view() { return JSON.stringify(this.r); }
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
    const r = this.r, view = this.view();
    const args = ["state", "--json", "--view", this.tab, ...(r.s === "agent" ? ["--agent", r.name] : r.s === "task" ? ["--task", String(r.id)] : [])];
    this.loading = true; this.at = Date.now(); this.dirty = false; this.polled = view;
    cx.spawn(async cx => {
      try {
        const r = await swarm(cwd, on, args);
        if (r.code !== 0) throw new Error(r.stderr.trim() || `swarm exited ${r.code}`);
        const s = JSON.parse(r.stdout);
        const now = location();
        if (now.cwd !== cwd || now.on !== on) return; // moved to another folder meanwhile; the next render asks again
        const same = s.db === this.s?.db && on === this.on;
        if (!same) {
          if (this.s) { this.seen.clear(); this.stack = [{ s: "home" }]; this.flash = null; } // another repo: its swarm, not the last one's
          this.prs = null; this.prsAt = 0; this.cwd = cwd; this.on = on; this.refreshPrs(cx);
        }
        // A view sends only its sections; the others keep their last values (empty at first) until their screen asks.
        this.s = { messages: [], events: [], locks: [], ...(same ? this.s : null), ...s }; this.error = null;
        if (this.s.agents) { const d = this.derive(); this.acts = [this.buildActs(d, false), this.buildActs(d, true)]; }
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

  // Open PRs, for an agent's screen and System. CI comes from state --json's `ci` (the table watchd fills).
  refreshPrs(cx) {
    const cwd = this.cwd, on = this.on;
    if (!cwd || this.prLoading || (this.tab !== "agents" && this.tab !== "system")) return;
    this.prLoading = true;
    cx.spawn(async cx => {
      try {
        const pr = await exec("gh", ["pr", "list", "--limit", "30", "--json", "number,title,headRefName,isDraft,reviewDecision,statusCheckRollup,url"], { cwd, on });
        this.prs = pr.code === 0 ? JSON.parse(pr.stdout) : null;
      } catch { this.prs = null; } // no gh: that part just says so
      finally { this.prLoading = false; this.prsAt = Date.now(); cx.notify(); }
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

  // ---- screens and actions -------------------------------------------------------------------
  // The nav bar's four sections are roots. A task or an agent opens on top of the screen it was picked on and
  // slides in; ‹ goes back. Rows re-run their staggered entrance.
  push(r, cx) {
    if (r.s !== "task" && r.s !== "agent") this.stack = [r];
    else if (JSON.stringify(r) !== this.view()) this.stack.push(r);
    this.landed(cx);
  }
  back(cx) { if (this.stack.length > 1) this.stack.pop(); this.landed(cx); }
  landed(cx) {
    this.seen = new Set([...this.seen].filter(k => k.startsWith("bar:"))); this.delay.clear(); this.flash = null;
    cx.notify();
  }
  // Runs one swarm command for the user. What it printed, or why it refused, shows at the top of the screen.
  // o.gh: a `gh` command instead (re-run CI); o.ok(): after it succeeded.
  act(cx, args, o = {}) {
    const { cwd, on } = location();
    this.busy = true; cx.notify();
    cx.spawn(async cx => {
      try {
        const r = await (o.gh ? exec("gh", args, { cwd, on }) : swarm(cwd, on, args));
        this.flash = r.code === 0 ? { ok: one(r.stdout) || "Done" } : { error: (r.stderr.trim() || r.stdout.trim() || `${o.gh ? "gh" : "swarm"} exited ${r.code}`).replace(/^swarm: /, ""), args };
        if (r.code === 0) o.ok?.();
      } catch (e) { this.flash = { error: String(e.message ?? e), args }; }
      this.busy = false; this.dirty = true; this.at = 0; cx.notify();
    });
  }
  // A destructive command: Herdr's confirm dialog first; its Confirm sends this mod "yes".
  ask(title, detail, args, o = {}) {
    this.pending = { ...o, args };
    openOverlay({ mod: "confirm", kind: "dialog", width: 440, height: 200, props: { title, detail, command: { name: "swarm.yes" } } });
  }
  askEnd(a, force) {
    this.ask(force ? `End ${a.name} anyway?` : `End ${a.name}?`,
      force ? `Its terminal closes now, with whatever it was doing. ${a.task ? `Task #${a.task.id} goes back to the board. ` : ""}Its worktree and branch stay.`
        : `Closes ${a.name}'s terminal. The swarm refuses if it is working, holds a task or a lock, or has work that is not on main yet. Its worktree and branch stay.`,
      ["end", a.name, ...(force ? ["--force"] : [])]);
  }
  askDrop(k) {
    this.ask(`Drop #${k.id}?`, `"${k.title}" leaves the board for good; tasks that wait on it stay held.${k.owner && k.state !== "open" ? ` ${k.owner} is told to stop.` : ""}`, ["task", "drop", String(k.id)]);
  }
  askStayEnd(a) {
    this.ask(`End ${a.name}'s stay?`, `${a.name} stops waiting for "${one(a.stay)}". watchd then ends it once its work is on main; every other check still applies.`, ["stay", "--end", a.name]);
  }
  askRerun(run) {
    this.ask(`Re-run the failed jobs of run ${run}?`, "It spends CI minutes, and an agent may be mid-fix.", ["run", "rerun", String(run), "--failed"], { gh: true });
  }
  askWatchd() {
    this.ask("Restart watchd?", "The swarm's daemon is replaced by a new one with the flags it was started with. The bar says whether the new one is alive.", ["watchd", "--restart"]);
  }
  nudge(cx, a) { this.act(cx, ["nudge", a.name], { ok: () => this.nudged.set(a.name, Date.now()) }); }
  sendMsg(cx) {
    const name = this.r.name, text = this.in.msg.value().trim();
    if (!name || !text || this.busy) return;
    this.act(cx, ["post", ...(this.urgent ? ["--urgent"] : []), "--", name, text], { ok: () => { this.in.msg.set_value(""); this.urgent = false; } });
  }
  addTask(cx) {
    const v = k => this.in[k].value().trim(), title = v("title"), after = v("after").replace(/[#\s]/g, "");
    if (!title || this.busy) return;
    this.act(cx, ["task", "add", ...(v("body") ? ["--body", v("body")] : []), ...(after ? ["--after", after] : []), ...(v("model") ? ["--model", v("model")] : []), "--", title],
      { ok: () => { for (const k in this.in) if (k !== "msg") this.in[k].set_value(""); this.adding = false; } });
  }
  askRelease(k) {
    this.ask(`Release #${k.id} from ${k.owner}?`, `"${k.title}" goes back to the board as open, for any agent to claim. ${k.owner} is told to stop; what it already wrote stays in its worktree.`, ["task", "release", String(k.id)]);
  }

  // ---- small parts --------------------------------------------------------------------------
  chip(t, text, color, fill) {
    return div().px(5).h(16).flex_none().flex().items_center().rounded(4).text_size(10).whitespace_nowrap().border_1()
      .border_color(fill ? color : color ? color + "66" : t.border).bg(fill ? color + "22" : t.background).text_color(color ?? t.muted).child(text);
  }
  dot(color, n = 8) { return div().size(n).rounded(n / 2).flex_none().bg(color); }
  mono(el) { return el.font_family(settings().font_family ?? "JetBrains Mono"); }
  chev(t, dir) { return div().flex_none().text_size(11).text_color(t.dim).child({ right: "›", up: "⌃", down: "⌄" }[dir]); }
  btn(t, id, label, onClick) {
    return h_flex().id(id).h(24).px(10).gap(5).flex_none().items_center().rounded(6).border_1().border_color(t.border).bg(t.surface)
      .text_size(11).cursor_pointer().hover(s => s.bg(t.hover)).on_click((_e, cx) => { cx.stop_propagation(); onClick(cx); }).child(label);
  }
  // A one-line text field: Enter sends (the state's submit), Esc clears.
  field(t, id, st) {
    return div().id(id).flex_1().min_w(0).h(30).px(10).flex().items_center().rounded(7).border_1().border_color(t.input ?? t.border).bg(t.background).cursor_text()
      .on_mouse_down("left", (_e, cx) => cx.stop_propagation())
      .on_key_down((e, cx) => { if (e.key === "escape") { st.set_value(""); cx.notify(); } })
      .child(Input.new(st).h_full().text_size(12.5).text_color(t.foreground));
  }
  tick(t, id, label, on, set) {
    return h_flex().id(id).flex_none().h(24).gap(6).items_center().text_size(11).text_color(on ? t.foreground : t.muted).cursor_pointer()
      .on_click((_e, cx) => { cx.stop_propagation(); set(cx); })
      .child(div().size(14).flex().items_center().justify_center().rounded(4).border_1().border_color(on ? t.accent : t.input ?? t.border).bg(on ? t.accent : t.background)
        .text_size(10).text_color(t.accent_foreground).child(on ? "✓" : ""))
      .child(label);
  }
  link(t, id, text, onClick) {
    return div().id(id).flex_none().text_size(11).text_color(t.dim).cursor_pointer().hover(s => s.text_color(t.foreground))
      .on_click((_e, cx) => { cx.stop_propagation(); onClick(cx); }).child(text);
  }

  statusColor(t, s) { return { working: t.working, idle: t.idle, blocked: t.blocked, ended: t.dim }[s] ?? t.unknown; }
  signChip(t, a) { const g = SIGN[a.stay_sign]; return g ? this.chip(t, g[0], g[2] ? t.blocked : t.ansi3, true).tooltip(g[1]) : null; }

  // Context bar on a 0..600k scale with ticks at the 350k finish note and the 550k compaction note; it fills
  // 0 -> value once per key (a lane, or the detail pane for one agent).
  ctxBar(t, key, n, big) {
    const pct = Math.min(100, (n / CTX_MAX) * 100), { first } = this.enter(`bar:${key}`, false), h = big ? 6 : 4;
    const tick = (at, color) => div().absolute().left(`${(at / CTX_MAX) * 100}%`).top(big ? -4 : -2).w(1).h(h + (big ? 8 : 4)).bg(color);
    return div().relative().flex_1().min_w(0).h(h).rounded(h / 2).bg(t.selected)
      .child(div().id(`bar:${key}`).absolute().left(0).top(0).h(h).rounded(h / 2).bg(n >= HANDOFF ? t.blocked : n >= FINISH ? t.ansi3 : t.ansi4)
        .w(first ? "0%" : `${pct}%`).transition("width", { duration: 400, easing: "ease-out" }))
      .child(tick(FINISH, t.dim)).child(tick(HANDOFF, t.blocked));
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
    // main's CI, from the table watchd fills: [word, color] of the latest run, and the newest finished run when it is red.
    const runs = s.ci?.runs ?? [], last = runs.find(r => r.status === "completed" && r.conclusion !== "cancelled"), reds = s.ci?.red_streak ?? 0;
    const ci = !runs.length ? null : runs[0].status !== "completed" ? ["pending", "ansi3"] : reds ? ["red", "blocked"] : last?.conclusion === "success" ? ["green", "ansi2"] : [runs[0].conclusion ?? "?", "ansi3"];
    const w = s.watchd, watchdDead = Boolean(s.active && w && !w.alive);
    // shortcut: the CI fixer is the claimed task that mentions red/CI; a ci-red -> task link in the db would be exact.
    const fix = s.tasks.find(k => (k.state === "claimed" || k.state === "blocked") && /\b(red|ci)\b/i.test(k.title));
    const told = id => s.messages.filter(m => m.kind === "system" && m.body.startsWith(`main CI is red (run ${id}`)).length;
    return { comms, commsAgent: s.agents.find(a => a.name === comms), live, ended, count, runs, reds, redRun: reds ? last : null, ci, watchdDead, fix, told };
  }

  // ---- shared parts of the screens ------------------------------------------------------------
  // One scale everywhere: 16 a screen's title, 12.5 a row, 11 its meta; 16px gutters; rows grouped in one
  // bordered card with hairlines between them.
  group(t, id, red) {
    return v_flex().id(id).w_full().min_w(0).rounded(10).overflow_hidden().bg(red ? t.blocked + "12" : t.surface).border_1().border_color(red ? t.blocked + "88" : t.border);
  }
  row(t, id, i, onClick) {
    return h_flex().id(id).h(38).flex_none().px(12).gap(10).items_center().min_w(0).text_size(12.5)
      .when(i > 0, el => el.border_t(1).border_color(t.border))
      .when(Boolean(onClick), el => el.cursor_pointer().hover(s => s.bg(t.hover)).on_click((_e, cx) => { cx.stop_propagation(); onClick(cx); }));
  }
  title(t, label, note, right) {
    return h_flex().h(30).flex_none().px(2).gap(8).items_center().min_w(0)
      .child(div().flex_none().text_size(12.5).font_semibold().child(label))
      .when(note != null && note !== "", el => el.child(div().truncate().min_w(0).text_size(11).text_color(t.dim).child(String(note))))
      .child(div().flex_1()).when(Boolean(right), el => el.child(right));
  }
  more(t, id, text, onClick) { return this.link(t, id, text, onClick).text_size(11).text_color(t.muted); }
  danger(t, id, label, onClick) { return this.btn(t, id, label, onClick).text_color(t.blocked).border_color(t.blocked + "66"); }
  empty(t, text) {
    return h_flex().h(38).px(12).items_center().rounded(10).border_1().border_dashed().border_color(t.border).text_size(12).text_color(t.dim).child(text);
  }
  seg(t, id, opts, cur, pick) {
    return h_flex().flex_none().p(2).gap(2).rounded(8).bg(t.surface).border_1().border_color(t.border)
      .children(opts.map(([k, label, n]) => h_flex().id(`${id}-${k}`).h(26).flex_1().px(10).gap(6).justify_center().items_center().rounded(6).text_size(12).cursor_pointer()
        .bg(k === cur ? t.selected : t.surface).text_color(k === cur ? t.foreground : t.muted).when(k === cur, el => el.font_semibold())
        .hover(st => st.text_color(t.foreground)).on_click((_e, cx) => pick(k, cx)).child(label)
        .when(n != null, el => el.child(div().text_size(11).font_normal().text_color(t.dim).child(String(n))))));
  }

  // Label and value rows; null rows are left out.
  facts(t, id, rows) {
    return this.group(t, id).children(rows.filter(Boolean).map(([label, el], i) => h_flex().px(12).py(9).gap(12).items_start().min_w(0).text_size(12)
      .when(i > 0, el => el.border_t(1).border_color(t.border))
      .child(div().w(76).flex_none().text_color(t.dim).child(label)).child(div().flex_1().min_w(0).child(el))));
  }
  taskColor(t, k) { return { blocked: t.blocked, claimed: t.working, done: t.ansi2, dropped: t.dim }[k.state] ?? (k.waiting ? t.dim : t.muted); }
  taskWord(k) { return { blocked: "waiting on you", claimed: "in progress", open: k.waiting ? "waiting" : "ready" }[k.state] ?? k.state; }
  // Priority P0 (urgent) to P3 (someday), 2 when the row has none: the board's order is priority, then id.
  prio(k) { return k.priority ?? 2; }
  prioChip(t, k) { return this.chip(t, `P${this.prio(k)}`, [t.blocked, t.ansi3, null, t.dim][this.prio(k)], this.prio(k) < 2).tooltip("Priority: lower is picked first"); }
  undone(k) { return k.waiting ? k.deps.filter(i => this.s.tasks.find(x => x.id === i)?.state !== "done") : []; }
  taskRow(t, k, i) {
    const e = k.state === "done" ? evidence(k.evidence) : null, after = this.undone(k);
    const right = k.state === "blocked" ? "waiting on you" : k.state === "open" ? (after.length ? `after ${after.map(x => `#${x}`).join(" ")}` : "ready") : k.owner ?? "";
    return this.row(t, `task-${k.id}`, i, cx => this.push({ s: "task", id: k.id }, cx))
      .child(this.dot(this.taskColor(t, k), 7))
      .child(div().w(26).flex_none().text_size(11).text_color(t.dim).child(`#${k.id}`))
      .child(div().flex_1().min_w(0).truncate().text_color(k.state === "dropped" || k.waiting ? t.muted : t.foreground).child(k.title))
      .when(Boolean(e?.chip), el => el.child(this.chip(t, e.chip, e.chip.startsWith("PR") ? t.ansi2 : null)))
      .when(k.state !== "done" && k.state !== "dropped", el => el.child(this.prioChip(t, k)))
      .child(div().flex_none().max_w(120).truncate().text_size(11).text_color(k.state === "blocked" ? t.blocked : t.dim).child(right))
      .child(this.chev(t, "right"));
  }
  agentRow(t, a, i, d) {
    const ended = a.status === "ended", sign = !ended && SIGN[a.stay_sign];
    const what = a.task ? `#${a.task.id} ${a.task.title}` : ended ? [a.model, a.ended ? `ended ${hhmm(a.ended)}` : null].filter(Boolean).join(" · ") : a.stay ? `waits for ${a.stay}` : "no task";
    const right = ended ? "" : a.status === "working" ? "working" : a.status === "blocked" ? "needs you" : `idle ${ago(a.idle_s)}${a.fate?.short ? `: ${a.fate.short}` : ""}`;
    return this.row(t, `agent-${a.name}`, i, cx => this.push({ s: "agent", name: a.name }, cx))
      .child(this.dot(this.statusColor(t, a.status)).when(a.status === "working", el => el.loop("opacity", { from: 0.35, to: 1, period: 1400 })))
      .child(div().flex_none().font_semibold().text_color(ended ? t.muted : t.foreground).child(a.name))
      .child(div().flex_1().min_w(0).truncate().text_color(a.task ? t.muted : t.dim).child(what))
      .when(Boolean(sign), el => el.child(this.signChip(t, a)))
      .when(!sign && !ended && a.ctx_tokens >= HANDOFF, el => el.child(this.chip(t, "context full", t.ansi3, true)))
      .child(div().flex_none().text_size(11).text_color(a.status === "blocked" ? t.blocked : t.dim).child(right))
      .child(this.chev(t, "right"));
  }

  // What needs the user, most urgent first; each opens the screen where they can act on it.
  needs(t, d) {
    const s = this.s, out = [];
    if (d.watchdDead) out.push({ key: "watchd", title: "watchd is not running", detail: "Nothing is reaped, spawned or told until it runs again.", to: { s: "more", tab: "system" },
      acts: [["Restart watchd…", () => this.askWatchd(), true]] });
    if (d.redRun) {
      const r = d.redRun;
      out.push({ key: "ci", title: "main CI is red", detail: `Run ${r.id} failed at ${hhmm(iso(r.created))}${d.reds > 1 ? `; ${d.reds} red runs in a row` : ""}`,
        owner: d.fix ? `${d.fix.owner} is fixing it (#${d.fix.id})` : "Nobody is on it yet", to: { s: "more", tab: "system" },
        acts: [["Open run ↗", () => openUrl(r.url)], ["Re-run failed jobs…", () => this.askRerun(r.id), true]] });
    }
    for (const k of s.tasks.filter(k => k.state === "blocked"))
      out.push({ key: `t${k.id}`, title: `${k.owner} asks about #${k.id}`, detail: one(k.question) || k.title, owner: `#${k.id} ${k.title}`, to: { s: "task", id: k.id } });
    for (const a of d.live.filter(a => a.status === "blocked" && !s.tasks.some(k => k.state === "blocked" && k.owner === a.name)))
      out.push({ key: `a${a.name}`, title: `${a.name} stopped at a prompt`, detail: "Open its terminal and answer.", to: { s: "agent", name: a.name } });
    for (const a of d.live.filter(a => a.stay_sign === "hung"))
      out.push({ key: `h${a.name}`, title: `${a.name} is hung`, detail: SIGN.hung[1], to: { s: "agent", name: a.name }, nudge: a });
    if (s.machine?.high) out.push({ key: "mem", title: "The machine is short on memory", detail: (s.machine.line ?? "").replace(/^machine: /, ""), to: { s: "more", tab: "system" } });
    return out;
  }
  attention(t, d) {
    const n = this.needs(t, d);
    if (!n.length) return h_flex().h(38).flex_none().px(12).gap(10).items_center().rounded(10).bg(t.surface).border_1().border_color(t.border)
      .child(this.dot(t.ansi2)).child(div().text_size(12.5).child("Nothing needs you")).child(div().flex_1())
      .child(div().text_size(11).text_color(t.dim).child(this.at ? `checked ${hhmm(this.at / 1000)}` : ""));
    return this.group(t, "needs", true)
      .child(h_flex().h(32).px(12).gap(8).items_center().child(this.dot(t.blocked))
        .child(div().text_size(12.5).font_semibold().text_color(t.blocked).child("Needs you")).child(div().text_size(11).text_color(t.blocked).child(String(n.length))))
      .children(n.map(x => v_flex().id(`need-${x.key}`).px(12).py(9).gap(3).min_w(0).border_t(1).border_color(t.blocked + "33").cursor_pointer().hover(st => st.bg(t.blocked + "14"))
        .on_click((_e, cx) => this.push(x.to, cx))
        .child(h_flex().gap(8).items_center().min_w(0).child(div().flex_1().min_w(0).truncate().font_semibold().child(x.title)).child(this.chev(t, "right")))
        .child(div().text_size(12).line_height("17px").whitespace_normal().child(x.detail))
        .when(Boolean(x.owner), el => el.child(div().truncate().text_size(11).text_color(t.dim).child(x.owner)))
        .when(Boolean(x.acts || x.nudge), el => el.child(h_flex().pt(4).gap(8).flex_wrap()
          .when(Boolean(x.nudge), el => el.child(this.nudgeBtn(t, x.nudge)))
          .children((x.acts ?? []).map(([label, fn, danger], i) => (danger ? this.danger : this.btn).call(this, t, `need-${x.key}-${i}`, label, fn)))))));
  }

  // Rests for a minute after use (drawn at the next data refresh; no timer of its own).
  nudgeBtn(t, a) {
    const rests = Date.now() - (this.nudged.get(a.name) ?? 0) < 60000;
    return rests ? this.btn(t, `nudge-${a.name}`, "Nudged", () => {}).text_color(t.dim).tooltip("Rests for a minute after a nudge.")
      : this.btn(t, `nudge-${a.name}`, "Nudge", cx => this.nudge(cx, a)).tooltip("Types one line into its terminal: read your messages and continue, or say what you wait for.");
  }
  // The user's two staffing numbers, each with − and + (`swarm limits`), and the board's holding line.
  stepper(t, id, label, v, set) {
    const b = (k, ch, n) => div().id(`${id}-${k}`).size(22).flex().items_center().justify_center().rounded(5).text_size(13).text_color(t.muted).cursor_pointer()
      .hover(s => s.bg(t.hover).text_color(t.foreground)).on_click((_e, cx) => { cx.stop_propagation(); set(cx, Math.max(0, n)); }).child(ch);
    return h_flex().flex_none().gap(6).items_center()
      .child(div().text_size(11).text_color(t.muted).child(label))
      .child(h_flex().h(26).px(2).items_center().rounded(7).border_1().border_color(t.border).bg(t.background)
        .child(b("dn", "−", (v ?? this.s.limits.live) - 1))
        .child(div().w(22).flex().justify_center().text_size(12.5).font_semibold().child(v == null ? "–" : String(v)))
        .child(b("up", "+", v == null ? this.s.limits.live : v + 1)));
  }
  staffing(t) {
    // Pause sets the auto-spawn number to 0 and remembers it (Herdr's shared store, per board) for Resume.
    const l = this.s.limits ?? { live: 0 }, key = `swarm.resume:${this.s.db}`, saved = Number(shared(key)) || 0;
    return v_flex().gap(8).min_w(0)
      .child(h_flex().gap(12).items_center().flex_wrap().min_w(0)
        .child(this.stepper(t, "min", "Auto-spawn to", l.min, (cx, n) => this.act(cx, ["limits", "--min", String(n)])))
        .when(l.min > 0, el => el.child(this.btn(t, "pause", "Pause", cx => { setShared(key, l.min); this.act(cx, ["limits", "--min", "0"]); }).tooltip("Stops auto-spawn; running agents go on.")))
        .when(l.min === 0 && saved > 0, el => el.child(this.btn(t, "resume", `Resume (${saved})`, cx => this.act(cx, ["limits", "--min", String(saved)]))))
        .child(div().flex_1())
        .child(this.stepper(t, "max", "Max", l.max, (cx, n) => this.act(cx, ["limits", "--max", String(n)]))))
      .when(Boolean(l.held), el => el.child(div().text_size(11).line_height("15px").whitespace_normal().text_color(t.ansi3).child(`Auto-spawn is ${held(l.held)}`)));
  }

  // `swarm away --back`'s digest (state --json's `back`), on Home until dismissed or the next away.
  backCard(t) {
    const g = this.s.back, key = `swarm.back:${this.s.db}`;
    if (!g || this.s.away || shared(key) === g.back) return null;
    const dim = text => div().text_color(t.dim).child(text), wrap = text => div().line_height("17px").whitespace_normal().child(text);
    const word = g.ci && ({ success: "green", failure: "red" }[g.ci.conclusion] ?? g.ci.conclusion ?? g.ci.status ?? "?");
    const ci = g.ci ? h_flex().gap(6).items_center().child(this.dot(word === "green" ? t.ansi2 : word === "red" ? t.blocked : t.ansi3, 7)).child(word).child(this.mono(dim((g.ci.sha ?? "").slice(0, 7)).text_size(11))) : dim("no run seen");
    return v_flex().min_w(0)
      .child(this.title(t, "While you were away", `${hhmm(g.since)}–${hhmm(g.back)}${g.note ? ` · ${g.note}` : ""}`, this.more(t, "back-x", "Dismiss", cx => { setShared(key, g.back); cx.notify(); })))
      .child(this.facts(t, "g-back", [
        ["Questions", g.questions.length ? v_flex().gap(6).children(g.questions.map(q => v_flex().id(`back-q-${q.id}`).gap(1).min_w(0).cursor_pointer().hover(st => st.text_color(t.accent))
            .on_click((_e, cx) => this.push({ s: "task", id: q.id }, cx))
            .child(wrap(one(q.question) || q.title)).child(div().truncate().text_size(11).text_color(t.dim).child(`#${q.id} ${q.owner ?? ""} · asked ${hhmm(q.since)} ›`))))
          : dim("none wait")],
        g.done.length ? ["Finished", wrap(g.done.map(k => `#${k.id} ${k.title}`).join(" · "))] : null,
        g.merged.length ? ["Merged", wrap(g.merged.map(k => `PR #${k.pr ?? "?"} (#${k.id})`).join(" · "))] : null,
        ["main CI", ci],
        g.ended.length ? ["Ended", wrap(g.ended.map(a => `${a.name}${a.why ? ` (${a.why})` : ""}`).join(" · "))] : null,
        g.hung.length ? ["Hung", div().text_color(t.ansi3).child(g.hung.join(" · "))] : null,
      ]));
  }

  // ---- Home: what needs you, who is running and on what, what is left ---------------------------
  home(t, d) {
    const s = this.s, two = this.width >= 760;
    const rank = k => k.state === "blocked" ? 0 : k.state === "claimed" ? 1 : k.waiting ? 3 : 2;
    const left = s.tasks.filter(k => ["blocked", "claimed", "open"].includes(k.state)).sort((a, b) => rank(a) - rank(b) || this.prio(a) - this.prio(b) || a.id - b.id);
    const shown = left.slice(0, 7), nd = d.count("done"), ndrop = d.count("dropped"), total = s.tasks.length - ndrop;
    const agents = v_flex().min_w(0)
      .child(this.title(t, "Agents", s.limits?.max != null ? `${d.live.length} of ${s.limits.max}` : d.live.length,
        this.more(t, "all-agents", d.ended.length ? `All, ${d.ended.length} ended ›` : "All ›", cx => this.push({ s: "agents" }, cx))))
      .child(d.live.length ? this.group(t, "g-agents").children(d.live.map((a, i) => this.agentRow(t, a, i, d))) : this.empty(t, "No agents are running"));
    const tasks = v_flex().min_w(0)
      .child(this.title(t, "Tasks", `${nd} of ${total} done`, this.more(t, "all-tasks", "Board ›", cx => this.push({ s: "board", f: "active" }, cx))))
      .child(this.group(t, "g-tasks")
        .child(div().h(3).w_full().bg(t.selected).child(div().h(3).bg(t.ansi2).w(`${total ? (nd / total) * 100 : 0}%`)))
        .children(shown.map((k, i) => this.taskRow(t, k, i)))
        .when(!left.length, el => el.child(this.row(t, "none-left", 0).text_color(t.dim).child("Nothing left on the board")))
        .child(h_flex().h(34).px(12).gap(16).items_center().border_t(1).border_color(t.border)
          .when(left.length > shown.length, el => el.child(this.more(t, "left-more", `${left.length - shown.length} more ›`, cx => this.push({ s: "board", f: "active" }, cx))))
          .child(this.more(t, "done-link", `${nd} done ›`, cx => this.push({ s: "board", f: "done" }, cx)))
          .when(ndrop > 0, el => el.child(this.more(t, "drop-link", `${ndrop} dropped ›`, cx => this.push({ s: "board", f: "dropped" }, cx))))));
    const staff = v_flex().min_w(0).child(this.title(t, "Staffing")).child(this.group(t, "g-staff").px(12).py(10).child(this.staffing(t)));
    const back = this.backCard(t), att = back ? v_flex().gap(10).child(back).child(this.attention(t, d)) : this.attention(t, d);
    if (two) return h_flex().gap(16).items_start()
      .child(v_flex().gap(10).min_w(0).flex_grow(1).flex_basis(0).child(att).child(agents))
      .child(v_flex().gap(10).min_w(0).flex_grow(1).flex_basis(0).child(tasks).child(staff));
    return v_flex().gap(10).child(att).child(agents).child(tasks).child(staff);
  }

  // ---- Agents: running, the communicator, ended -------------------------------------------------
  agentsScreen(t, d) {
    const c = d.commsAgent;
    return v_flex().gap(10)
      .child(v_flex().child(this.title(t, "Running", d.live.length))
        .child(d.live.length ? this.group(t, "g-live").children(d.live.map((a, i) => this.agentRow(t, a, i, d))) : this.empty(t, "No agents are running")))
      .when(Boolean(c), el => el.child(v_flex().child(this.title(t, "Communicator", "your channel to the swarm; not counted")).child(this.group(t, "g-comms").child(this.agentRow(t, c, 0, d)))))
      .when(d.ended.length > 0, el => el.child(v_flex().child(this.title(t, "Ended", `${d.ended.length} · newest first`))
        .child(this.group(t, "g-ended").children(d.ended.slice(0, 60).map((a, i) => this.agentRow(t, a, i, d))))));
  }
  // ---- Board: every task, by state; a row opens the task ----------------------------------------
  board(t, d) {
    const s = this.s, f = this.r.f, by = st => s.tasks.filter(k => k.state === st).sort((a, b) => st === "done" || st === "dropped" ? 0 : this.prio(a) - this.prio(b) || a.id - b.id), open = by("open");
    const sets = (f === "active" ? [["Waiting on you", by("blocked")], ["In progress", by("claimed")], ["Ready", open.filter(k => !k.waiting)], ["Waiting on other tasks", open.filter(k => k.waiting)]]
      : [[f === "done" ? "Done" : "Dropped", by(f).reverse(), "newest first"]]).filter(([, ks]) => ks.length);
    // shortcut: 80 rows a group; a board with more done tasks than that needs a virtual list.
    const form = this.adding ? this.group(t, "new-task").px(12).py(10).gap(8)
      .child(div().text_size(12.5).font_semibold().child("New task"))
      .child(h_flex().child(this.field(t, "nt-title", this.in.title)))
      .child(h_flex().child(this.field(t, "nt-body", this.in.body)))
      .when(this.moreOpts, el => el.child(h_flex().gap(8).child(this.field(t, "nt-after", this.in.after)).child(this.field(t, "nt-model", this.in.model))))
      .child(h_flex().gap(8).items_center()
        .child(this.more(t, "nt-more", this.moreOpts ? "Fewer options" : "More options", cx => { this.moreOpts = !this.moreOpts; cx.notify(); })).child(div().flex_1())
        .child(this.btn(t, "nt-cancel", "Cancel", cx => { this.adding = false; cx.notify(); }))
        .child(this.btn(t, "nt-add", "Add task", cx => this.addTask(cx)).bg(t.solid).text_color(t.solid_foreground).border_color(t.solid)))
      : h_flex().child(this.btn(t, "nt-open", "+ New task", cx => { this.adding = true; this.in.title.focus(); cx.notify(); })).child(div().flex_1());
    return v_flex().gap(10)
      .child(form)
      .child(this.seg(t, "bf", [["active", "Active", by("blocked").length + by("claimed").length + open.length], ["done", "Done", by("done").length], ["dropped", "Dropped", by("dropped").length]], f,
        (id, cx) => { this.r.f = id; this.landed(cx); }))
      .children(sets.map(([label, ks, note]) => v_flex().child(this.title(t, label, note ? `${ks.length} · ${note}` : ks.length))
        .child(this.group(t, `g-${label}`).children(ks.slice(0, 80).map((k, i) => this.taskRow(t, k, i))))))
      .when(!sets.length, el => el.child(this.empty(t, f === "active" ? "Nothing left on the board" : `No ${f} tasks`)));
  }

  // ---- Task: everything the board knows about one task ------------------------------------------
  task(t, d) {
    const s = this.s, id = this.r.id, k = s.tasks.find(x => x.id === id);
    if (!k) return this.empty(t, `No task #${id} on this board`);
    const x = s.task?.id === id ? s.task : null, e = evidence(k.evidence), live = k.state === "claimed" || k.state === "blocked";
    const owner = k.owner ? s.agents.find(a => a.name === k.owner) : null, addr = owner && focusAddr(owner);
    const who = name => div().id(`who-${name}`).flex_none().font_semibold().cursor_pointer().hover(st => st.text_color(t.accent)).on_click((_e, cx) => this.push({ s: "agent", name }, cx)).child(name);
    const refs = ids => h_flex().gap(10).flex_wrap().children(ids.map(i => { const o = s.tasks.find(y => y.id === i);
      return h_flex().id(`ref-${i}`).gap(5).items_center().cursor_pointer().hover(st => st.text_color(t.accent)).on_click((_e, cx) => this.push({ s: "task", id: i }, cx))
        .child(this.dot(o ? this.taskColor(t, o) : t.dim, 6)).child(`#${i}`).child(div().text_color(t.dim).child(o ? this.taskWord(o) : "gone")); }));
    const dim = text => div().text_color(t.dim).child(text);
    const times = [k.queue_wait_s != null ? `queued ${ago(k.queue_wait_s)}` : null, k.work_s != null ? `worked ${ago(k.work_s)}` : null, k.blocked_s ? `blocked ${ago(k.blocked_s)}` : null].filter(Boolean);
    const facts = [
      k.owner ? [k.state === "done" ? "Done by" : "Owner", h_flex().gap(8).items_center().child(who(k.owner))
        .when(live && k.lease_left != null, el => el.child(dim(k.lease_left > 0 ? `lease ${ago(k.lease_left)} left` : "lease expired")))] : ["Owner", dim(k.state === "open" ? "nobody yet" : "nobody")],
      k.state === "open" || live ? ["Priority", this.seg(t, "t-prio", [0, 1, 2, 3].map(n => [n, `P${n}`]), this.prio(k),
        (n, cx) => n !== this.prio(k) && this.act(cx, ["task", "priority", String(k.id), String(n)]))] : null,
      ["Added", h_flex().gap(8).child(k.created_by ?? "?").when(Boolean(k.created_at), el => el.child(dim(hhmm(k.created_at))))],
      k.deps.length ? ["Waits on", refs(k.deps)] : null,
      k.blocks?.length ? ["Holds back", refs(k.blocks)] : null,
      times.length ? ["Time", times.join(" · ")] : null,
      k.claims > 1 || k.releases ? ["Claims", `${k.claims} by ${k.holders.join(", ")}${k.releases ? ` · released ${k.releases}×` : ""}`] : null,
      k.model || k.effort || k.base ? ["Runs as", [k.model, k.effort, k.base ? `lands on ${k.base}` : null].filter(Boolean).join(" · ")] : null,
      k.evidence ? ["Evidence", v_flex().gap(5).min_w(0)
        .child(h_flex().gap(6).items_center()
          .when(Boolean(k.pr), el => el.child(this.btn(t, "open-pr", `PR #${k.pr} ↗`, () => exec("gh", ["pr", "view", String(k.pr), "--web"], { cwd: this.cwd, on: this.on }))))
          .when(!k.pr && Boolean(e.chip), el => el.child(this.chip(t, e.chip, t.ansi2)))
          .when(Boolean(e.sha), el => el.child(this.mono(div().text_size(11).text_color(t.muted).child(e.sha))))
          .when(Boolean(k.ci_conclusion), el => el.child(this.chip(t, `CI ${k.ci_conclusion}`, k.ci_conclusion === "success" ? t.ansi2 : t.blocked))))
        .child(div().line_height("17px").whitespace_normal().text_color(t.muted).child(k.evidence))] : null,
    ].filter(Boolean);
    const says = { "task-add": "added it", claim: "claimed it", spawn: "was started for it", done: "finished it", unblock: "was unblocked", release: "gave it back", drop: "dropped it" };
    return v_flex().gap(12)
      .child(v_flex().gap(7).px(2)
        .child(h_flex().gap(8).items_center().child(this.chip(t, this.taskWord(k), this.taskColor(t, k), true)).child(div().text_size(11).text_color(t.dim).child(`#${k.id}`)))
        .child(div().text_size(16).line_height("22px").font_semibold().whitespace_normal().child(k.title))
        .when(live || k.state === "open", el => el.child(h_flex().pt(3).gap(8).flex_wrap()
          .when(live && Boolean(addr), el => el.child(this.btn(t, "t-focus", `Open ${k.owner}'s terminal ↗`, () => run("agent.focus", { terminal: addr }))))
          .when(live && Boolean(k.owner), el => el.child(this.danger(t, "t-release", "Release task…", () => this.askRelease(k))))
          .child(this.danger(t, "t-drop", "Drop task…", () => this.askDrop(k))))))
      .when(k.state === "blocked", el => el.child(this.group(t, "t-q", true).px(12).py(10).gap(5)
        .child(div().text_size(11).font_semibold().text_color(t.blocked).child(`${k.owner} asks`))
        .child(div().line_height("18px").whitespace_normal().child(k.question ?? ""))
        .child(div().text_size(11).line_height("15px").whitespace_normal().text_color(t.dim).child("Answer in its terminal, or tell the communicator; the task moves again once it is unblocked."))))
      .when(Boolean(k.answer), el => el.child(this.group(t, "t-a").px(12).py(10).gap(5)
        .child(div().text_size(11).font_semibold().text_color(t.muted).child("Answered")).child(div().line_height("18px").whitespace_normal().child(k.answer ?? ""))))
      .child(this.facts(t, "t-facts", facts))
      .child(v_flex().child(this.title(t, "Description"))
        .child(x?.body ? this.group(t, "t-body").px(12).py(8).child(TextView.markdown(`body-${id}`, x.body))
          : this.empty(t, x ? "No description: the title is the whole task" : "…")))
      .when(x?.messages.length > 0, el => el.child(v_flex().child(this.title(t, "Messages about it", x.messages.length))
        .child(this.group(t, "t-msgs").children(x.messages.map((m, i) => v_flex().px(12).py(8).gap(3).min_w(0).when(i > 0, el => el.border_t(1).border_color(t.border))
          .child(h_flex().gap(8).text_size(11).text_color(t.dim).child(hhmm(m.ts)).child(div().text_color(t.muted).child(`${m.frm} → ${m.dest === "all" ? "everyone" : m.dest}`)))
          .child(div().text_size(12).line_height("17px").whitespace_normal().child(shortUrls(one(m.body)).text)))))))
      .when(x?.events.length > 0, el => el.child(v_flex().child(this.title(t, "History"))
        .child(this.group(t, "t-hist").children(x.events.map((ev, i) => this.row(t, `t-ev-${i}`, i).h(30).text_size(12)
          .child(div().w(34).flex_none().text_size(11).text_color(t.dim).child(hhmm(ev.ts)))
          .child(div().flex_none().child(ev.agent ?? "swarm"))
          .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(says[ev.kind] ?? (ev.kind === "block" ? `asked: ${one(ev.data).replace(/^#\d+\s*/, "")}` : ev.kind))))))));
  }

  moreScreen(t, d) {
    const tab = this.r.tab;
    return v_flex()
      .child(div().px(16).child(this.seg(t, "more", [["activity", "Activity"], ["system", "System"]], tab, (id, cx) => { this.r.tab = id; this.landed(cx); })))
      .when(tab === "activity", el => el.child(div().px(16).pt(10).child(this.filters(t, d))))
      .child(tab === "activity" ? this.activity(t, d) : this.system(t, d));
  }

  // Activity: Summary | Full log first, the filters, then the key's toggle at the end.
  filters(t, d) {
    const opts = [["all", "All"], ["you", "Needs you", this.actRows(t, d, "you").length], ["tasks", "Tasks"], ["code", "Code"], ["agents", "Agents"], ["messages", "Messages"], ["machine", "Machine"]];
    const pill = (id, label, on, pick) => h_flex().id(id).h(24).px(9).gap(5).items_center().rounded(6).border_1().border_color(t.border)
      .bg(on ? t.selected : t.background).text_size(11).text_color(on ? t.foreground : t.muted).cursor_pointer().hover(st => st.bg(t.hover))
      .on_click((_e, cx) => { pick(); cx.notify(); }).child(label);
    return h_flex().gap(4).items_center().flex_wrap()
      .child(pill("v-sum", "Summary", !this.actLog, () => { this.actLog = false; }).tooltip("What happened, in plain words. Routine events are left to the full log."))
      .child(pill("v-log", "Full log", Boolean(this.actLog), () => { this.actLog = true; }).mr(8).tooltip("Every event and message, with its raw kind. Nothing folded or hidden."))
      .children(opts.map(([id, label, n]) => pill(`f-${id}`, label, id === this.actFilter, () => { this.actFilter = id; })
        .when(n > 0, el => el.child(div().text_size(11).text_color(id === "you" ? t.blocked : t.dim).child(String(n))))))
      .child(div().flex_1()).child(this.more(t, "key-toggle", this.open.key ? "Hide key" : "What these mean", cx => { this.open.key = !this.open.key; cx.notify(); }).pl(8));
  }

  fileRow(t, f) {
    const i = f.lastIndexOf("/") + 1;
    return this.mono(h_flex().h(18).min_w(0).text_size(11).truncate()
      .child(div().flex_none().text_color(t.dim).child(f.slice(0, i))).child(div().truncate().min_w(0).text_color(t.muted).child(f.slice(i))));
  }

  // ---- Agent: one agent, what it is on and what it did ----------------------------------------
  agentScreen(t, d) {
    const s = this.s, a = s.agents.find(x => x.name === this.r.name);
    if (!a) return this.empty(t, `No agent ${this.r.name} in this swarm`);
    const isComms = a.name === d.comms, ended = a.status === "ended", addr = focusAddr(a), sign = !ended && SIGN[a.stay_sign];
    const task = a.task && s.tasks.find(k => k.id === a.task.id), n = a.ctx_tokens;
    const branch = a.branch ?? (a.worktree ? base(a.worktree) : isComms ? "main" : null);
    const pr = branch && this.prs?.find(p => p.headRefName === branch), push = a.events?.find(e => e.kind === "push");
    const msgs = (a.messages ?? []).slice(0, 6), tl = (a.events ?? []).slice(0, 10);
    const done = s.tasks.filter(k => k.state === "done" && k.owner === a.name).reverse();
    const state = ended ? `ended ${a.ended ? hhmm(a.ended) : ""}` : a.status === "idle" ? `${a.stay ? "waiting" : "idle"} ${ago(a.idle_s)}` : a.status === "blocked" ? "needs you" : a.status;
    const dim = text => div().text_color(t.dim).child(text);
    const left = !ended && a.cache === "warm" && a.cold_at ? a.cold_at - s.now : null;
    return v_flex().gap(12)
      .child(v_flex().gap(8).px(2)
        .child(h_flex().gap(8).items_center().min_w(0)
          .child(this.dot(this.statusColor(t, a.status), 9).when(a.status === "working", el => el.loop("opacity", { from: 0.35, to: 1, period: 1400 })))
          .child(div().flex_none().text_size(16).font_semibold().child(a.name))
          .child(div().flex_none().text_color(a.status === "blocked" ? t.blocked : t.muted).child(state))
          .when(Boolean(a.role), el => el.child(div().min_w(0).flex_shrink(1).overflow_hidden().child(this.chip(t, a.role, t.ansi4, true)))))
        .when(!ended, el => el.child(h_flex().gap(8)
          .when(Boolean(addr), el => el.child(this.btn(t, "a-focus", "Open terminal ↗", () => run("agent.focus", { terminal: addr }))))
          .when(a.stay_sign === "hung" || (a.status === "idle" && Boolean(a.task)), el => el.child(this.nudgeBtn(t, a)))
          .when(!isComms, el => el.child(this.danger(t, "a-end", "End agent…", () => this.askEnd(a)))))
          .child(h_flex().gap(8).items_center().child(this.field(t, "a-msg", this.in.msg))
            .child(this.tick(t, "a-urgent", "Urgent", this.urgent, cx => { this.urgent = !this.urgent; cx.notify(); }).tooltip("Wakes it at once, even with a cold cache."))
            .child(this.btn(t, "a-send", "Send", cx => this.sendMsg(cx))))))
      .when(Boolean(sign), el => el.child(this.group(t, "a-sign", sign[2]).px(12).py(10).child(div().line_height("17px").whitespace_normal().text_color(sign[2] ? t.foreground : t.ansi3).child(sign[1]))))
      .child(v_flex().child(this.title(t, "Working on"))
        .child(task ? this.group(t, "a-task", task.state === "blocked").child(this.taskRow(t, task, 0))
            .when(task.state === "blocked", el => el.child(div().px(12).pb(10).line_height("17px").whitespace_normal().child(one(task.question))))
          : this.empty(t, isComms ? "No task: the communicator is your channel to the swarm" : a.stay ? `No task: it waits for ${a.stay}` : "No task")))
      // state --json's fate: watchd's verdict on an idle agent and each check behind it; the panel never re-derives it.
      .when(Boolean(a.fate), el => el.child(v_flex().child(this.title(t, a.fate.verdict === "end" ? "Why it is about to end" : "Why it is still here", "watchd's own checks"))
        .child(this.group(t, "a-fate")
          .child(div().px(12).py(9).line_height("17px").whitespace_normal().child(a.fate.says))
          .children(a.fate.checks.map((c, i) => this.row(t, `a-fate-${i}`, 1).h(30).text_size(12)
            .child(this.dot(c.on ? t.ansi3 : t.selected, 7))
            .child(div().flex_none().text_color(c.on ? t.foreground : t.dim).child(c.label))
            .child(div().flex_1().min_w(0).truncate().text_right().text_color(t.dim).child(c.detail ?? ""))
            .when(c.label === "Stays" && c.on && !isComms, el => el.child(this.danger(t, "a-stay-end", "End its stay…", () => this.askStayEnd(a)).h(22))))))))
      .child(this.facts(t, "a-facts", [
        a.stay ? ["Waits for", a.stay] : null,
        ["Model", [a.model ?? "?", a.started ? `started ${hhmm(a.started)}` : null, a.hc ? `terminal ${a.hc}` : null].filter(Boolean).join(" · ")],
        ["Context", v_flex().gap(7)
          .child(h_flex().gap(8).child(div().font_semibold().child(n ? kilo(n) : "–"))
            .child(dim(!n ? "no reading for this session" : n >= HANDOFF ? "past 550k: compacting; it releases the task if it loses the thread" : n >= FINISH ? "past 350k: it finishes and takes no new task" : "takes new tasks up to 350k")))
          .when(n > 0, el => el.child(h_flex().h(6).child(this.ctxBar(t, `det-${a.name}`, n, true))))],
        !ended ? ["Cache", a.cold_guarded ? "cold: messages wait in its inbox" : a.cache === "warm" ? `warm${left > 0 ? `, cold in ${ago(left)}` : ""}` : "cold"] : null,
        ["Branch", h_flex().gap(8).min_w(0).child(this.mono(div().flex_none().text_size(11.5).child(branch ?? "–"))).child(dim(a.worktree ? "its own worktree" : "the main checkout"))
          .when(Boolean(push), el => el.child(div().truncate().min_w(0).text_color(t.dim).child(`pushed ${hhmm(push?.ts ?? 0)}`)))],
        ["Pull request", pr ? this.prRow(t, pr, false).px(0) : dim(this.prs == null ? (this.prLoading ? "…" : "unknown (gh is not available here)") : "none open from this branch")],
      ]))
      .when(a.files.length > 0, el => el.child(v_flex().child(this.title(t, "Files it is editing", a.files.length))
        .child(this.group(t, "a-files").px(12).py(8).children(a.files.slice(0, 12).map(f => this.fileRow(t, f))))))
      .when(msgs.length > 0, el => el.child(v_flex().child(this.title(t, "Messages"))
        .child(this.group(t, "a-msgs").children(msgs.map((m, i) => v_flex().px(12).py(8).gap(3).min_w(0).when(i > 0, el => el.border_t(1).border_color(t.border))
          .child(h_flex().gap(8).items_center().text_size(11).text_color(t.dim).child(hhmm(m.ts))
            .child(div().text_color(t.muted).child(m.frm === a.name ? `to ${m.dest === "all" ? "everyone" : m.dest}` : `from ${m.frm}`))
            .when(Boolean(m.urgent), el => el.child(this.chip(t, "urgent", t.blocked, true))))
          .child(div().text_size(12).line_height("17px").whitespace_normal().child(shortUrls(one(m.body)).text)))))))
      .when(done.length > 0, el => el.child(v_flex().child(this.title(t, "Finished", done.length))
        .child(this.group(t, "a-done").children(done.slice(0, 20).map((k, i) => this.taskRow(t, k, i))))))
      .when(tl.length > 0, el => el.child(v_flex().child(this.title(t, "Latest"))
        .child(this.group(t, "a-tl").children(tl.map((e, i) => { const l = evLine(e); return this.row(t, `a-ev-${i}`, i).h(30).text_size(12)
          .child(div().w(34).flex_none().text_size(11).text_color(t.dim).child(hhmm(e.ts)))
          .child(div().flex_1().min_w(0).truncate().text_color(l.red ? t.blocked : t.muted).child(`${l.text}${l.sub ? ` · ${l.sub}` : ""}`)); })))));
  }

  // ---- Activity tab -------------------------------------------------------------------------
  // Summary: one plain sentence per event, problems in color, routine noise left to the log. A post fanned
  // out to N agents is one row, a memory-pressure episode is one row, and FOLD runs fold into one.
  // Log: every event and message state --json sent, with its raw kind, nothing folded.
  actRows(t, d, filter, log = false) {
    const items = this.actItems(d, log);
    return items.filter(i => filter === "all" || (filter === "you" ? KIND[i.kind].level === "you" && i.open : KIND[i.kind].group === filter));
  }
  // Render only reads these: refresh() builds both lists once per snapshot, because Herdr's engine
  // interrupts a render that builds them in the frame.
  actItems(d, log) { return this.acts?.[Number(log)] ?? []; }
  buildActs(d, log) {
    const s = this.s;
    const items = [], groups = new Map();
    for (const m of s.messages) {
      const kind = m.urgent ? "urgent" : m.kind === "system" || m.kind === "notice" ? "notice" : m.kind === "all" ? "all" : "msg";
      if (!log && !KIND[kind].show) continue;
      const g = `${m.frm}|${m.ts}|${m.body}`;
      if (groups.has(g)) { groups.get(g).dests.push(m.dest); continue; }
      const it = { key: `m${m.id}`, ts: m.ts, who: m.frm, kind, raw: m.kind, dests: [m.dest], ...(log ? { text: one(m.body) } : shortUrls(one(m.body))) };
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
    if (!log) this.foldAsks(items);
    return items;
  }

  // One block is up to four events within a minute: the agent's "asked you", the task's "waiting on you",
  // the swarm's notice to the comms and the agent's own message about the task. The ask row keeps them in
  // its tooltip; the full log keeps them as rows.
  foldAsks(items) {
    for (const b of items.filter(i => i.kind === "block" && i.task)) {
      const near = i => i !== b && Math.abs(i.ts - b.ts) <= 60 && (i.kind === "task-blocked" && i.task === b.task
        || i.who === "swarm" && i.text.includes(`${b.who} is blocked on #${b.task}`)
        || i.who === b.who && KIND[i.kind].group === "messages" && i.text.includes(`#${b.task}`));
      const folded = items.filter(near);
      if (!folded.length) continue;
      b.full = [b, ...folded].map(i => `${i.who} ${i.text}${i.meta ? ` (${i.meta})` : ""}`);
      for (const i of folded) items.splice(items.indexOf(i), 1);
    }
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
      case "block": return { text: `asked you about #${m?.[1]}: ${shortUrls(m?.[2] ?? "").text}`, task: m?.[1], open: task(m?.[1])?.state === "blocked" };
      case "task-blocked": return { text: `#${e.path} is waiting on you: ${shortUrls(data).text}`, task: e.path, open: task(e.path)?.state === "blocked" };
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
      case "takeover": return { text: "moved to another terminal" };
      case "end": return { text: "ended", part: e.agent ?? "?" };
      case "pressure": return { text: "machine is short on memory", open: true };
      case "orphan-kill": return { text: `left a process running; the swarm stopped it: ${data.split(" ").slice(1, -1).join(" ")}` };
      case "spawn-held": return { text: SAYS[kind](data), open: Boolean(s.limits?.held) };
      case "stay-hung": case "stay-nowaiter": case "stay-unwoken":
        return { text: SAYS[kind](data), open: s.agents.find(a => a.name === e.agent)?.stay_sign === kind.slice(5) };
      default: return { text: SAYS[kind]?.(data) ?? data };
    }
  }

  actColor(t, i) {
    const lv = KIND[i.kind].level;
    return lv === "you" ? (i.open === false ? t.dim : t.blocked) : lv === "warn" ? (i.open === false ? t.muted : t.ansi3) : lv === "good" ? t.ansi2 : t.muted;
  }
  icon(t, i, n = 14) {
    return this.iconDir ? svg(`${this.iconDir}/${KIND[i.kind].icon}.svg`).size(n).flex_none().text_color(this.actColor(t, i)) : div().size(n).flex_none();
  }

  // One row: time, icon, who, (log: raw kind), what, then a tail (needs you / answered / ongoing / PR) and
  // to whom. Summary rows wrap to their whole text, the log stays one line per event. Returns { h, el }.
  // The tooltip says what the kind means and whether you act; a folded row adds each event it holds. It is a
  // card pinned under the row's left edge and no wider than the row: the native tooltip follows the pointer
  // and, near the window's right edge, flips left past the panel.
  actRow(t, d, i, log) {
    const W = this.width, narrow = W < 520, fold = W < 640, k = KIND[i.kind], hot = k.level === "you" && i.open;
    const who = i.who === d.comms ? `${i.who} (comms)` : i.who, whoW = W < 760 ? 80 : 118;
    const text = `${fold ? i.who + " " : ""}${i.text}${i.sub ? ` — ${i.sub}` : ""}`;
    const tip = `${k.label}: ${k.what}${i.full?.length > 1 ? `\n\n${i.full.join("\n")}` : log && text.length > 70 ? `\n\n${text}` : ""}`;
    const [tailText, tailEl] = log ? [] : hot ? ["needs you", this.chip(t, "needs you", t.blocked, true)]
      : k.level === "you" ? ["answered", div().flex_none().text_size(11).text_color(t.dim).child("answered")]
      : k.level === "warn" && i.open ? (x => [x, this.chip(t, x, t.ansi3)])(i.kind === "pressure" || i.kind === "spawn-held" ? "ongoing" : "unresolved")
      : i.chip ? [i.chip, this.chip(t, i.chip, i.chip.startsWith("PR") ? t.ansi2 : null)] : [];
    const meta = i.meta && !narrow && (!tailEl || k.group === "messages") ? i.meta : null;
    // Text column: panel minus border, list and row padding, a scrollbar's room, time, icon, who and tails;
    // glyphs at 11.5px measured 5.1-5.4 wide on average in 320-860 shots; 5.6 errs high, never low (6.1 at 12.5px).
    const textW = W - 2 - 12 - 20 - 8 - (34 + 10) - (14 + 10) - (fold ? 0 : whoW + 10) - (log && !narrow ? 106 : 0)
      - (tailText ? tailText.length * 6 + 22 : 0) - (meta ? meta.length * 6 + 10 : 0);
    const n = log ? 1 : wrapLines(text, textW, 6.1), h = n * 17 + 10;
    const lead = el => el.h(17).flex().items_center();
    const el = h_flex().id(`act-${i.key}`).h(h).px(10).py(5).gap(10).items_start().w_full().min_w(0).rounded(6)
      .when(hot, el => el.bg(t.blocked + "14")).hover(st => st.bg(hot ? t.blocked + "1f" : t.surface))
      .child(lead(div().w(34).flex_none().text_size(11).text_color(t.dim)).child(hhmm(i.ts)))
      .child(lead(div().flex_none()).child(this.icon(t, i)))
      .when(!fold, el => el.child(lead(div().w(whoW).flex_none().min_w(0)).child(div().truncate().text_size(11).text_color(t.muted).child(who))))
      .when(log && !narrow, el => el.child(lead(div().w(96).flex_none().min_w(0)).child(this.mono(div().truncate().text_size(11).text_color(t.dim).child(i.raw)))))
      .child(div().flex_1().min_w(0).line_height("17px").text_size(12.5).when(log, el => el.truncate()).when(!log, el => el.whitespace_normal())
        .text_color(hot || (k.level === "warn" && i.open !== false) || k.group === "messages" ? t.foreground : t.muted).child(text))
      .when(Boolean(tailEl), el => el.child(lead(div().flex_none()).child(tailEl)))
      .when(Boolean(meta), el => el.child(lead(div().flex_none().text_size(11).text_color(t.dim)).child(meta)));
    const card = v_flex().max_w(W - 48).px(8).py(6).gap(2).rounded(6).bg(t.surface).border_1().border_color(t.border)
      .text_size(11).line_height("16px").children(tip.split("\n").map(l => l ? div().whitespace_normal().child(l) : div().h(4)));
    return { h, el: HoverCard.new(`tip-${i.key}`).anchor("top_left").open_delay(500).trigger(el).content(card) };
  }

  // The key: each kind on screen with its icon, name and meaning (the row tooltips say the same).
  actKey(t, items) {
    const kinds = Object.keys(KIND).filter(k => items.some(i => i.kind === k));
    return this.group(t, "act-key").mx(10).mb(8).px(12).py(10).gap(6)
      .child(h_flex().gap(8).items_center().child(div().text_size(12.5).font_semibold().child("What these mean"))
        .child(div().text_size(11).text_color(t.dim).child("kinds in this view")).child(div().flex_1())
        .child(this.more(t, "key-hide", "Hide", cx => { this.open.key = false; cx.notify(); })))
      .when(!kinds.length, el => el.child(div().text_size(11).text_color(t.dim).child("Nothing in this view")))
      .children(kinds.map(k => h_flex().items_start().gap(10).min_w(0)
        .child(div().pt(1).flex_none().child(this.icon(t, { kind: k, open: true })))
        .child(div().w(this.width < 520 ? 92 : 124).flex_none().text_size(12).child(KIND[k].label))
        .child(div().flex_1().min_w(0).whitespace_normal().line_height("16px").text_size(11).text_color(t.muted).child(KIND[k].what))));
  }

  activity(t, d) {
    const log = Boolean(this.actLog), all = this.actRows(t, d, this.actFilter, log), rows = [];
    let hour = null;
    // shortcut: 120 rows; 200 overran Herdr's render deadline on a loaded machine. Upgrade: a virtual list.
    for (const i of all.slice(0, 120)) {
      const h = hhmm(i.ts).slice(0, 2);
      if (h !== hour) {
        hour = h;
        rows.push({ key: `hr${i.ts}`, h: 28, el: h_flex().h(28).px(10).pt(8).gap(10).items_center().text_size(11).text_color(t.dim).child(`${h}:00`).child(div().flex_1().h(1).bg(t.border)) });
      }
      rows.push({ key: i.key, ...this.actRow(t, d, i, log) });
    }
    if (!rows.length) rows.push({ key: "none", h: 30, el: div().px(10).py(8).text_size(12).text_color(t.dim).child(this.actFilter === "you" ? "Nothing needs you right now." : "Nothing here yet") });
    return div().px(6).pt(6).pb(8).when(Boolean(this.open.key), el => el.child(this.actKey(t, all)))
      .child(this.list(`act-${log ? "log" : "sum"}-${this.actFilter}`, rows));
  }

  // ---- System tab ---------------------------------------------------------------------------
  prRow(t, p, withAgent) {
    const r = p.statusCheckRollup ?? [];
    const c = !r.length ? null : r.some(c => ["FAILURE", "ERROR", "CANCELLED", "TIMED_OUT"].includes(c.conclusion ?? c.state)) ? ["failing", t.blocked]
      : r.some(c => c.status && c.status !== "COMPLETED" || c.state === "PENDING") ? ["running", t.ansi3] : ["passing", t.ansi2];
    const agent = withAgent && this.s.agents.find(a => (a.branch ?? base(a.worktree)) === p.headRefName);
    return h_flex().id(`pr-${p.number}`).h(30).px(12).gap(8).items_center().text_size(12).min_w(0).cursor_pointer().hover(s => s.bg(t.hover))
      .on_click((_e, cx) => { cx.stop_propagation(); openUrl(p.url); })
      .child(div().text_color(t.dim).flex_none().child(`#${p.number}`))
      .child(div().flex_1().min_w(0).truncate().child(p.title))
      .when(withAgent, el => el.child(div().flex_none().max_w(90).truncate().text_size(11).text_color(agent ? t.foreground : t.dim).child(agent ? agent.name : p.headRefName)))
      .when(p.isDraft, el => el.child(this.chip(t, "draft")))
      .when(p.reviewDecision === "APPROVED", el => el.child(this.chip(t, "approved", t.ansi2)))
      .when(p.reviewDecision === "CHANGES_REQUESTED", el => el.child(this.chip(t, "changes", t.ansi3)))
      .when(Boolean(c), el => el.child(this.chip(t, c[0], c[1], true)));
  }

  // Each part is a titled group, as on the other screens; a problem here also shows in Needs you.
  system(t, d) {
    const s = this.s, m = s.machine, two = this.width >= 700, small = this.width < 520;
    const part = (label, note, right, g) => v_flex().min_w(0).child(this.title(t, label, note, right)).child(g);
    const dim = text => div().text_size(11).text_color(t.dim).child(text), lab = text => div().flex_none().text_size(11).text_color(t.dim).child(text);
    const pad = (id, red) => this.group(t, id, red).px(12).py(10).gap(6);
    const line = (key, i, open) => this.row(t, key, i, open).h(30).text_size(12);
    const red = d.reds > 0, runs = d.runs;
    const ci = part("CI on main", red ? `${plural(d.reds, "red run")} in a row` : !s.ci ? "" : "from watchd's polls", d.ci && this.chip(t, d.ci[0], t[d.ci[1]], true),
      !runs.length ? this.empty(t, s.ci ? "No runs seen on main yet" : "No CI data: this swarm's CLI is older than the panel")
      : this.group(t, "ci", red)
        .children(runs.map((r, i) => {
          const live = r.status !== "completed", bad = !live && r.conclusion !== "success", n = d.told(r.id);
          return line(`run-${r.id}`, i, () => openUrl(r.url))
            .child(div().w(12).flex_none().text_color(live ? t.ansi3 : r.conclusion === "failure" ? t.blocked : bad ? t.dim : t.ansi2).child(live ? "●" : r.conclusion === "failure" ? "✕" : bad ? "–" : "✓"))
            .child(div().w(34).flex_none().text_size(11).text_color(t.dim).child(hhmm(iso(r.created))))
            .child(this.mono(div().flex_none().text_size(11.5).child(String(r.id))))
            .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(`${live ? r.status.replace("_", " ") : r.conclusion ?? "?"}${n ? ` · told ${plural(n, "agent")}` : ""}`))
            .child(dim("Open run ↗"));
        }))
        .when(red, el => el.child(h_flex().px(12).py(8).gap(8).items_center().min_w(0).border_t(1).border_color(t.border)
          .child(d.fix ? h_flex().id("ci-owner").flex_1().min_w(0).gap(6).text_size(12).cursor_pointer().hover(st => st.text_color(t.accent)).on_click((_e, cx) => this.push({ s: "agent", name: d.fix.owner }, cx))
              .child(div().flex_none().font_semibold().child(d.fix.owner)).child(div().truncate().min_w(0).text_color(t.muted).child(`is fixing it: #${d.fix.id} ${d.fix.title}`))
            : div().flex_1().min_w(0).text_size(12).text_color(t.muted).child("Nobody is on it yet"))
          .child(this.danger(t, "ci-rerun", "Re-run failed jobs…", () => this.askRerun(d.redRun.id))))));
    const w = s.watchd, wOk = w?.alive && !w.stale;
    const watchd = part("watchd", "the swarm's daemon: reaps, spawns, tells", w ? this.chip(t, !w.alive ? "not running" : w.stale ? "older than the code" : "running", !w.alive ? t.blocked : w.stale ? t.ansi3 : t.ansi2, !wOk) : null,
      !w ? this.empty(t, s.watchd === undefined ? "No watchd reading: this swarm's CLI is older than the panel" : "No watchd has run for this swarm")
      : pad("watchd", !w.alive)
        .child(div().text_size(12).line_height("17px").whitespace_normal().text_color(wOk ? t.muted : t.foreground)
          .child(!w.alive ? `watchd (pid ${w.pid}) is not running: nothing is reaped, spawned or told until it runs again.`
            : `${w.stale ? "The swarm's code changed after this watchd started; restart it to run the new code. " : ""}pid ${w.pid}${w.started ? ` · started ${hhmm(w.started)}` : ""}${w.terminal ? ` · terminal ${w.terminal}` : ""}`))
        .when(Boolean(w.flags?.length), el => el.child(this.mono(div().truncate().text_size(11).text_color(t.dim).child(`watchd ${w.flags.join(" ")}`))))
        .child(h_flex().pt(2).child(this.danger(t, "watchd-restart", "Restart watchd…", () => this.askWatchd()))));
    const prs = part("Pull requests", this.prs ? `${this.prs.length} open` : "", null,
      !this.prs?.length ? this.empty(t, this.prs ? "No open PRs" : this.prLoading ? "…" : "No PR data (gh is not available here)")
      : this.group(t, "prs").children(this.prs.map((p, i) => this.prRow(t, p, true).when(i > 0, el => el.border_t(1).border_color(t.border)))));
    const c = d.commsAgent, refused = (s.events ?? []).filter(e => e.kind === "spawn-refused").slice(0, 3);
    const staff = part("Staffing", `${d.live.length} running`, s.limits?.held ? this.chip(t, "holding", t.ansi3, true) : null,
      pad("staff").gap(8).child(this.staffing(t))
        .children(refused.map(e => h_flex().h(20).gap(8).items_center().text_size(11).min_w(0)
          .child(div().w(34).flex_none().text_color(t.dim).child(hhmm(e.ts)))
          .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(`${e.agent} ${evLine(e).text}`))))
        .child(h_flex().pt(8).gap(8).items_center().text_size(12).min_w(0).border_t(1).border_color(t.border).child(lab("Communicator"))
          .child(d.comms ? div().flex_none().font_semibold().child(d.comms) : dim("none recorded"))
          .child(div().truncate().min_w(0).text_size(11).text_color(t.dim).child(d.comms ? ["not counted", c?.hc ? `terminal ${c.hc}` : null, c?.started ? `started ${hhmm(c.started)}` : null].filter(Boolean).join(" · ") : "")))
        .child(div().text_size(11).line_height("15px").whitespace_normal().text_color(t.dim)
          .child("Auto-spawn staffs startable tasks up to the first number; every spawn refuses at the max. Pause stops auto-spawn and keeps the running agents.")));
    const tile = (label, value, color) => v_flex().flex_1().min_w(0).px(10).py(8).gap(3).rounded(8).bg(t.background).border_1().border_color(t.border)
      .child(lab(label)).child(div().text_size(16).font_semibold().text_color(color ?? t.foreground).child(value));
    const gb = kb => (kb / 1048576).toFixed(1);
    // Memory per owner, measured: each agent's whole process tree, then other claude sessions on this machine.
    const costly = (s.costly ?? []).slice(0, 4), run = s.running ?? [], here = run.filter(j => !j.machine), away = run.filter(j => j.machine);
    const most = Math.max(1, ...here.map(j => j.rss_kb ?? 0));
    const machine = part("Machine", this.on ? this.on : "this computer", m ? this.chip(t, m.high ? "pressure" : "ok", m.high ? t.blocked : t.ansi2, m.high) : null,
      !m ? this.empty(t, "No machine reading")
      : pad("machine", m.high).gap(9)
        .child(h_flex().gap(6).text_size(12).child(div().text_color(t.muted).child("Memory")).child(div().flex_1()).child(`${gb(m.avail_kb)}G free`).child(div().text_color(t.dim).child(`of ${gb(m.total_kb)}G`)))
        .child(div().relative().h(6).rounded(3).bg(t.selected).child(div().absolute().left(0).top(0).h(6).rounded(3).bg(t.muted).w(`${Math.round((1 - m.avail_kb / m.total_kb) * 100)}%`)))
        .child(h_flex().gap(8).child(m.psi.level ? tile("Memory pressure", m.psi.level) : tile("Memory pressure", `${m.psi.memory}%`)).child(m.psi.level ? tile("Load", `${m.psi.load} on ${m.psi.cores}`) : tile("CPU pressure", `${m.psi.cpu}%`)).child(tile("High", m.high ? "yes" : "no", m.high ? t.blocked : t.ansi2)))
        .when(here.length > 0, el => el
          .child(h_flex().pt(3).gap(8).items_center().child(lab("Held by")).child(div().truncate().min_w(0).text_size(11).text_color(t.dim).child("each agent's whole process tree, and its biggest process")))
          .children(here.slice(0, 7).map(j => {
            const ag = s.agents.find(a => a.name === j.agent);
            return h_flex().id(`held-${j.agent}`).h(24).gap(8).items_center().text_size(12).min_w(0).rounded(5)
              .when(Boolean(ag), el => el.cursor_pointer().hover(st => st.bg(t.hover)).on_click((_e, cx) => this.push({ s: "agent", name: j.agent }, cx)))
              .child(div().w(small ? 64 : 84).flex_none().truncate().text_color(ag ? t.foreground : t.dim).child(ag ? j.agent : small ? "others" : "other sessions"))
              .when(!small, el => el.child(div().relative().w(56).flex_none().h(4).rounded(2).bg(t.selected)
                .child(div().absolute().left(0).top(0).h(4).rounded(2).bg(ag ? t.ansi4 : t.dim).w(`${Math.max(3, (j.rss_kb / most) * 100)}%`))))
              .child(div().w(40).flex_none().text_right().child(`${gb(j.rss_kb)}G`))
              .child(div().flex_1().min_w(0).truncate().text_size(11).text_color(t.dim).child(j.command ? `${j.command} ${gb(j.top_kb ?? 0)}G · ${ago(j.elapsed_s)}` : "its session only"));
          }))
          .when(here.length > 7, el => el.child(dim(`+${here.length - 7} more`))))
        .when(away.length > 0, el => el
          .child(div().pt(3).child(lab("On other machines")))
          .children(away.slice(0, 6).map((j, i) => h_flex().id(`away-${i}`).h(24).gap(8).items_center().text_size(12).min_w(0)
            .child(div().w(40).flex_none().text_color(t.dim).child(ago(j.elapsed_s))).child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(`${j.agent} · ${j.command}`))
            .child(div().flex_none().text_color(j.lost ? t.blocked : t.dim).child(`${j.machine}${j.unreachable ? " unreachable" : j.lost ? " lost" : j.rss_kb != null ? ` · ${gb(j.rss_kb)}G` : ""}`))))));
    // The cmd-cost history: what a build or test here has cost before (`swarm cost --top`), then the latest.
    const tops = s.cost_top ?? [], mins = sec => `${Math.max(1, Math.round(sec / 60))} min`;
    const jobs = part("Command cost", "this repo, this machine", null,
      !tops.length && !costly.length ? this.empty(t, "No history yet: a command is recorded once it runs a minute or takes 1G")
      : pad("jobs").gap(4)
        .when(tops.length > 0, el => el.child(h_flex().h(20).gap(8).items_center().child(lab("Most intensive")).child(div().flex_1()).child(lab(small ? "peak" : "longest · peak")))
          .children(tops.map(r => h_flex().h(24).gap(8).items_center().text_size(12).min_w(0)
            .child(this.mono(div().flex_shrink(1).min_w(0).truncate().text_size(11.5).child(r.key)))
            .child(dim(`×${r.n}`)).child(div().flex_1())
            .when(!small, el => el.child(dim(mins(r.wall_s))))
            .child(div().w(42).flex_none().text_right().text_color(r.peak_kb >= 8 * 1048576 ? t.ansi3 : t.foreground).child(`${gb(r.peak_kb)}G`)))))
        .when(costly.length > 0, el => el.child(div().h(20).mt(4).flex().items_center().child(lab("Latest")))
          .children(costly.map(e => h_flex().h(24).gap(8).items_center().text_size(12).min_w(0)
            .child(div().w(34).flex_none().text_size(11).text_color(t.dim).child(hhmm(e.ts)))
            .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(`${e.agent ?? "?"} · ${one(e.cmd)}`))
            .child(div().w(42).flex_none().text_right().text_color(t.dim).child(`${gb(e.peak_kb)}G`))))));
    const row = (key, text, color) => div().id(key).h(22).truncate().text_size(12).text_color(color ?? t.muted).child(text);
    const calm = !s.locks.length && !s.conflicts.length && !s.pressure.length;
    const locks = part("Locks and conflicts", calm ? "all clear" : "", null, pad("locks").gap(8)
      .child(h_flex().gap(8).child(tile("Locks", String(s.locks.length))).child(tile("Conflicts", String(s.conflicts.length), s.conflicts.length ? t.blocked : null)).child(tile("Memory episodes", String(s.pressure.length), s.pressure.some(p => !p.end) ? t.blocked : null)))
      .children(s.locks.map(l => row(`lock-${l.path}`, `🔒 ${l.path} · ${l.agent}${l.reason ? " · " + l.reason : ""}`)))
      .children(s.conflicts.map(c => row(`cf-${c.a}-${c.b}-${c.path}`, `⚠ ${c.a} × ${c.b} · ${c.path} · ${ago(s.now - c.since)}`, t.blocked)))
      .children(s.pressure.map(p => row(`pr-${p.start}`, `${hhmm(p.start)}–${p.end ? hhmm(p.end) : "now"} · ${p.line.replace(/^machine: /, "")}`, p.end ? t.dim : t.blocked))));
    const left = v_flex().gap(10).min_w(0).child(ci).child(watchd).child(prs).child(staff), right = v_flex().gap(10).min_w(0).child(machine).child(jobs).child(locks);
    return two ? h_flex().px(16).pt(10).gap(16).items_start().child(left.flex_grow(1.15).flex_basis(0)).child(right.flex_grow(1).flex_basis(0))
      : v_flex().px(16).pt(10).gap(10).child(left).child(right);
  }

  // ---- frame ---------------------------------------------------------------------------------
  render(cx) {
    const t = theme(), el = this.draw(t);
    if (this.visible()) {
      if (!this.loading && this.due()) this.refresh(cx);
      if (Date.now() - (this.prsAt ?? 0) > PR_POLL) this.refreshPrs(cx);
    }
    // Keys first drawn in this frame sit at their start values; a frame later they move, staggered.
    if (this.fresh.size && !this.entering) {
      this.entering = true;
      cx.timer.after(40, cx => { for (const k of this.fresh) this.seen.add(k); this.fresh.clear(); this.entering = false; cx.notify(); });
    }
    return el;
  }

  // What a command printed, or why swarm refused it. A refused `end` offers the forced one, behind its own confirmation.
  banner(t) {
    const f = this.flash, forced = f.error && f.args?.[0] === "end" && !f.args.includes("--force") && f.error.includes("--force");
    const a = forced && this.s.agents.find(x => x.name === f.args[1]);
    const text = f.error ? `Refused: ${f.error.replace(/; `swarm end \S+ --force` ends it anyway\.$/, ".")}` : f.ok;
    return h_flex().id("flash").flex_none().mx(16).mt(10).px(12).py(8).gap(10).items_start().rounded(8).border_1()
      .border_color(f.error ? t.blocked + "88" : t.border).bg(f.error ? t.blocked + "14" : t.surface)
      .child(div().flex_1().min_w(0).pt(3).text_size(12).line_height("17px").whitespace_normal().text_color(f.error ? t.foreground : t.muted).child(text))
      .when(Boolean(a), el => el.child(this.danger(t, "force", "End anyway…", () => this.askEnd(a, true))))
      .child(this.link(t, "flash-x", "Dismiss", cx => { this.flash = null; cx.notify(); }).pt(5));
  }

  // Home, Agents, Board, More on every screen, the shown screen's section marked: a task counts as Board, an
  // agent as Agents. Four equal segments of the panel's width; the mark slides. Home's badge counts what needs
  // you, More's dot is a System problem. At 340px and below the counts go and the labels stay.
  navBar(t, d) {
    const s = this.s, r = this.r, cur = r.s === "task" ? "board" : r.s === "agent" ? "agents" : r.s;
    const need = this.needs(t, d).length, left = d.count("blocked") + d.count("claimed") + d.count("open"), tiny = this.width <= 340;
    const alert = d.reds > 0 || d.watchdDead || s.watchd?.stale || s.conflicts.length > 0 || s.pressure.some(p => !p.end) || s.machine?.high;
    const items = [["home", "Home", need || null, true], ["agents", "Agents", d.live.length], ["board", "Board", left], ["more", "More", alert ? "" : null, true]];
    const w = (this.width - 2 - 32 - 6) / 4, at = Math.max(0, items.findIndex(i => i[0] === cur));
    return div().flex_none().mx(16).mb(2).relative().h(34).rounded(9).bg(t.surface).border_1().border_color(t.border)
      .child(div().id("nav-on").absolute().top(2).left(2 + at * w).w(w).h(28).rounded(7).bg(t.selected).transition("left", { duration: 180, easing: "ease-out" }))
      .children(items.map(([id, label, n, red], i) => h_flex().id(`nav-${id}`).absolute().top(2).left(2 + i * w).w(w).h(28).gap(6).justify_center().items_center().rounded(7)
        .text_size(12).cursor_pointer().text_color(id === cur ? t.foreground : t.muted).when(id === cur, el => el.font_semibold())
        .hover(st => st.text_color(t.foreground)).on_click((_e, cx) => this.push(id === "board" ? { s: id, f: "active" } : id === "more" ? { s: id, tab: "activity" } : { s: id }, cx))
        .child(label)
        .when(n === "", el => el.child(this.dot(t.blocked, 6)))
        .when(Boolean(n) && !tiny, el => el.child(red ? div().px(5).h(15).flex().items_center().rounded(8).bg(t.blocked).text_color(t.background).text_size(10).font_semibold().child(String(n))
          : div().text_size(11).font_normal().text_color(t.dim).child(String(n))))));
  }

  // Home is two columns from 760px; every other screen is one column, at most 720px wide. The Activity and
  // System code keeps its own breakpoints (760, 640, 520, 340).
  draw(t) {
    const s = this.s, r = this.r, deep = this.stack.length > 1;
    const root = v_flex().id("swarm").size_full().min_h(0).rounded(10).overflow_hidden().bg(t.background).border_1().border_color(t.border).text_color(t.foreground).text_size(12.5)
      .on_size_change((size, cx) => { if (Math.abs(size.width - this.width) > 1) { this.width = size.width; cx.notify(); } });
    const note = text => div().px(16).pt(12).text_size(11).text_color(t.dim).child(text);
    if (!s?.agents) {
      return root.child(h_flex().h(48).flex_none().px(16).items_center().border_b(1).border_color(t.border).child(div().font_semibold().text_size(14).child("Swarm")))
        .child(note(this.error ?? (this.loading || !s ? "loading…" : "No live swarm in this repo")));
    }
    const d = this.derive(), away = s.away, commsAddr = d.commsAgent && focusAddr(d.commsAgent);
    const toggle = h_flex().id("away").flex_none().h(28).pl(10).pr(5).gap(8).items_center().rounded(14).border_1().border_color(away ? t.accent : t.border).bg(away ? t.accent + "1c" : t.surface).cursor_pointer()
      .tooltip(away ? "You are away. Click when you are back." : "Going away? Questions will wait here instead of pinging you.")
      .on_click((_e, cx) => this.act(cx, away ? ["away", "--back"] : ["away"]))
      .child(div().text_size(11.5).text_color(away ? t.foreground : t.muted).child("Away"))
      .child(div().relative().w(30).h(18).rounded(9).bg(away ? t.accent : t.selected)
        .child(div().id("away-knob").absolute().top(2).left(away ? 14 : 2).size(14).rounded(7).bg(away ? t.accent_foreground : t.muted).transition("left", { duration: 160, easing: "ease-out" })));
    const head = h_flex().h(48).flex_none().px(16).gap(8).items_center().min_w(0)
      .child(div().flex_none().font_semibold().text_size(14).child("Swarm"))
      .child(div().truncate().min_w(0).text_size(12).text_color(t.dim).child(base(this.cwd)))
      .when(Boolean(d.ci), el => el.child(h_flex().id("ci-dot").flex_none().gap(5).items_center().text_size(11).text_color(d.ci[0] === "green" ? t.dim : t[d.ci[1]]).cursor_pointer()
        .tooltip(`main's CI: ${d.ci[0]}`).on_click((_e, cx) => this.push({ s: "more", tab: "system" }, cx))
        .child(this.dot(t[d.ci[1]], 7)).when(this.width >= 420, el => el.child(d.ci[0]))))
      .child(div().flex_1())
      .when(Boolean(commsAddr), el => el.child(this.link(t, "comms-link", this.width >= 480 ? "Communicator ↗" : "Comms ↗", () => run("agent.focus", { terminal: commsAddr })).text_size(11).text_color(t.muted)
        .tooltip("Open the communicator's terminal: your channel to the swarm.")))
      .child(toggle);
    const prev = deep ? this.stack.at(-2) : null;
    const backRow = deep ? h_flex().flex_none().h(32).px(10).items_center().child(h_flex().id("back").h(24).px(6).gap(6).items_center().rounded(6).text_size(12).text_color(t.muted).cursor_pointer()
      .hover(st => st.bg(t.hover).text_color(t.foreground)).on_click((_e, cx) => this.back(cx))
      .child(div().text_size(15).child("‹")).child({ home: "Home", agents: "Agents", board: "Board", more: "More", task: `Task #${prev.id}`, agent: prev.name }[prev.s])) : null;
    const body = r.s === "agents" ? this.agentsScreen(t, d) : r.s === "board" ? this.board(t, d) : r.s === "task" ? this.task(t, d)
      : r.s === "agent" ? this.agentScreen(t, d) : r.s === "more" ? this.moreScreen(t, d) : this.home(t, d);
    const k = `scr:${this.stack.length}:${r.s}:${r.id ?? r.name ?? ""}`, { first } = deep ? this.enter(k, false) : { first: false };
    const wide = r.s === "more" || (r.s === "home" && this.width >= 760), waiting = this.needs(t, d).length;
    const page = v_flex().id(k).relative().w_full().max_w(wide ? 1400 : 720).px(r.s === "more" ? 0 : 16).pt(deep ? 2 : 10).pb(16)
      .left(first ? 20 : 0).opacity(first ? 0 : 1).transition("left", { duration: 200, easing: "ease-out" }).transition("opacity", { duration: 200, easing: "ease-out" })
      .child(body);
    return root.child(head).child(this.navBar(t, d))
      .when(deep, el => el.child(backRow))
      .when(Boolean(away), el => el.child(h_flex().flex_none().px(16).py(7).gap(8).items_center().min_w(0).bg(t.accent + "14").border_b(1).border_color(t.border).text_size(11.5)
        .child(div().flex_1().min_w(0).whitespace_normal().line_height("16px").text_color(t.muted)
          .child(`Away since ${hhmm(away.since)}${away.note ? ` (${away.note})` : ""}. Questions wait here and nobody pings you${waiting ? `; ${waiting} waiting now` : ""}.`))))
      .when(Boolean(this.flash) && !this.busy, el => el.child(this.banner(t)))
      .when(Boolean(this.busy), el => el.child(div().flex_none().mx(16).mt(10).px(12).py(8).rounded(8).border_1().border_color(t.border).bg(t.surface).text_size(12).text_color(t.muted).child("Working…")))
      .when(!s.active, el => el.child(note("No live swarm in this repo; showing its last state.")))
      .when(Boolean(this.error), el => el.child(note(this.error)))
      .child(v_flex().id(`body-${k}`).flex_1().min_h(0).overflow_y_scrollbar().items_center().child(page));
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
  "task-priority": ["link", "tasks", "Priority set", "A task's priority was changed. Nothing for you to do.", "", 0],
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
  "ctx-note": ["gauge", "agents", "Context note", "An agent's context passed a size mark and it was told to wrap up or keep working through compaction.", "", 0],
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
  "job-start": ["cpu", "machine", "Run started", "An agent started a build or test on another machine.", "", 0],
  "job-end": ["cpu", "machine", "Run finished", "A build or test on another machine finished.", "", 0],
  "remote-clean": ["trash", "machine", "Run cleaned up", "A finished run's copy on another machine was removed.", "", 0],
  "orphan-kill": ["zap", "machine", "Process stopped", "The swarm stopped a process an agent left running. Nothing for you to do.", "warn", 1],
  limits: ["users", "agents", "Limits set", "The staffing numbers changed: how many agents auto-spawn keeps, and the most that may run.", "", 1],
  "spawn-held": ["ban", "agents", "Auto-spawn holding", "Tasks could start, but auto-spawn stopped at your number, your max or for memory. Ask the communicator to raise a number if you want more agents.", "warn", 1],
  "spawn-refused": ["ban", "agents", "Spawn refused", "An agent tried to start a peer at your max and was refused. Only the communicator raises the max.", "", 1],
  "stay-hung": ["triangle-alert", "agents", "Hung", SIGN.hung[1], "warn", 1],
  "stay-nowaiter": ["triangle-alert", "agents", "No waiter", SIGN.nowaiter[1], "warn", 1],
  "stay-unwoken": ["triangle-alert", "agents", "Not waking", SIGN.unwoken[1], "warn", 1],
  "stay-check": ["bell", "agents", "Liveness check", "A stayer idle 50 minutes was asked whether it still stays. No answer in 5 minutes means hung.", "", 0],
  role: ["users", "agents", "Role", "An agent named what it is doing now. Nothing for you to do.", "", 0],
  stay: ["clock", "agents", "Staying", "An agent said what it is waiting for, so the swarm keeps it while idle. Nothing for you to do.", "", 0],
  "stay-end": ["log-out", "agents", "Stay over", "An agent stopped staying and is treated like any idle agent.", "", 0],
  quiet: ["info", "agents", "Swarm quiet", "No task is open or claimed. Staying agents were told.", "", 0],
  other: ["dot", "other", "Other", "An event this panel has no description for.", "", 0],
}).map(([k, [icon, group, label, what, level, show]]) => [k, { icon, group, label, what, level, show: Boolean(show) }]));
// Runs of these, within two minutes, fold into one summary row; `same`: only by the same agent.
const FOLD = { spawn: { same: true }, end: {}, "task-add": { same: true }, drop: { same: true } };
const andList = xs => xs.length > 1 ? `${xs.slice(0, -1).join(", ")} and ${xs.at(-1)}` : xs[0] ?? "";
