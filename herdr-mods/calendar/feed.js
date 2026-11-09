import { div } from "gpui-kit";
import { shared, setShared, exec, appHome, run, layout, nextCommand, notify, readTextFile } from "herdr";

// Calendar plumbing for the tab bar, which always runs (the panel only starts once opened).
// The source is herdr-mods/calendar/feed.js in jgetzel-skills; install.lua copies it into mods/jgetzel-tabs.
// - shared "calendar" holds the last fetch and persists in shared.json, so a restart shows it at once.
// - the panel's ↻ bumps shared "calendar.refresh"; the "jgetzel-tabs.calendar" key toggles the panel.

const STALE = 300000;

function find(node, id) {
  if (node?.id === id) return node;
  for (const child of node?.children ?? []) {
    const found = find(child, id);
    if (found) return found;
  }
  return null;
}

// Tells the panel it is about to be shown, so it can start hidden and animate in.
export function markCalendarOpened() { setShared("calendar.opened", Date.now()); }

function toggle() {
  const root = layout(), panel = find(root, "panel"), body = find(root, "panel-body");
  if (panel && !panel.hidden && body?.active === "calendar") run("layout.hide", { id: "panel" });
  else { markCalendarOpened(); run("layout.select", { stack: "panel-body", child: "calendar" }); run("layout.show", { id: "panel" }); }
}

// After a Herdr update, rebuild this tab bar copy and the layout from the new originals: install.lua,
// whose path the copy's mod.json records along with the Herdr version it was built from.
async function reinstallIfUpdated() {
  const mod = JSON.parse((await readTextFile(`${appHome()}/mods/jgetzel-tabs/mod.json`)) ?? "{}");
  const running = (await exec("herdr-app", ["--version"])).stdout.trim().split(/\s+/).pop();
  if (!running || !mod.installer || mod.cloned_from?.version === running) return;
  // A successful run rewrites this mod, which reloads it and ends this task, so the reloaded copy
  // announces it (see calendarFeed). A failed run writes nothing, so this task survives to report it.
  setShared("jgetzel.reinstalled", running);
  const r = await exec("luajit", [mod.installer]);
  if (r.code !== 0) {
    setShared("jgetzel.reinstalled", null);
    notify({ title: "Herdr mods re-install failed", body: `${(r.stderr || r.stdout).trim().split("\n").pop()}. Run luajit ${mod.installer} to see why.`, level: "error" });
  }
}

export function calendarFeed(cx) {
  const feed = { asked: shared("calendar.refresh") ?? 0, fetching: false, tried: 0 };

  // Render calls this, so it never calls cx.notify() itself (that throws there). A failed fetch waits out
  // STALE like a good one: `tried` covers it, since `updated` only moves on success.
  feed.fetch = (cx, force) => {
    if (feed.fetching || (!force && Date.now() - Math.max(shared("calendar")?.updated ?? 0, feed.tried) < STALE)) return;
    feed.asked = shared("calendar.refresh") ?? 0; feed.fetching = true; feed.tried = Date.now(); setShared("calendar.loading", true);
    cx.spawn(async (cx) => {
      try {
        const r = await exec("luajit", [`${appHome()}/mods/calendar/events.lua`]);
        if (r.code !== 0) throw new Error(r.stderr.trim().split("\n").pop() || `exit ${r.code}`);
        // stderr on success: rules or time zones it skipped
        setShared("calendar", { events: JSON.parse(r.stdout), updated: Date.now(), error: r.stderr.trim() || null });
      } catch (e) { setShared("calendar", { ...(shared("calendar") ?? { events: [] }), error: String(e) }); }
      finally { feed.fetching = false; setShared("calendar.loading", false); cx.notify(); }
    });
  };

  // Call from render: picks up the panel's refresh request.
  feed.render = (cx) => { if ((shared("calendar.refresh") ?? 0) > feed.asked) feed.fetch(cx, true); };

  // The Calendar button's badge: a dot while a meeting runs, minutes until one within the hour (pulsing in the last 5).
  feed.badge = (t) => {
    const now = Date.now(), timed = (shared("calendar")?.events ?? []).filter((e) => !e.all_day && e.end > now);
    const next = timed.find((e) => e.start > now), mins = next ? Math.ceil((next.start - now) / 60000) : Infinity;
    if (mins > 5 && timed.some((e) => e.start <= now)) return [div().size(7).ml(1).rounded(4).flex_none().bg(t.accent)];  // in a meeting
    const b = mins <= 5 ? { text: `${mins}m`, color: t.blocked } : mins <= 60 ? { text: `${mins}m`, color: t.muted } : null;
    return b ? [div().text_size(11).font_semibold().text_color(b.color).child(b.text).when(mins <= 5, (el) => el.loop("opacity", { from: 0.4, to: 1, period: 1400 }))] : [];
  };

  setShared("calendar.loading", false);
  const reinstalled = shared("jgetzel.reinstalled");
  if (reinstalled) { setShared("jgetzel.reinstalled", null); notify({ title: "Herdr mods updated", body: `Re-installed for Herdr ${reinstalled}`, level: "success", timeout: 5000 }); }
  cx.spawn(async () => { try { await reinstallIfUpdated(); } catch (e) { notify({ title: "Herdr mods re-install check failed", body: String(e), level: "error" }); } });
  feed.fetch(cx, false);
  // The notify redraws the badge's minute count.
  cx.timer.every(60000, (cx) => { feed.fetch(cx, false); cx.notify(); });
  cx.spawn(async (cx) => {
    for (;;) {
      if (await nextCommand() === "calendar") toggle();
      cx.notify();
    }
  });
  return feed;
}
