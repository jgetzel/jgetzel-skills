import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex } from "gpui-base";
import { exec, theme, shared, setShared, props, openOverlay, closeOverlay, notify, settings, window } from "herdr";

// Events are fetched by the jgetzel-tabs mod into shared "calendar"; this panel only shows them.
const pad = (n) => String(n).padStart(2, "0");
const dayKey = (d) => `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}`;
const clock = (ms) => { const d = new Date(ms), h = d.getHours(); return `${h % 12 || 12}:${pad(d.getMinutes())}`; };
const ampm = (ms) => `${clock(ms)} ${new Date(ms).getHours() < 12 ? "AM" : "PM"}`;
const span = (ms) => { const m = Math.max(1, Math.round(ms / 60000)); return m < 60 ? `${m}m` : m % 60 ? `${Math.floor(m / 60)}h ${m % 60}m` : `${m / 60}h`; };
const DAYS = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"], MONTHS = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];
const dateLabel = (d) => `${DAYS[d.getDay()]}, ${MONTHS[d.getMonth()]} ${d.getDate()}`;
const conflictsOf = (e, list) => e.all_day ? [] : list.filter((f) => f !== e && !f.all_day && f.start < e.end && e.start < f.end);
const icon = (name, size, color) => svg(`mods/calendar/${name}.svg`).size(size).flex_none().text_color(color);
const pill = (t, text, color) => div().px(5).rounded(4).flex_none().bg(t.raised).text_size(10).text_color(color).child(text);
const stop = (_e, cx) => cx.stop_propagation();
// The popup draws its own frame so the whole card can fade and rise in, not just its contents.
const openDetails = (e) => openOverlay({ mod: "calendar", kind: "dialog", width: 460, height: 540, frame: "none", props: { event: e } });
const mac = () => window().platform === "macos";
const open = (url) => exec(mac() ? "open" : "xdg-open", [url]);
const COPY = { mac: 'printf %s "$1" | pbcopy', linux: 'printf %s "$1" | wl-copy 2>/dev/null || printf %s "$1" | xclip -selection clipboard' };
const copy = (text) => exec("sh", ["-c", mac() ? COPY.mac : COPY.linux, "copy", text]).then(() => notify({ title: "Copied", body: text, timeout: 2000 }));
// The meeting's working doc for the row's notes button: an attached Doc, else the first description link.
const notesOf = (e) => (e.files ?? []).find((f) => f.kind === "doc") ?? (e.links ?? [])[0];
const KIND = { doc: ["doc", "Google Doc"], recording: ["video", "Recording"], file: ["doc", "File"] };

function button(id, t, { label, iconName, strong, onClick }) {
  return h_flex().id(id).h(24).px(8).gap(5).flex_none().items_center().rounded(6).text_size(11).cursor_pointer()
    .when(strong, (el) => el.bg(t.solid).text_color(t.solid_foreground))
    .when(!strong, (el) => el.border_1().border_color(t.border).text_color(t.muted).hover((s) => s.bg(t.hover).text_color(t.foreground)))
    .on_mouse_down("left", stop).on_click((e, cx) => { cx.stop_propagation(); onClick(e, cx); })
    .when(Boolean(iconName), (el) => el.child(icon(iconName, 13, strong ? t.solid_foreground : t.muted)))
    .when(Boolean(label), (el) => el.child(label));
}

function state(e, now) {
  const past = !e.all_day && e.end <= now, live = !e.all_day && e.start <= now && now < e.end;
  return { past, live, soon: !e.all_day && e.start > now && e.start - now <= 300000 };
}

export default class Calendar extends View {
  init(_props, cx) {
    // Redraw each minute for the countdowns; data changes redraw on their own.
    cx.timer.every(60000, (cx) => cx.notify());
    // A popup starts hidden and fades in once armed; unarmed, it simply shows (never stuck invisible).
    this.armed = Boolean(props()?.event);
    if (this.armed) {
      this.handle = cx.focus_handle();
      cx.timer.after(16, (cx) => { this.entered = true; this.handle.focus(); cx.notify(); });
      return;
    }
    this.gen = 0; this.opened = shared("calendar.opened") ?? 0;
    this.reveal(cx);
  }

  // Each panel opening draws fresh rows and strip blocks (new ids, so nothing animates *from* the old
  // state), starting hidden and revealed a moment later: rows fade in from the left, blocks grow in.
  // From render, skip notify (it throws there; that render already draws the hidden state).
  reveal(cx, fromRender = false) {
    this.gen++; this.revealed = false; this.revealedAt = Date.now();
    if (!fromRender) cx.notify();
    cx.timer.after(40, (cx) => { this.revealed = true; cx.notify(); });
  }

  // Fade the popup out, then close it.
  leave(cx) {
    if (this.leaving) return;
    this.leaving = true; cx.notify();
    cx.timer.after(170, () => closeOverlay(props().overlay));
  }

  // The left rail says how you stand with a meeting: solid accepted, faint maybe, hollow unanswered.
  rail(e, s, t) {
    const el = div().w(3).h(32).rounded(2).flex_none();
    if (s.past) return el.bg(t.border);
    if (s.soon) return el.bg(t.blocked).loop("opacity", { from: 0.4, to: 1, period: 1400 });
    if (e.rsvp === "NEEDS-ACTION") return el.border_1().border_color(t.blocked);
    if (e.rsvp === "TENTATIVE") return el.bg(t.accent + "55");
    return el.bg(s.live ? t.accent : t.accent + "99");
  }

  meta(e, s, list, t, now) {
    const clash = s.past ? [] : conflictsOf(e, list), parts = [];
    if (s.live) parts.push(div().text_color(t.accent).font_semibold().child(`Now · ${span(e.end - now)} left`));
    else if (s.soon) parts.push(div().text_color(t.blocked).font_semibold().child(`Starts in ${span(e.start - now)}`));
    else if (!e.all_day) parts.push(div().child(span(e.end - e.start)));
    if (!s.past && e.rsvp === "NEEDS-ACTION") parts.push(h_flex().gap(4).items_center().text_color(t.blocked)
      .child(div().size(6).rounded(3).bg(t.blocked)).child("Respond"));
    if (!s.past && e.rsvp === "TENTATIVE") parts.push(div().text_color(t.muted).child("Maybe"));
    if (clash.length) parts.push(h_flex().min_w(0).gap(4).items_center().text_color(t.ansi3)
      .child(icon("conflict", 11, t.ansi3)).child(div().min_w(0).truncate().child(clash.length > 1 ? `Conflicts with ${clash.length}` : `Conflicts with ${clash[0].title}`)));
    return h_flex().min_w(0).gap(6).items_center().text_size(11).text_color(t.dim)
      .children(parts.flatMap((p, i) => i ? [div().text_color(t.dim).child("·"), p] : [p]));
  }

  row(e, i, list, t, now) {
    const s = state(e, now), delay = Math.min(this.rowN++, 6) * 12;
    return h_flex().id(`ev-${this.gen}-${e.day}-${i}`).flex_none()
      .relative().left(this.revealed ? 0 : -12).opacity(this.revealed ? 1 : 0)
      .transition("opacity", { duration: 150, delay, easing: "ease-out" }).transition("left", { duration: 150, delay, easing: "ease-out" }).px(8).py(s.past ? 4 : 6).gap(10).items_center().rounded(8).cursor_pointer()
      .when(s.live, (el) => el.bg(t.selected)).hover((st) => st.bg(t.hover))
      .on_click(() => openDetails(e))
      .child(v_flex().w(44).flex_none().items_end()
        .child(div().text_size(12).text_color(s.past ? t.dim : t.foreground).child(e.all_day ? "All day" : clock(e.start)))
        .when(!e.all_day && !s.past, (el) => el.child(div().text_size(10.5).text_color(t.dim).child(clock(e.end)))))
      .when(!s.past, (el) => el.child(this.rail(e, s, t)))
      .child(v_flex().flex_1().min_w(0).gap(2)
        .child(div().truncate().text_size(13).text_color(s.past ? t.dim : e.rsvp === "TENTATIVE" ? t.muted : t.foreground).when(s.live, (el) => el.font_semibold()).child(e.title))
        .when(!s.past, (el) => el.child(this.meta(e, s, list, t, now))))
      .when(Boolean(notesOf(e)), (el) => el.child(button(`notes-${e.day}-${i}`, t, { iconName: "doc", onClick: () => open(notesOf(e).url) })))
      .when(Boolean(e.link) && !s.past, (el) => el.child(button(`join-${e.day}-${i}`, t, { label: s.live || s.soon ? "Join" : null, iconName: "video", strong: s.live || s.soon, onClick: () => open(e.link) })));
  }

  nowLine(t, now) {
    return h_flex().h(14).px(8).gap(10).items_center().flex_none()
      .child(div().w(44).flex_none().text_right().text_size(10).font_semibold().text_color(t.ansi1).child(clock(now)))
      .child(div().size(7).rounded(4).bg(t.ansi1).flex_none()).child(div().flex_1().h(1).bg(t.ansi1));
  }

  day(label, date, list, t, now, isToday) {
    const upcoming = list.filter((e) => !state(e, now).past).length;
    const rows = list.map((e, i) => this.row(e, i, list, t, now));
    // The now line sits before the next meeting (or after the last), unless one is running.
    if (isToday && list.length && !list.some((f) => state(f, now).live)) {
      const next = list.findIndex((f) => !f.all_day && f.start > now);
      rows.splice(next < 0 ? rows.length : next, 0, this.nowLine(t, now));
    }
    return v_flex().gap(1).flex_none()
      .child(h_flex().px(8).pt(10).pb(6).gap(6).items_center()
        .child(div().text_size(12).font_semibold().child(label)).child(div().text_size(11).text_color(t.dim).child(dateLabel(date)))
        .child(div().flex_1()).child(div().text_size(10.5).text_color(t.dim).child(list.length ? `${upcoming} upcoming` : "")))
      .children(list.length ? rows : [div().px(8).py(6).text_size(12).text_color(t.dim).child("Nothing scheduled")]);
  }

  strip(events, t, now) {
    const H = 3600000, base = new Date(now); base.setHours(0, 0, 0, 0);
    const timed = events.filter((e) => !e.all_day);
    let from = 8, to = 18;
    for (const e of timed) { from = Math.min(from, Math.floor((e.start - base) / H)); to = Math.max(to, Math.ceil((e.end - base) / H)); }
    from = Math.max(0, from); to = Math.min(24, Math.max(to, from + 1));
    // Positions are percentages of the track, so they need no measuring.
    const t0 = +base + from * H, t1 = +base + to * H, pct = (f) => `${(f * 100).toFixed(3)}%`;
    const x = (ms) => Math.max(0, Math.min(1, (ms - t0) / (t1 - t0)));
    const lanes = [], placed = timed.map((e) => {
      let lane = lanes.findIndex((end) => end <= e.start);
      if (lane < 0) { lane = lanes.length; lanes.push(0); }
      lanes[lane] = e.end;
      return [e, lane];
    });
    const TOP = 15, TRACK = 20, n = Math.max(1, lanes.length), laneH = (TRACK - 4 - (n - 1) * 2) / n;
    const step = to - from > 10 ? 2 : 1, hours = [];
    for (let h = from; h <= to; h += step) if (x(+base + h * H) <= 0.97) hours.push(h);
    const live = timed.find((e) => e.start <= now && now < e.end), next = timed.find((e) => e.start > now);
    const block = ([e, lane], i) => {
      const s = state(e, now), left = x(e.start), width = Math.max(0.006, x(e.end) - left - 0.003);
      // Width animates only in px (not %), so blocks use the measured track once known; until then, %.
      const W = this.trackW, size = W ? (this.revealed ? width * W : 0) : pct(width);
      const el = div().id(`blk-${this.gen}-${e.start}-${lane}`).absolute().left(W ? left * W : pct(left)).top(TOP + 2 + lane * (laneH + 2)).w(size).h(laneH)
        .transition("width", { duration: 420, delay: i * 35, easing: "ease-out" }).rounded(3).cursor_pointer()
        .tooltip(`${ampm(e.start)}  ${e.title}`).on_click(() => openDetails(e));
      if (s.past) return el.bg(t.border);
      if (s.live) return el.bg(t.accent);
      if (s.soon) return el.bg(t.blocked).loop("opacity", { from: 0.4, to: 1, period: 1400 });
      if (e.rsvp === "NEEDS-ACTION") return el.bg(t.blocked + "26").border_1().border_color(t.blocked);
      return el.bg(e.rsvp === "TENTATIVE" ? t.accent + "55" : t.accent + "99");
    };
    return v_flex().flex_none().px(14).pt(10).pb(10).gap(6).border_b(1).border_color(t.border)
      // Size reports give the track width (zoomed px; layout takes unzoomed ones). One also arrives when the
      // panel is shown by something other than the tab bar (e.g. a space switch), so an unchanged width after
      // a quiet spell counts as an opening; a changed width is a resize and only re-measures.
      .child(div().id("strip").relative().w_full().h(TOP + TRACK + 2).on_size_change((size, cx) => {
        const w = size.width / (settings().zoom ?? 1), first = this.trackW === undefined, same = Math.abs(w - (this.trackW ?? w)) < 0.5;
        this.trackW = w;
        if (first || (same && Date.now() - this.revealedAt > 800)) this.reveal(cx); else cx.notify();
      })
        .children(hours.map((h) => div().absolute().top(0).left(pct(x(+base + h * H))).text_size(10).text_color(t.dim).child(String(h % 12 || 12))))
        .child(div().absolute().left(0).top(TOP).w_full().h(TRACK).rounded(5).bg(t.raised))
        .children(placed.map(block))
        .when(now >= t0 && now <= t1, (el) => el.child(div().absolute().left(pct(x(now))).top(TOP - 3).w(2).h(TRACK + 6).rounded(1).bg(t.ansi1))))
      .child(h_flex().gap(6).items_center().text_size(12).min_w(0)
        .when(Boolean(live), (el) => el.child(div().size(6).rounded(3).bg(t.accent)).child(div().min_w(0).truncate().font_semibold().child(live.title))
          .child(div().flex_none().text_color(t.accent).child(`${span(live.end - now)} left`)))
        .when(!live && Boolean(next), (el) => el.child(div().flex_none().text_color(t.dim).child("Next"))
          .child(div().min_w(0).truncate().font_semibold().child(next.title))
          .child(div().flex_none().text_color(next.start - now <= 300000 ? t.blocked : t.muted).child(`in ${span(next.start - now)}`)))
        .when(!live && !next, (el) => el.child(div().text_color(t.dim).child(timed.length ? "Done with meetings today" : "No meetings today"))));
  }

  details(e, t) {
    const listed = e.organizer_email && !e.attendees.some((a) => a.email === e.organizer_email);
    const guests = listed ? [{ name: e.organizer ?? e.organizer_email, email: e.organizer_email, status: "ACCEPTED" }, ...e.attendees] : e.attendees;
    const now = Date.now(), s = state(e, now), yes = guests.filter((a) => a.status === "ACCEPTED").length;
    const when = e.all_day ? "All day" : `${ampm(e.start)} – ${ampm(e.end)} · ${span(e.end - e.start)}`;
    const status = s.live ? `Now · ${span(e.end - now)} left` : e.start > now ? `Starts in ${span(e.start - now)}` : "Ended";
    const going = { ACCEPTED: "You're going", TENTATIVE: "You said maybe", "NEEDS-ACTION": "You haven't responded" }[e.rsvp];
    const section = (label, body) => v_flex().gap(6).child(div().text_size(10.5).font_semibold().text_color(t.dim).child(label.toUpperCase())).child(body);
    return v_flex().id("cal-details").size_full().min_h(0).bg(t.popover).text_color(t.foreground).text_size(13)
      .rounded(12).border_1().border_color(t.border).shadow_xl().overflow_hidden()
      .when(Boolean(this.handle), (el) => el.track_focus(this.handle).on_key_down((ev, cx) => { if (ev.key === "escape") { cx.stop_propagation(); this.leave(cx); } }))
      .relative().top(this.leaving ? 6 : this.entered || !this.armed ? 0 : 10).opacity(!this.leaving && (this.entered || !this.armed) ? 1 : 0)
      .transition("opacity", { duration: 160, easing: "ease-out" }).transition("top", { duration: 200, easing: "ease-out" })
      .child(v_flex().flex_none().px(18).pt(16).pb(14).gap(8).border_b(1).border_color(t.border)
        .child(h_flex().gap(10).items_start()
          .child(div().flex_1().min_w(0).text_size(16).font_semibold().child(e.title))
          .child(div().id("details-close").size(24).flex_none().flex().items_center().justify_center().rounded(6).text_color(t.dim).cursor_pointer()
            .hover((st) => st.bg(t.hover).text_color(t.foreground)).on_click((_e, cx) => this.leave(cx)).child("✕")))
        .child(h_flex().gap(8).items_center().text_size(12).text_color(t.muted).child(when)
          .when(!e.all_day, (el) => el.child(div().text_color(s.live ? t.accent : s.soon ? t.blocked : t.dim).child(`· ${status}`))))
        .child(h_flex().gap(6).items_center().text_size(12).text_color(e.rsvp === "NEEDS-ACTION" ? t.blocked : t.muted)
          .child(div().size(6).rounded(3).when(e.rsvp === "NEEDS-ACTION", (el) => el.bg(t.blocked)).when(e.rsvp !== "NEEDS-ACTION", (el) => el.bg(e.rsvp === "TENTATIVE" ? t.accent + "55" : t.accent)))
          .child(going))
        .child(h_flex().pt(4).gap(8)
          .when(Boolean(e.link) && !s.past, (el) => el.child(button("details-join", t, { label: "Join meeting", iconName: "video", strong: true, onClick: () => open(e.link) })))
          .when(Boolean(e.open), (el) => el.child(button("details-open", t, { label: "Open in Google Calendar", iconName: "external", strong: !e.link || s.past, onClick: () => open(e.open) })))))
      .child(v_flex().id("cal-details-body").flex_1().min_h(0).overflow_y_scrollbar().px(18).py(14).gap(16)
        .when(Boolean(e.location) && e.location !== e.link, (el) => el.child(section("Location", div().text_size(12).child(e.location))))
        .when(Boolean(e.files?.length || e.links?.length), (el) => el.child(section("Notes & links", v_flex().gap(2).children([
          ...(e.files ?? []).map((f) => [f, ...KIND[f.kind]]), ...(e.links ?? []).map((l) => [l, "link", l.host]),
        ].map(([item, iconName, sub], i) => h_flex().id(`res-${i}`).px(8).py(6).mx(-8).gap(10).items_center().rounded(7).cursor_pointer()
          .hover((st) => st.bg(t.hover)).on_click(() => open(item.url))
          .child(icon(iconName, 15, t.accent))
          .child(v_flex().flex_1().min_w(0).child(div().text_size(12.5).truncate().child(item.title)).child(div().text_size(10.5).text_color(t.dim).truncate().child(sub)))
          .child(icon("external", 12, t.dim)))))))
        .when(Boolean(e.description), (el) => el.child(section("Description", div().text_size(12).text_color(t.muted).child(e.description))))
        .when(guests.length > 0, (el) => el.child(section(`Guests · ${guests.length}${e.attendees.length >= 60 ? "+" : ""} · ${yes} going`, this.guests(guests, e, t)))));
  }

  // Guests grouped by their answer; the organizer is tagged in place (and added as going if Google didn't list them).
  guests(guests, e, t) {
    const groups = [["ACCEPTED", "Going", t.ansi2], ["TENTATIVE", "Maybe", t.accent], ["NEEDS-ACTION", "No reply", t.dim], ["DECLINED", "Declined", t.ansi1]];
    return v_flex().gap(10).children(groups.map(([status, label, color]) => [label, color, guests.filter((a) => a.status === status)]).filter(([, , list]) => list.length)
      .map(([label, color, list]) => v_flex().gap(1)
        .child(h_flex().gap(6).items_center().pb(2).text_size(11).font_semibold().text_color(t.muted)
          .child(div().size(6).rounded(3).bg(color)).child(label).child(div().font_normal().text_color(t.dim).child(String(list.length))))
        .children(list.map((a) => h_flex().id(`guest-${a.email || a.name}`).px(8).py(3).mx(-8).gap(6).items_center().rounded(6).text_size(12)
          .when(Boolean(a.email), (el) => el.cursor_pointer().hover((st) => st.bg(t.hover)).on_click(() => copy(a.email)))
          .child(div().min_w(0).truncate().text_color(a.status === "DECLINED" ? t.dim : t.foreground).child(a.name))
          .when(Boolean(a.email) && a.email === e.organizer_email, (el) => el.child(pill(t, "Organizer", t.muted)))
          .when(Boolean(a.external), (el) => el.child(pill(t, "External", t.blocked)))
          .child(div().flex_1())
          .when(Boolean(a.email) && a.email !== a.name, (el) => el.child(div().max_w(180).flex_none().truncate().text_size(10.5).text_color(t.dim).child(a.email)))))));
  }

  render(cx) {
    const t = theme();
    if (props()?.event) return this.details(props().event, t);
    // The tab bar bumps shared "calendar.opened" just before it shows this panel.
    const opened = shared("calendar.opened") ?? 0;
    if (opened !== this.opened) { this.opened = opened; this.reveal(cx, true); }
    this.rowN = 0;
    const cal = shared("calendar") ?? { events: [] }, loading = shared("calendar.loading");
    const now = Date.now(), today = new Date(), tomorrow = new Date(now + 86400000);
    const of = (d) => cal.events.filter((e) => e.day === dayKey(d));
    return v_flex().id("calendar").size_full().min_h(0).rounded(10).overflow_hidden().bg(t.background).border_1().border_color(t.border).text_color(t.foreground).text_size(13)
      .child(h_flex().h(42).flex_none().px(14).gap(8).items_center().border_b(1).border_color(t.border)
        .child(icon("calendar", 15, t.muted)).child(div().font_semibold().child("Calendar"))
        .child(div().flex_1())
        .child(div().text_size(10.5).text_color(t.dim).child(loading ? "Refreshing…" : cal.updated ? `Updated ${ampm(cal.updated)}` : ""))
        .child(div().id("cal-refresh").size(24).flex().items_center().justify_center().rounded(6).text_color(t.dim).cursor_pointer()
          .hover((s) => s.bg(t.hover).text_color(t.foreground)).on_click(() => setShared("calendar.refresh", Date.now()))
          .child(icon("refresh", 13, t.dim).when(Boolean(loading), (el) => el.spin(900)))))
      .child(this.strip(of(today), t, now))
      .when(Boolean(cal.error), (el) => el.child(div().px(14).py(8).text_size(11).text_color(t.ansi1).border_b(1).border_color(t.border).child(cal.error)))
      .child(v_flex().id("cal-list").flex_1().min_h(0).overflow_y_scrollbar().px(6).pb(10)
        .child(this.day("Today", today, of(today), t, now, true))
        .child(this.day("Tomorrow", tomorrow, of(tomorrow), t, now, false)));
  }
}
