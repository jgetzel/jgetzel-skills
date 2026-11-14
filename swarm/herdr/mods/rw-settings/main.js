// The rework's Settings (swarm/herdr/UI-SPEC.md, slice 11): the app's own Settings screen with what today lives only in
// settings.json, hiding a machine from the rail, logging in again and keys.json. The installer clones the app's screen
// (frame/settings/main.js) as app.js, since a mod can't import from outside its folder. With props {footer: true} this
// mod is the rail's foot: Settings (this view, as a dialog) and Add machine.

import { div, svg } from "gpui-kit";
import { v_flex, h_flex, InputState, Input } from "gpui-base";
import { run, theme, shared, setShared, terminals, panes, spaces, props, openOverlay, updates, layout, window, appHome, keys } from "herdr";
import Settings, { SECTIONS } from "./app.js";
import { needsYou, colorsOf, line } from "./tree.js";

const HIDDEN = "rw-rail.hidden"; // as rw-rail
const mac = window()?.platform === "macos";
// The app shows Keyboard on macOS only; here it also holds keys.json.
if (!SECTIONS.some((s) => s.id === "keyboard")) SECTIONS.splice(1, 0, { id: "keyboard", title: "Keyboard", icon: "keyboard" });

// Opens $1 in $VISUAL or $EDITOR, else nano or vi; says so and waits when none opens.
const EDIT = 'e=${VISUAL:-$EDITOR}; [ -n "$e" ] || for x in nano vi; do command -v "$x" >/dev/null && e=$x && break; done; '
  + '${e:-vi} "$1" || { printf "\\nNo editor opened %s: set EDITOR. Press Enter to close. " "$1"; read _; }';
const mids = new Map(); // machine name -> a number for its elements' ids (a name is never part of one)
const mid = (name) => (mids.has(name) ? mids.get(name) : mids.set(name, mids.size).get(name));
const find = (node, id) => (node?.id === id ? node : (node?.children ?? []).reduce((f, c) => f ?? find(c, id), null));

export default class RwSettings extends Settings {
  init(p, cx) {
    if (props()?.footer) return;
    super.init(p, cx);
    this.wrong = null;
    this.colorsInput = InputState.new({ placeholder: '{"accent": "#ff8800"}' });
    this.colorsInput.on("submit", (_e, cx) => {
      const r = colorsOf(this.colorsInput.value(), Object.keys(theme()));
      this.save(r, (q) => { if (r.value) q.colors = r.value; else delete q.colors; }, cx);
    });
    this.coreInput = InputState.new({ placeholder: "/path/to/hc" });
    this.coreInput.on("submit", (_e, cx) => {
      const v = this.coreInput.value().trim();
      const r = !v || /^(\/|~\/|[a-z]:[\\/])/i.test(v) ? { value: v } : { wrong: "Write the whole path, from / or ~/." };
      this.save(r, (q) => { if (r.value) q.core = r.value; else delete q.core; }, cx);
    });
  }

  save(r, edit, cx) {
    this.wrong = r.wrong ?? null;
    if (!r.wrong) { this.change(edit, cx); this.picking = null; this.handle.focus(); }
    cx.notify();
  }

  // A program in a new tab of a space on this computer, and this dialog closed so it shows. (A terminal.peek of an
  // `hc run --bg` terminal, as the rail's Log in again does, didn't stay up from this dialog.)
  inTab(name, script, args) {
    run("tab.new", { name, space: spaces().find((s) => !s.machine)?.id, argv: ["sh", "-c", script, "sh", ...args] });
    this.close();
  }

  // A setting with a value typed in place: the button opens a field under the row; Enter saves, Esc closes it (the
  // app's Esc closes whatever `picking` names).
  typed(t, which, title, about, shown, input, now) {
    const open = this.picking === which;
    return v_flex().w_full()
      .child(this.row(t, title, about, this.button(t, `rw-${which}`, open ? "Cancel" : shown, (_e, cx) => {
        this.picking = open ? null : which;
        this.wrong = null;
        if (open) this.handle.focus();
        else { input.set_value(now); input.focus(); }
        cx.notify();
      })))
      .when(open, (el) => el.child(v_flex().pb(12).gap(6)
        .child(Input.new(input).h(32).px(10).rounded(7).border_1().border_color(t.accent).bg(t.background).text_size(13).text_color(t.foreground))
        .child(div().text_size(12).text_color(this.wrong ? t.blocked : t.dim).child(this.wrong ?? "Enter to save, empty for the default · Esc to cancel"))));
  }

  // On by default unless `def` is false; the default is written as no key.
  flag(t, key, def, title, about) {
    const on = this.person[key] ?? def;
    return this.row(t, title, about, this.toggle(t, `rw-${key}`, on, (_e, cx) => this.change((q) => {
      if (!on === def) delete q[key]; else q[key] = !on;
    }, cx)));
  }

  look(t, cx) {
    const c = this.person.minimum_contrast ?? 1;
    const contrast = (d) => (_e, cx) => this.change((q) => { q.minimum_contrast = Math.round(Math.max(1, Math.min(21, (q.minimum_contrast ?? 1) + d)) * 10) / 10; }, cx);
    const colors = this.person.colors ?? {};
    const listed = Object.entries(colors).map(([k, v]) => `${k} ${v}`).join(", ");
    return super.look(t, cx)
      .child(div().h(18))
      .child(this.heading(t, "Terminals"))
      .child(this.flag(t, "font_ligatures", false, "Font ligatures", "Joins characters such as -> and != in fonts that have them."))
      .child(this.row(t, "Minimum contrast", "Terminal text below this ratio turns near-white or near-black. 1 leaves program colors alone; up to 21.",
        this.stepper(t, "rw-contrast", c.toFixed(1), contrast(-0.1), contrast(0.1))))
      .child(this.flag(t, "pane_scrollbars", true, "Scroll position in panes", "A thumb at a terminal's right edge while it has scrollback."))
      .child(div().h(18))
      .child(this.heading(t, "Colors"))
      .child(this.typed(t, "colors", "Accent and other colors", listed ? `On top of the theme: ${listed}.` : "None: the theme's own. Name a theme color, like accent.",
        "Edit", this.colorsInput, Object.keys(colors).length ? JSON.stringify(colors) : ""));
  }

  keyboard(t) {
    const keys = this.row(t, "What every key does", "In keys.json; Herdr applies a change at once.",
      this.button(t, "rw-keys", "Open keys.json", (_e, cx) => this.inTab("keys.json", EDIT, [`${appHome()}/keys.json`])));
    return v_flex().w_full()
      .when(mac, (el) => el.child(super.keyboard(t)).child(div().h(18)))
      .child(this.heading(t, "Keys")).child(keys);
  }

  // Agents asking you in a machine's spaces (as the rail counts them for a hidden machine).
  asksOn(m) {
    const on = new Set(spaces().filter((s) => (s.machine ?? null) === m).flatMap((s) => s.tabs.map((tab) => tab.id)));
    const shown = new Set(panes().filter((p) => on.has(p.tab)).map((p) => p.terminal));
    return needsYou(terminals()).filter((x) => shown.has(x.address)).length;
  }

  machineRow(t, m, version) {
    const hidden = (shared(HIDDEN) ?? []).includes(m.name);
    const asks = hidden ? this.asksOn(m.name) : 0;
    const set = (on) => { const h = shared(HIDDEN) ?? []; setShared(HIDDEN, on ? [...h.filter((x) => x !== m.name), m.name] : h.filter((x) => x !== m.name)); };
    return super.machineRow(t, m, version).child(h_flex().gap(6).items_center()
      .child(div().flex_1().min_w(0).text_size(12.5).text_color(asks ? t.blocked : t.dim)
        .child(hidden ? `Hidden from the rail${asks ? ` · ${asks} ${asks === 1 ? "asks" : "ask"} you` : ""}` : ""))
      // After `--`, a name that starts with a dash is still a name.
      .when(m.state === "needs_login", (el) => el.child(this.button(t, `rw-login-${mid(m.name)}`, "Log in again", () =>
        this.inTab(`log in to ${line(m.name, 40)}`, 'hc machine login -- "$1"; printf "\\nPress Enter to close. "; read _', [m.name]))))
      .child(this.button(t, `rw-hide-${mid(m.name)}`, hidden ? "Show in the rail" : "Hide from the rail", () => set(!hidden))));
  }

  machines(t) {
    return super.machines(t).child(div().pt(14).text_size(12.5).line_height("18px").text_color(t.dim)
      .child("Hiding a machine takes its spaces out of the rail; its terminals keep running, and an agent that asks you there still counts in Needs you."));
  }

  privacy(t) {
    const core = this.person.core ?? "";
    return super.privacy(t)
      .child(div().h(18))
      .child(this.heading(t, "Terminals"))
      .child(this.flag(t, "clipboard_write", true, "Programs may write the clipboard", "Lets terminal programs copy to this computer's clipboard (OSC 52), remote ones too. They can never read it."))
      .child(this.typed(t, "core", "herdr-core location", `${core || "Where Herdr looks: PATH, ~/.local/bin, Homebrew, Nix."} Read at start: restart Herdr after a change.`,
        core ? "Change" : "Default", this.coreInput, core));
  }

  // The palette key as bound (as workspace-status shows it).
  hint() {
    const mod = { cmd: mac ? "⌘" : "Ctrl+", ctrl: mac ? "⌃" : "Ctrl+", shift: mac ? "⇧" : "Shift+", alt: mac ? "⌥" : "Alt+", option: mac ? "⌥" : "Alt+" };
    const b = keys().find((k) => k.section === "global" && k.action === "app.palette");
    const parts = b && b.keys.endsWith("--") ? [...b.keys.slice(0, -2).split("-"), "-"] : b?.keys.split("-");
    return parts ? parts.map((p) => mod[p.toLowerCase()] ?? p.toUpperCase()).join("") : "Commands";
  }

  footer(t) {
    const narrow = (find(layout(), "sidebar")?.size?.px ?? Infinity) < 160;
    const root = layout(), panel = find(root, "panel");
    const cal = Boolean(find(root, "calendar")), calOn = Boolean(panel && !panel.hidden && find(root, "panel-body")?.active === "calendar");
    const row = (id, icon, label, dim, action, on = false) => h_flex().id(id).h(28).px(8).gap(9).items_center().rounded(8)
      .text_color(on ? t.foreground : dim ? t.dim : t.muted).when(on, (el) => el.bg(t.selected))
      .hover((s) => s.bg(t.hover).text_color(t.foreground)).cursor_pointer()
      .on_click(action).child(svg(icon.includes("/") ? icon : `mods/workspace-chrome/${icon}.svg`).size(14))
      .when(!narrow, (el) => el.child(label));
    return v_flex().size_full().bg(t.chrome).px(8).pt(4).pb(8).text_size(13)
      .child(row("settings", "settings", "Settings", false, () => openOverlay({ mod: "rw-settings", kind: "dialog", width: 860, height: 620 }))
        .when(Boolean(updates().app.ready), (el) => el.child(div().size(6).rounded_full().bg(t.accent)))
        // The palette's key, quietly (the user asked it off the bar); it opens the palette.
        .when(!narrow, (el) => el.child(div().flex_1()).child(div().id("palette").px(6).rounded(6).text_size(11).text_color(t.dim)
          .hover((s) => s.bg(t.input).text_color(t.foreground))
          .on_click((_e, cx) => { cx.stop_propagation(); run("app.palette"); }).child(this.hint()))))
      // The calendar panel's toggle (Part II.2), pressed while it shows; "calendar.opened" tells the panel to animate in.
      .when(cal, (el) => el.child(row("calendar", "mods/calendar/calendar.svg", "Calendar", false, () => {
        if (calOn) return run("layout.hide", { id: "panel" });
        setShared("calendar.opened", Date.now());
        run("layout.select", { stack: "panel-body", child: "calendar" }); run("layout.show", { id: "panel" });
      }, calOn)))
      .child(row("machine", "plus", "Add machine", true, () => run("mod.open", { name: "machine-add" })));
  }

  render(cx) {
    return props()?.footer ? this.footer(theme()) : super.render(cx);
  }
}
