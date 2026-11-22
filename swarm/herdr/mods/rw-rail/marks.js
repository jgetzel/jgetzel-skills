// The spec's marks (UI-SPEC.md, Marks), drawn for rw-rail, rw-bar and rw-pane; the other two link this file.
import { div, svg } from "gpui-kit";
import { h_flex } from "gpui-base";

export function mark(t, kind, size = 9) {
  const box = h_flex().size(size).flex_none().items_center().justify_center();
  switch (kind) {
    case "working": return svg("mods/workspace-chrome/spinner.svg").size(size + 1).flex_none().text_color(t.working).spin(900);
    case "done": return box.rounded(size).bg(t.done);
    case "asks": return box.rounded(2).bg(t.blocked);
    case "hung": return box.rounded(2).border(2).border_color(t.blocked);
    case "gone": return box.child(div().w(size - 2).h(2).rounded(1).bg(t.dim));
    case "idle": return box.rounded(size).border(2).border_color(t.idle ?? t.dim);
    case "run": return box.child(div().size(5).rounded(3).bg(t.foreground));
    case "prompt": return box.child(div().size(5).rounded(3).bg(t.dim));
  }
  return box;
}

// One button set for the rw mods (round 4, proposal 3): "solid" the light main action of a card (never coral: coral is
// only what waits on you, proposal 2), "outline" the rest, with a fill so it keeps its shape on a tinted card, "link"
// text for what navigates.
export function look(el, t, kind = "outline") {
  if (kind === "solid") return el.bg(t.solid ?? t.foreground).text_color(t.solid_foreground ?? t.background).font_semibold().hover((s) => s.opacity(0.9));
  if (kind === "link") return el.text_color(t.muted).hover((s) => s.text_color(t.foreground));
  return el.border(1).border_color(t.input).bg(t.background).text_color(t.foreground).hover((s) => s.bg(t.hover));
}
