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
    case "idle": return box.rounded(size).border(2).border_color(t.idle ?? t.dim);
    case "run": return box.child(div().size(5).rounded(3).bg(t.foreground));
    case "prompt": return box.child(div().size(5).rounded(3).bg(t.dim));
  }
  return box;
}

// A hover highlight as a layer behind an element's content (UI-SPEC II.4b): it fades in over 90 ms and out over 140.
// The element is relative() and keeps `on` from its on_hover; the layer is its first child.
export const hoverLayer = (t, id, on, radius = 7) => div().id(id).absolute().inset_0().rounded(radius).bg(t.hover)
  .opacity(on ? 1 : 0).transition("opacity", on ? 90 : 140);
