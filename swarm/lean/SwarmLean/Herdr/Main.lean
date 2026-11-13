import SwarmLean.Herdr.Events
import SwarmLean.Herdr.Install

/-! herdr-mods: this repo's Herdr mods tools. `install` installs the Swarm and Calendar panels (Install.lean);
`events` is the Calendar panel's feed (Events.lean). herdr-mods/herdr-mods runs it. -/

def main (args : List String) : IO UInt32 := do
  match args with
  | "install" :: _ => SwarmLean.Herdr.Install.main
  | "events" :: rest => SwarmLean.Herdr.Events.main rest
  | _ => IO.eprintln "usage: herdr-mods install | herdr-mods events [--ics FILE] [--date YYYY-MM-DD] [--test]"; return 2
