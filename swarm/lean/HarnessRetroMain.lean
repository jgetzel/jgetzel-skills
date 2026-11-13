import HarnessRetro

/-! harness-retro: the harness-retro skill's tools in one binary, the first word picking the tool (../../harness-retro's
`<tool>.sh` launchers pass their own name). -/

def main (args : List String) : IO UInt32 := do
  match args with
  | "transcript" :: rest => HarnessRetro.Transcript.main rest
  | "time-report" :: rest => HarnessRetro.TimeReport.main rest
  | "harness-lint" :: rest => HarnessRetro.Lint.main rest
  | "probe-guard" :: rest => HarnessRetro.Probe.guard rest
  | "probe-json" :: rest => HarnessRetro.Probe.json rest
  | _ =>
    IO.eprintln "usage: harness-retro transcript|time-report|harness-lint|probe-guard|probe-json ARGS..."
    return 2
