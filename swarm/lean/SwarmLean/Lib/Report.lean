import SwarmLean.Lib.Re

/-! swarm-report's patterns, here because Report.lean, an executable's root, is not importable by `Tests/Re.lean`. -/

namespace SwarmLean.Report

/-- `--since`'s date and optional time parts. -/
def SINCE : Re.Pat := .lit "\\A(\\d+)-(\\d+)-(\\d+)[T ]?(\\d*):?(\\d*):?(\\d*)\\z"

end SwarmLean.Report
