import SwarmLean.Lib.Hook

/-! The hook's JSON answer against what the Lua (cjson) prints. -/

open SwarmLean.Hook

#guard jstr "a/\x7f\x01\x08\x0cé\"\\" == "\"a/\\u007f\\u0001\\b\\fé\\\"\\\\\""
#guard emitText "PreToolUse" (some "ctx") (some "no") ==
  "{\"hookSpecificOutput\": {\"hookEventName\": \"PreToolUse\", \"permissionDecision\": \"deny\", \"permissionDecisionReason\": \"no\", \"additionalContext\": \"ctx\"}}"
#guard emitText "PostToolUse" (some "") none == "{\"hookSpecificOutput\": {\"hookEventName\": \"PostToolUse\"}}"
