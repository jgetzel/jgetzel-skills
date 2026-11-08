# sw-probe: Claude Code behaviors /swarm v1 depends on

Measured 2026-11-07 on Claude Code 2.1.316 (Linux, Claude Ultra plan) with
throwaway `--model haiku` sessions started by `relaunch/launch.sh <name> split
… --permission-mode auto --settings <file>`, cwd = this repo. Probe hooks
logged stdin and env to a jsonl file. Docs read: hooks, cross-session-messaging,
settings, settings-reference, env-vars, prompt-caching (code.claude.com/docs/en/*.md).

The probe sessions ran in a folder Claude Code already trusted. In a new
folder, a fresh session stops at the "trust this folder?" dialog, defaulting to
"No, exit", before any hook runs. `swarm spawn` has to start agents in a
trusted repo or worktree.

## 1. asyncRewake Stop waiter

**Config:**

```json
"Stop": [{"hooks": [{"type": "command", "command": "waiter.sh", "async": true, "asyncRewake": true, "timeout": N}]}]
```

`waiter.sh` polls a per-terminal file every 0.5 s. When the file appears, it
prints the contents to stdout and exits 2. It traps and logs signals.

**What was observed:**

- **Wake works on an idle interactive session.** The woken turn's
  `UserPromptSubmit` fires about 50 ms after the waiter exits 2. The cache was
  warm (46k `cache_read`).
- **What the model sees** is a user-role turn:

  ```
  [SYSTEM NOTIFICATION - NOT USER INPUT] … <task-notification><summary>Stop hook feedback</summary></task-notification>
  <system-reminder>Stop hook blocking error from command "Stop": <output></system-reminder>
  ```

  Stdout was used because stderr was empty; the docs prefer stderr. The
  model treated it as a notification and quoted it.
- **`stop_hook_active`** is `true` on the Stop that ends a rewoken turn.
- **Expiry.** At exactly `timeout` seconds (120.0 s measured), Claude Code
  sends SIGTERM to the waiter. Nothing is shown and nothing wakes. No new
  waiter starts until the next Stop, so from then on the agent can't be woken
  by the hook.
- **Ceiling.** Waiters with `timeout` 600, 3600 and 86400 all started, so all
  three values are accepted. For whether they outlive 600 s and 3600 s, see the
  addendum below.
- **Pile-up.** Every Stop starts a new waiter, and old waiters are never killed
  when a new turn starts, whether it came from `hc send`, `SendMessage` or a
  rewake. A stale waiter that fires still wakes the session. Each waiter lives
  until its own timeout.
- **Firing while the session is busy.** The rewake is delivered mid-turn, at
  the next tool round. `UserPromptSubmit` fires then (between `PostToolUse`
  and the final reply, with no Stop in between), and the content joins the same
  turn.
- **Turn starts.** `UserPromptSubmit` fired at every turn start seen. Its
  `prompt` begins with:
  - `<cross-session-message from=…` for a SendMessage wake;
  - `<task-notification>…Stop hook feedback` for a rewake, idle or mid-turn;
  - `<hc from=…>` for `hc send`.
- **Ending the session.** `hc kill` of the session SIGTERMs its live waiters,
  so no orphans are left.

**Consequences for the spec:**

- Hook wakes work. Keep mechanism 1, with the SendMessage nudge as the fallback
  for an agent with no live waiter. The merged code does this through
  `agent.waiter` plus a `/proc` check.
- The waiter must dedupe itself. The newest waiter owns the inbox, and older
  ones exit when `agent.waiter` isn't their own pid. The merged `cmd_wait` does
  this. A "status == working" check alone is racy: woken turns took 1.4–2 s,
  which can fall between two polls.
- Have `swarm wait` exit 0 a little before its own `timeout`, so the expiry
  path is ours and not a SIGTERM. The merged code waits 21000 s under a 21600 s
  hook timeout.

## 2. PostToolUse additionalContext

**Config:** a `PostToolUse` hook with matcher `Bash` prints:

```json
{"hookSpecificOutput": {"hookEventName": "PostToolUse", "additionalContext": "<N chars>"}}
```

**What was observed:**

- **It arrives mid-turn**, beside the tool result, as:

  ```
  <system-reminder>PostToolUse:Bash hook additional context: …</system-reminder>
  ```

  The transcript records it as an `attachment` of type `hook_additional_context`.
- **Size.** 500 and 9,500 characters came through inline. At 15,000 characters
  the text was replaced by:

  ```
  <persisted-output>Output too large (14.6KB). Full output saved to: <session dir>/tool-results/… Preview (first 2KB):
  ```

  That matches the documented 10,000-character cap. The docs add that Claude
  isn't asked to read the file.

**Consequence:** the hook's digest must stay under about 9,000 characters,
including the touch notices. Mark as read only the messages it includes, and
end with "N more: run `swarm read`". Otherwise a burst of messages is marked
read but only 2 KB of it is seen. **The merged `post-tool`/`prompt` hooks have
no cap.** The rewake stderr in `cmd_wait` probably falls under the same cap
(not tested).

## 3. PreToolUse on SendMessage

**Config:** `PreToolUse` with matcher `SendMessage`. It denies unless the
message starts with `[urgent]`:

```json
{"hookSpecificOutput": {"hookEventName": "PreToolUse", "permissionDecision": "deny", "permissionDecisionReason": "<R>"}}
```

**What was observed:**

- **`tool_input` fields:**

  ```
  {to, summary, message, type: "message", recipient, recipient_kind: "name", content}
  ```

  `to` and `recipient` hold the name exactly as the model typed it, which can
  include a ` [ref]` suffix. `message` == `content`.
- **Deny.** The tool returns `Error: <R>` verbatim. The model reported it and
  didn't retry.
- **`[urgent]`.** The resend with `[urgent]` (the hook printed nothing) went
  through, and auto mode allowed it.

**Consequence:** the spec's cold-wake guard works as written. The merged code
strips ` [` from `to`, which is correct.

## 4. Compaction

**Config:** log hooks on `PreCompact`, `PostCompact` and `SessionStart`.
Auto compaction was forced with:

```json
"autoCompactWindow": 100000, "env": {"CLAUDE_AUTOCOMPACT_PCT_OVERRIDE": "45"}
```

Manual compaction: `/compact keep it short`, typed with `hc keys`. `hc send`
wraps the text in `<hc …>`, so a slash command sent that way runs as a prompt.

**What was observed:**

- **Auto compaction**, at turn start, after `UserPromptSubmit`:
  1. `PreCompact {trigger: "auto", custom_instructions: null}`;
  2. `SessionStart {source: "compact"}`;
  3. `PostCompact {trigger: "auto", compact_summary}`.
- **A PreCompact without a compaction.** Once, `PreCompact(auto)` fired and no
  compaction followed: no boundary and no PostCompact. The next turn compacted.
- **Manual `/compact`:** `PreCompact {trigger: "manual", custom_instructions:
  "keep short"}`, then `SessionStart(compact)`, then `PostCompact(manual)`.
  No `UserPromptSubmit` or Stop fires around it.
- **Transcript.** Compaction writes this line:

  ```json
  {"type":"system","subtype":"compact_boundary","compactMetadata":{"trigger","preTokens","postTokens","durationMs",…}}
  ```

  `postTokens` (13.7k) leaves out the system prompt and tools. The next request
  was 53.5k = 31.1k `cache_read` + 22.4k `cache_creation`.
- **Context tokens.** Take the last `"type":"assistant"` line's
  `message.usage`, and sum `input_tokens + cache_read_input_tokens +
  cache_creation_input_tokens`. `usage.cache_creation.ephemeral_1h_input_tokens`
  vs `ephemeral_5m_input_tokens` shows which TTL is in effect.
- **Idle compaction:** see the addendum below.

**Consequences:**

- `SessionStart` with `source == "compact"` (or PostCompact) is the right
  signal. Never use PreCompact.
- At that moment, the last assistant usage in the transcript is still the
  **pre-compaction** size. The merged hook's `ctx_from()` therefore stores the
  old, high size until the next Stop. The cold rule is unaffected, because
  `compacted_at >= last_active`, but `swarm who` overstates context. A fix is
  `compactMetadata.postTokens` plus the session's baseline, or leaving
  ctx_tokens alone until the next Stop.

## 5. `--settings <file>` through launch.sh

**Config:** one file holding `hooks`, `env` (`SWARM_NAME`, `SWARM_DB`,
`CLAUDE_CODE_IDLE_COMPACT_MIN_TOKENS`), `crossSessionInbound` and
`promptCacheTtl`. A second file held `"crossSessionInbound": "refuse"` and
`"promptCacheTtl": "5m"`.

**What was observed:**

- **Everything took effect:**
  - the hooks ran;
  - the `env` values were visible in hooks and in the Bash tool;
  - `refuse` stopped a SendMessage from starting any turn. The sender's
    SendMessage still returned `success: true`. Several minutes later the
    sender got a turn-starting `[Cross-session delivery notice] Your message …
    was refused` with the msg_id;
  - `"5m"` produced `ephemeral_5m` cache writes.

  This account defaults to the 1 h TTL, so `"1h"` only pins it.
- **Hooks stack** with `~/.claude/settings.json` and plugins. Each Stop ran 4
  hooks: the user's impeccable hook, the orchestrator-pane guard, and the two
  from `--settings`. Ponytail's plugin SessionStart also injected its prompt.
- **Sender mode.** Auto-mode sessions send as `from-mode="prompting"`, the same
  class as auto receivers, so `accept` changed nothing between them. It matters
  only for mixed modes.

**Consequences:**

- Swarm agents inherit the user's hooks and plugins, so their Stop runs those
  too. Today that's harmless: the orchestrator guard fires only when
  `.claude/orchestrator/pane` names that agent's terminal.
- `launch.sh` strips `CLAUDE*` from the environment, so swarm variables must
  live in the settings file's `env`, as the template does.

## 6. Identity in hooks

**What was observed:**

- **Input fields.** Every event gets `session_id`, `transcript_path`, `cwd` and
  `scratchpad_dir`. `session_title`, which is the `-n` name, appears only on
  `SessionStart` and `UserPromptSubmit`, not on tool events or Stop.
- **Hook env:**
  - `SWARM_*` from `--settings`;
  - `HC_TERMINAL_ID`, `HC_TERMINAL_SOCKET`, `HC_SCOPE`;
  - `CLAUDE_CODE_SESSION_ID`, `CLAUDE_CODE_MESSAGING_SOCKET`, `CLAUDE_PID`,
    `CLAUDE_PROJECT_DIR`.

**Consequence:** hooks identify the agent by env `SWARM_NAME`, and
`HC_TERMINAL_ID` gives its terminal.

## Addendum (timeouts, idle compaction)

### Timeout ceiling

**What was observed:**

| `timeout` | Outcome |
|---|---|
| 120 | SIGTERM at 120.0 s |
| 600 | SIGTERM at 600.0 s |
| 3600 | SIGTERM at 3600.0 s |
| 86400 | Still alive at 3628 s. Fired at 61 min, it woke the session normally. |

No ceiling showed up at 3600 s or below, so the merged 21600 s is very likely
honoured. Past one hour it is untested.

**The late wake's cost:** `cache_read` was 31,104 and `cache_creation` was
15,738.

- The conversation part had passed its 1 h TTL, so it was written again.
- The 31k system-and-tools prefix was still warm. Other haiku sessions on this
  account were probably keeping it warm.

So a cold wake costs about the conversation's size, not the whole context.
The cold rule's estimate of "~ctx_tokens uncached" is high by roughly the
shared prefix (about 31k here). That's fine as a conservative estimate.

### Idle compaction: not seen

**Config:** session swp-i ran haiku 5.5, interactive, under `--settings` with
`promptCacheTtl: "1h"` and `env.CLAUDE_CODE_IDLE_COMPACT_MIN_TOKENS =
"100000"`, auto-compaction on by default. It read docs until its context was
241,646 tokens (1 h cache writes confirmed). Then it sat idle.

**What was observed:** it did not compact within 76 minutes of its last
request:

- no `PreCompact`, `PostCompact` or `SessionStart(compact)`;
- no `compact_boundary` in the transcript;
- the only hook event while idle was `Notification(idle_prompt)` at 60 s.

It never auto-compacted at 241k either, so haiku 5.5's window here is
larger than 200k. The cause is unknown. Candidates are a server-side feature
flag, a size condition relative to that larger window, or an "attended"
condition. The probe can't tell these apart.

**Consequence:** don't count on idle compaction to make idle agents cheap.

- The cold-cache guard (PreToolUse on SendMessage, `swarm post`/`wait`) is
  what actually prevents expensive wakes. Keep it as the primary mechanism.
- If idle compaction does happen, the hooks will see `SessionStart(compact)`,
  as for manual and auto compaction. That is unverified for the idle path,
  whose `trigger` value is also unknown.
- To make idle compaction testable, rerun with an opus/sonnet agent on a 200k
  window, or ask whether the flag is on for this account.
