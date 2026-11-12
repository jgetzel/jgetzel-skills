# Stop hook with a background Bash job running (board #82)

Claude Code **2.1.319**, interactive session in an hc terminal (not `claude -p`), project-level
command Stop hook that copies its stdin to a file.

## Result

- **(a) no background job:** the hook fires. `background_tasks` is `[]`.
- **(b) turn ends with a `run_in_background` `sleep 600` still running:** the hook **fires**, and
  `background_tasks` lists the job (`type: shell`, `status: running`, `command: sleep 600`).
  So `/goal`-style skipping while a shell runs does not apply to Stop hooks.
- **Block in (b):** `{"decision":"block","reason":"..."}` on stdout is fed back to the agent. The
  UI shows `Stop hook error: <reason>`, the agent ran another turn and obeyed the reason (replied
  `PINEAPPLE`). On that continuation the hook fired again with `stop_hook_active: true` and the job
  still `running`. The hook must not block unconditionally or it loops.
- `session_crons` was `[]` in both cases (none were set up).

## stdin (a)

```json
{"session_id":"4c3cf265-0a54-4615-97ef-5618db7000f2","transcript_path":"/home/jgetzel/.claude/projects/-tmp-claude-1000--home-jgetzel-workspace-jgetzel-skills-ll-58-d67fe35b-1d80-48be-91d5-09dee7cf929d-scratchpad-stophook/4c3cf265-0a54-4615-97ef-5618db7000f2.jsonl","cwd":"/tmp/claude-1000/-home-jgetzel-workspace-jgetzel-skills-ll-58/d67fe35b-1d80-48be-91d5-09dee7cf929d/scratchpad/stophook","scratchpad_dir":"/tmp/claude-1000/-tmp-claude-1000--home-jgetzel-workspace-jgetzel-skills-ll-58-d67fe35b-1d80-48be-91d5-09dee7cf929d-scratchpad-stophook/4c3cf265-0a54-4615-97ef-5618db7000f2/scratchpad","prompt_id":"60db7591-06be-43ec-a179-17d68c64dd55","permission_mode":"auto","effort":{"level":"medium"},"hook_event_name":"Stop","stop_hook_active":false,"last_assistant_message":"hello","background_tasks":[],"session_crons":[]}

```

## stdin (b), first stop

```json
{"session_id":"4c3cf265-0a54-4615-97ef-5618db7000f2","transcript_path":"/home/jgetzel/.claude/projects/-tmp-claude-1000--home-jgetzel-workspace-jgetzel-skills-ll-58-d67fe35b-1d80-48be-91d5-09dee7cf929d-scratchpad-stophook/4c3cf265-0a54-4615-97ef-5618db7000f2.jsonl","cwd":"/tmp/claude-1000/-home-jgetzel-workspace-jgetzel-skills-ll-58/d67fe35b-1d80-48be-91d5-09dee7cf929d/scratchpad/stophook","scratchpad_dir":"/tmp/claude-1000/-tmp-claude-1000--home-jgetzel-workspace-jgetzel-skills-ll-58-d67fe35b-1d80-48be-91d5-09dee7cf929d-scratchpad-stophook/4c3cf265-0a54-4615-97ef-5618db7000f2/scratchpad","prompt_id":"99ff2938-7f36-4428-b067-c1d3386df0e8","permission_mode":"auto","effort":{"level":"medium"},"hook_event_name":"Stop","stop_hook_active":false,"last_assistant_message":"started","background_tasks":[{"id":"bdpf9078e","type":"shell","status":"running","description":"Sleep for 10 minutes in the background","command":"sleep 600"}],"session_crons":[]}

```

## stdin (b), after the block (continuation)

```json
{"session_id":"4c3cf265-0a54-4615-97ef-5618db7000f2","transcript_path":"/home/jgetzel/.claude/projects/-tmp-claude-1000--home-jgetzel-workspace-jgetzel-skills-ll-58-d67fe35b-1d80-48be-91d5-09dee7cf929d-scratchpad-stophook/4c3cf265-0a54-4615-97ef-5618db7000f2.jsonl","cwd":"/tmp/claude-1000/-home-jgetzel-workspace-jgetzel-skills-ll-58/d67fe35b-1d80-48be-91d5-09dee7cf929d/scratchpad/stophook","scratchpad_dir":"/tmp/claude-1000/-tmp-claude-1000--home-jgetzel-workspace-jgetzel-skills-ll-58-d67fe35b-1d80-48be-91d5-09dee7cf929d-scratchpad-stophook/4c3cf265-0a54-4615-97ef-5618db7000f2/scratchpad","prompt_id":"99ff2938-7f36-4428-b067-c1d3386df0e8","permission_mode":"auto","effort":{"level":"medium"},"hook_event_name":"Stop","stop_hook_active":true,"last_assistant_message":"PINEAPPLE","background_tasks":[{"id":"bdpf9078e","type":"shell","status":"running","description":"Sleep for 10 minutes in the background","command":"sleep 600"}],"session_crons":[]}

```
