#!/usr/bin/env bash
# Replay one task under two harnesses in herdr tabs, for a blind comparison. See probe.md.
#
#   probe.sh setup  RECORD.md OUT   two detached worktrees at the record's commit; prints which side to edit
#   probe.sh launch OUT             commit each side's harness, start both agents, send the prompt
#   probe.sh wait   OUT [MIN]       until both end with PROBE DONE, block, or MIN (45) minutes pass;
#                                   then writes OUT/judge/{prompt.md,a.md,a.diff,b.md,b.diff}
#   probe.sh clean  OUT             close the tabs, remove the worktrees
#
# OUT/state holds the sides; `cand=` names the candidate side. Never hand OUT/state to the judge.
set -euo pipefail
here=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
json() { "$here/probe-json.sh" get "$1"; }

case ${1:-} in
setup)
  rec=$(readlink -f "$2"); out=$(mkdir -p "$3" && cd "$3" && pwd)
  [ -e "$out/state" ] && { echo "$out/state exists; use a new OUT" >&2; exit 1; }
  repo=$(git -C "$(dirname "$rec")" rev-parse --show-toplevel)
  commit=$(sed -n 's/^commit: *//p' "$rec" | head -1)
  [ -n "$commit" ] || { echo "$rec has no 'commit:' line" >&2; exit 1; }
  id=$(od -An -N2 -tx1 /dev/urandom | tr -d ' \n')
  cand=$([ $((RANDOM % 2)) = 0 ] && echo a || echo b)
  awk 'NR==1 && /^---$/ {f=1; next} f && /^---$/ {f=0; next} !f' "$rec" > "$out/prompt.md"
  printf 'repo=%q\ncommit=%q\nid=%s\ncand=%s\n' "$repo" "$commit" "$id" "$cand" > "$out/state"
  for s in a b; do
    wt="$(dirname "$repo")/.$(basename "$repo")-worktrees/probe-$id-$s"
    GIT_LFS_SKIP_SMUDGE=1 git -C "$repo" worktree add -q --detach "$wt" "$commit"
    [ -f "$repo/.claude/settings.local.json" ] && mkdir -p "$wt/.claude" && cp "$repo/.claude/settings.local.json" "$wt/.claude/"
    mkdir -p "$out/$s"; : > "$out/$s/append.md"
    "$here/probe-json.sh" settings "$here/probe-guard.sh" "$wt" "$repo" > "$out/$s/settings.json"
    printf 'wt_%s=%q\n' "$s" "$wt" >> "$out/state"
  done
  . "$out/state"; w=wt_$cand
  echo "candidate side: $cand. Make the candidate change in ${!w} (repo harness: CLAUDE.md, .claude/, scripts),"
  echo "in $out/$cand/settings.json (extra hooks), or in $out/$cand/append.md (always-on text from outside the repo)."
  echo "Leave side $([ "$cand" = a ] && echo b || echo a) as it is, then: probe.sh launch $out"
  ;;
launch)
  out=$(cd "$2" && pwd); . "$out/state"
  for s in a b; do
    w=wt_$s; wt=${!w}; name=probe-$id-$s
    git -C "$wt" add -A
    git -C "$wt" -c user.name=probe -c user.email=probe@localhost commit -q --no-verify --allow-empty -m "probe start"
    printf 'start_%s=%s\n' "$s" "$(git -C "$wt" rev-parse HEAD)" >> "$out/state"
    tab=$(herdr tab create --label "$name" --no-focus --cwd "$wt")
    pane=$(json 'd.result.root_pane.pane_id' <<<"$tab")
    printf 'tab_%s=%s\n' "$s" "$(json 'd.result.tab.tab_id or d.result.tab.id' <<<"$tab")" >> "$out/state"
    args=(--permission-mode auto -n "$name" --settings "$out/$s/settings.json" --disallowedTools AskUserQuestion)
    [ -s "$out/$s/append.md" ] && args+=(--append-system-prompt-file "$out/$s/append.md")
    if ! herdr agent start "$name" --kind claude --pane "$pane" -- "${args[@]}" >/dev/null; then
      herdr agent read "$name" --source recent-unwrapped --lines 30 || true
      echo "agent $name did not start (trust dialog?); show the user, then probe.sh clean $out" >&2; exit 1
    fi
    herdr agent prompt "$name" "$(cat "$here/probe-preamble.md" "$out/prompt.md")" >/dev/null
    printf 'sid_%s=%s\n' "$s" "$(herdr agent get "$name" | json 'd.result.agent.agent_session.value')" >> "$out/state"
  done
  echo "launched probe-$id-a and probe-$id-b; next: probe.sh wait $out (run_in_background)"
  ;;
wait)
  out=$(cd "$2" && pwd); . "$out/state"
  deadline=$(( $(date +%s) + ${3:-45} * 60 ))
  for s in a b; do
    name=probe-$id-$s; st=timeout; v=sid_$s; sid=${!v:-}
    tx=$(ls ~/.claude/projects/*/"$sid.jsonl" 2>/dev/null | head -1)
    while :; do
      [ -n "$tx" ] && "$here/transcript.sh" "$tx" --last | grep -q 'PROBE DONE' && { st=done; break; }
      [ "$(date +%s)" -lt "$deadline" ] || break
      herdr agent wait "$name" --timeout $(( (deadline - $(date +%s)) * 1000 )) >/dev/null 2>&1 || true
      info=$(herdr agent get "$name" 2>/dev/null) || { st=gone; break; }
      tx=$(ls ~/.claude/projects/*/"$sid.jsonl" 2>/dev/null | head -1)
      [ -n "$tx" ] && "$here/transcript.sh" "$tx" --last | grep -q 'PROBE DONE' && { st=done; break; }
      [ "$(json 'd.result.agent.agent_status' <<<"$info")" = blocked ] && { st=blocked; break; }
      sleep 60
    done
    printf 'status_%s=%s\ntx_%s=%q\n' "$s" "$st" "$s" "$tx" >> "$out/state"
  done
  . "$out/state"; mkdir -p "$out/judge"; cp "$out/prompt.md" "$out/judge/"
  for s in a b; do
    w=wt_$s; t=tx_$s; r=start_$s
    [ -n "${!t}" ] && "$here/transcript.sh" "${!t}" --redact "${!w}=<checkout>" --redact "probe-$id-$s=probe" > "$out/judge/$s.md"
    git -C "${!w}" add -A -N && git -C "${!w}" diff "${!r}" > "$out/judge/$s.diff"
  done
  grep '^status_' "$out/state"; ls "$out/judge"
  ;;
clean)
  out=$(cd "$2" && pwd); . "$out/state"
  for s in a b; do
    t=tab_$s; w=wt_$s
    [ -n "${!t:-}" ] && herdr tab close "${!t}" >/dev/null 2>&1 || true
    git -C "$repo" worktree remove --force "${!w}" 2>/dev/null || true
  done
  git -C "$repo" worktree prune
  echo "cleaned probe-$id"
  ;;
*) sed -n '2,11p' "$0"; exit 2 ;;
esac
