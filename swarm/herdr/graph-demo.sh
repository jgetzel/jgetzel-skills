#!/bin/sh
# Dependencies for the Board's graph (board #190), inside shot.sh's sandbox after rail-demo.sh's real preset:
#   swarm/herdr/shot.sh --rework real --before 'sh swarm/herdr/graph-demo.sh; <clicks>' out.png
# The ll swarm's board gets a chain (done #175, then #182, #183, #184), a diamond (#188 after #179 and #180, both after
# done #177), a done pair (#174 after #173), tasks with no edges (#167 held, #181, #170, #171) and a queue of #188, #184,
# #181, #182; then the Board shows. Its List | Graph switch and the scopes are clicked (xdotool) after it.
set -eu
[ -n "${HERDR_APP_HOME:-}" ] && case $HERDR_APP_HOME in /tmp/hs.*) ;; *) false ;; esac ||
  { echo "graph-demo.sh: only inside shot.sh's sandbox" >&2; exit 2; }
db=$(dirname "$HERDR_APP_HOME")/w/jgetzel-skills/.git/swarm/swarm.db
sqlite3 -cmd ".timeout 9000" "$db" "
  insert or replace into task(id, title, state, owner) values
    (182, 'Rail: fold a space''s tabs under its heading', 'open', null),
    (183, 'Rail: remember folds across restarts', 'open', null),
    (184, 'Rail: fold all but the shown space', 'open', null),
    (188, 'Herdr rework: ship the real preset as the default shot', 'open', null);
  update task set deps = '175' where id = 182; update task set deps = '182' where id = 183; update task set deps = '183' where id = 184;
  update task set deps = '177' where id in (179, 180); update task set deps = '179,180' where id = 188;
  update task set deps = '173' where id = 174; update task set hold = 'waits for the user''s go' where id = 167;
  update task set qpos = case id when 188 then 1 when 184 then 2 when 181 then 3 when 182 then 4 end where id in (188, 184, 181, 182)"
sleep 4 # rw-bar's commands are ignored until the preset settles
herdr-app do rw-bar.board >/dev/null
