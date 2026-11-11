-- ensureComms (model Comms.lean, findings #22 to #24): join refuses a communicator terminal outside the swarm's space or
-- bound to another swarm; watchd launches a missing communicator in the swarm's space and holds auto-spawn when it can't.
local json, util = require "swarm.json", require "swarm.util"
local T = {}

local function put(path, text, mode)
  local f = assert(io.open(path, "w")); f:write(text); f:close()
  if mode then os.execute("chmod " .. mode .. " " .. util.shquote(path)) end
end

-- hc: ls from hc.json, get <t> prints labels from label.<t>.json, label <t> k=v writes swarm.comms
local function setup(t, terms, labels)
  t:fakes()
  local D = util.shquote(t.d)
  t:fake("hc", ([[#!/bin/sh
D=%s
case "$1" in
  ls) cat $D/hc.json; echo ;;
  get) cat $D/label.$2.json 2>/dev/null || echo '{}' ;;
  label) shift; a=$1; shift; echo "$a $*" >> $D/labels.log ;;
  *) echo '{}' ;;
esac
]]):format(D))
  t:set_hc(unpack(terms))
  for a, l in pairs(labels or {}) do put(t.d .. "/label." .. a .. ".json", json.encode({ labels = l })) end
  put(t.launch, ([[#!/bin/sh
echo "$1 space=$SWARM_SPACE" >> %s/launch.space
[ -f %s/launch.fail ] && { echo "no Herdr window" >&2; exit 1; }
echo t9
]]):format(D, D), "755")
end
local function join(t, who, hc, flag)
  local a = { "join", flag, { hc = hc, ok = false } }
  if not flag then table.remove(a, 2) end
  return t:sw(who, unpack(a))
end
local function meta(t, k) local r = t:q("select v from meta where k='" .. k .. "'") return r[1] and r[1].v end

function T.test_join_records_space_and_labels(t)
  setup(t, { { address = "t1" } }, { t1 = { ["herdr.space"] = "s1" } })
  t:q("insert or replace into meta(k,v) values('comms','c')")
  t:eq(join(t, "c", "t1").code, 0)
  t:eq(meta(t, "space"), "s1")
  t:has(t:calls("labels"), "t1 swarm.comms=" .. t.db)
end

function T.test_join_refused_outside_space_even_with_takeover(t)
  setup(t, { { address = "t1" } }, { t1 = { ["herdr.space"] = "s2" } })
  t:q("insert or replace into meta(k,v) values('comms','c')")
  t:q("insert or replace into meta(k,v) values('space','s1')")
  for _, f in ipairs({ false, "--takeover" }) do
    local r = join(t, "c", "t1", f)
    t:eq(r.code ~= 0, true)
    t:has(r.stderr, "space s1")
  end
end

function T.test_join_refused_for_another_swarms_communicator(t)
  setup(t, { { address = "t1" } }, { t1 = { ["herdr.space"] = "s1", ["swarm.comms"] = "/other/swarm.db" } })
  t:q("insert or replace into meta(k,v) values('comms','c')")
  local r = join(t, "c", "t1")
  t:eq(r.code ~= 0, true)
  t:has(r.stderr, "another swarm")
  t:eq(join(t, "c", "t1", "--takeover").code, 0)
end

local function tick(t) t:sw("a", "watchd", "--once", "--comms", "c", "--max-agents", "1", "--min-free-mem", "0", { hc = false }) end

function T.test_watchd_launches_missing_communicator_in_space(t)
  setup(t, { { address = "t3" } })
  t:agent("a", { status = "working" })
  t:q("insert or replace into meta(k,v) values('space','s1')")
  tick(t)
  t:has(util.slurp(t.d .. "/launch.space"), "c space=s1")
  t:eq(t:q("select hc from agent where name='c'")[1].hc, "t9")
  t:has(t:calls("labels"), "t9 swarm.comms=" .. t.db)
end

function T.test_watchd_leaves_a_good_communicator(t)
  setup(t, { { address = "t1" } }, { t1 = { ["herdr.space"] = "s1", ["swarm.comms"] = t.db } })
  t:agent("a", { status = "working" })
  t:q("insert or replace into meta(k,v) values('space','s1')")
  t:eq(join(t, "c", "t1").code, 0)
  tick(t)
  t:eq(util.slurp(t.d .. "/launch.space"), nil)
end

function T.test_watchd_holds_autospawn_when_comms_cant_launch(t)
  setup(t, { { address = "t3" } })
  t:agent("a", { status = "working" })
  t:q("insert or replace into meta(k,v) values('space','s1')")
  t:q("insert into task(title,state) values('x','open')")
  put(t.d .. "/launch.fail", "")
  tick(t)
  tick(t)  -- inside the backoff: no second launch attempt
  t:eq(#util.splitlines(util.slurp(t.d .. "/launch.space")), 1)
  t:has(meta(t, "spawn_held"), "no communicator can be launched")
end

return T
