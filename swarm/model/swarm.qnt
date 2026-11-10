// The coordination swarm/lua/swarm implements: the board, leases and watchd's reaping and auto-spawn, locks,
// agents, and inboxes. swarm/model/README.md lists every property as a sentence and says what is proved,
// what is only replayed against the Lua (../lua/test/cli_model_spec.lua), and what is not modelled.
module swarm {
  // ---------- parameters ----------
  const AGENTS: List[str]  // agent slots; the first ROSTER are live at the start, a spawn fills the first not live
  const ROSTER: int        // also watchd's --max-agents: it refills the roster, never grows it
  const NTASKS: int
  const PATTERNS: Set[str] // lock patterns agents may take
  const PATHS: Set[str]    // concrete files, to judge whether two patterns overlap
  const RELEASE: str       // which lapsed claims reap reopens: "ended" (before #106), "notWorking" (b04cf08), "idle" (now)
  const ANSWER_ON_TASK: bool // unblock --answer is stored on the task (since #106)
  const RACY: bool         // claim, and the waiter's delivery, are a read then a write, as the Lua runs them
  const CLAIM_CHECKS_DEPS: bool // claim's write rechecks the deps (since #112); before, only state='open'
  // (task done --evidence "" is accepted before #113: "emptyEvidence" in OFF is the code since)
  const LOCK_OVERLAP: bool // swarm lock refuses any common file (since #114); before, only one covering the other
  const DELIVER_CAS: bool  // a delivery moves the cursor only from where it read, else reads again (since #115)
  const PASSED_OVER: bool  // lifecycle ends a reusable agent told of the whole pool, inbox read, idle again (since #116)
  const WAITER_ALIVE: bool // lifecycle keeps an agent reusable only while its waiter is alive (since #119)
  // what the environment can't do in this instance, so the checker can exhaust it: "deps" (add --after, task after),
  // "block" (block, unblock), "big" (a context too big to reuse), "cold", "waiterGone" (the Stop hook's waiter
  // times out at 21000 s), "leave" (swarm leave, a dead terminal), "hc" (permission prompts), "prompt" (a turn the
  // waiter didn't start), "emptyEvidence" (task done --evidence "")
  const OFF: Set[str]
  const COMPACT: bool      // drop messages their reader has passed, renumbering: finite inboxes, no `seen` ghost
  const MAX_LOG: int       // without COMPACT, messages the model holds; a system post past it is lost
  const MAX_POSTS: int     // peer posts, a bound for the checker
  const COMMS: str

  pure val NAMES: Set[str] = AGENTS.foldl(Set(), (acc, x) => acc.union(Set(x)))
  pure val TASKS: Set[int] = 1.to(NTASKS)
  pure val IDS: List[int] = range(1, NTASKS + 1)  // in id order, as the Lua's selects return them
  pure def imax(x: int, y: int): int = if (x > y) x else y
  pure def on(f: str): bool = not(OFF.contains(f))

  // locks.covers(path, pat) for the strings below, from the Lua's rule: equal, fnmatch (no FNM_PATHNAME),
  // or under the pattern as a directory. The replay checks the CLI agrees.
  pure val COVERS: Set[(str, str)] = Set(
    ("m/", "m/"), ("m/a.lua", "m/"), ("m/*.lua", "m/"), ("m/a*", "m/"), ("m/b.lua", "m/"), ("m/a.txt", "m/"),
    ("m/a.lua", "m/a.lua"),
    ("m/a.lua", "m/*.lua"), ("m/*.lua", "m/*.lua"), ("m/b.lua", "m/*.lua"),
    ("m/a.lua", "m/a*"), ("m/a*", "m/a*"), ("m/a.txt", "m/a*"))
  pure def covers(x: str, pat: str): bool = COVERS.contains((x, pat))
  // what a lock is for: some file both patterns cover
  pure def overlap(p: str, q: str): bool = PATHS.exists(f => covers(f, p) and covers(f, q))
  // what `swarm lock` refuses: before #114, either pattern covering the other taken as a path; since, any common file
  pure def refuses(p: str, q: str): bool = if (LOCK_OVERLAP) overlap(p, q) else covers(p, q) or covers(q, p)

  // ---------- state ----------
  // task.st: absent (not added yet), open, claimed, blocked, done, dropped
  type Task = { st: str, owner: str, deps: Set[int], lease: bool, ev: bool, answer: bool, hcq: bool }
  // agent.st: unborn, working, idle, blocked (an hc prompt), ended. believes: tasks it thinks it holds.
  // aged: idle 2+ min (lifecycle may end or reuse it); cold: idle past the cache with a big context.
  type Agent = { st: str, waiter: bool, big: bool, aged: bool, cold: bool, boot: bool, told: Set[int],
    believes: Set[int], snap: List[int], reading: int }
  type Lock = { holder: str, exp: bool }  // holder "" is no row
  type Msg = { frm: str, to: str, urgent: bool, kind: str, task: int }  // kind: dm, answer, released, digest
  type State = {
    task: int -> Task, ag: str -> Agent, lock: str -> Lock,
    log: List[Msg],            // msg ids are positions, from 1
    cursor: str -> int, start: str -> int, seen: str -> List[int],  // seen: ids shown to the agent, in order
    pend: Set[int],            // tasks whose unblock answer the holder hasn't seen
    early: bool,               // ghost: some claim happened while a task it is after wasn't done
    posts: int
  }
  var s: State

  // ---------- queries ----------
  // lookups by a field that may be empty ("" owner, task 0): TLC evaluates both sides of and/or
  pure val NOBODY: Agent = { st: "unborn", waiter: false, big: false, aged: false, cold: false, boot: false, told: Set(),
    believes: Set(), snap: [], reading: 0 }
  pure def agOf(st: State, a: str): Agent = if (NAMES.contains(a)) st.ag.get(a) else NOBODY
  pure def ownerOf(st: State, t: int): str = if (TASKS.contains(t)) st.task.get(t).owner else ""
  pure def live(g: Agent): bool = g.st != "unborn" and g.st != "ended"
  pure def depsDone(st: State, t: int): bool = st.task.get(t).deps.forall(d => st.task.get(d).st == "done")
  pure def startable(st: State, t: int): bool = st.task.get(t).st == "open" and depsDone(st, t)
  pure def pool(st: State): Set[int] = TASKS.filter(t => startable(st, t))
  pure def holds(st: State, a: str): bool = TASKS.exists(t => st.task.get(t).owner == a and Set("claimed", "blocked").contains(st.task.get(t).st))
  pure def lockHeld(st: State, a: str): bool = PATTERNS.exists(p => st.lock.get(p).holder == a)
  pure def members(st: State): int = NAMES.filter(a => live(st.ag.get(a))).size()
  pure def addressed(st: State, a: str, i: int): bool = {
    val m = st.log[i - 1]
    (m.to == a or m.to == "@all") and m.frm != a
  }
  pure def unread(st: State, a: str): List[int] =
    range(st.cursor.get(a), st.log.length()).foldl([], (acc, i) => if (addressed(st, a, i + 1)) acc.append(i + 1) else acc)
  pure def wakes(st: State, a: str): bool = {
    val u = unread(st, a)
    u.length() > 0 and (not(st.ag.get(a).cold) or u.foldl(false, (b, i) => b or st.log[i - 1].urgent))
  }
  pure def nextTask(st: State): int = TASKS.filter(t => st.task.get(t).st != "absent").size() + 1
  // the slot a spawn fills: the first not live. An ended agent's slot is a new agent (the Lua's next name).
  pure def nextAgent(st: State): str = AGENTS.foldl("", (r, a) => if (r == "" and not(live(st.ag.get(a)))) a else r)
  // the cycle `task after` refuses: does t reach target along deps?
  pure def reaches(st: State, t: int, target: int): bool =
    1.to(NTASKS).fold(Set(t), (r, _i) => r.union(r.fold(Set(), (acc, x) => acc.union(st.task.get(x).deps)))).contains(target)

  // ---------- state changes (pure, so watchd's tick composes them) ----------
  pure def setTask(st: State, t: int, f: Task => Task): State = { ...st, task: st.task.setBy(t, f) }
  pure def setAg(st: State, a: str, f: Agent => Agent): State = { ...st, ag: st.ag.setBy(a, f) }
  pure def post(st: State, m: Msg): State = {
    val x = compact(st)
    if (COMPACT or x.log.length() < MAX_LOG) { ...x, log: x.log.append(m) } else x
  }
  // COMPACT: a message is gone once its reader's cursor passed it, or its reader is not live (a new agent in the
  // slot starts past it); ids are renumbered, and each cursor becomes the count of messages left at or below it
  pure def gone(st: State, i: int): bool = {
    val m = st.log[i - 1]
    not(live(agOf(st, m.to))) or st.cursor.get(m.to) >= i
  }
  pure def renum(keep: List[int], i: int): int = keep.foldl(0, (n, j) => if (j <= i) n + 1 else n)
  pure def compact(st: State): State = if (not(COMPACT)) st else {
    val keep = range(1, st.log.length() + 1).foldl([], (acc, i) => if (gone(st, i)) acc else acc.append(i))
    { ...st,
      log: keep.foldl([], (acc, i) => acc.append(st.log[i - 1])),
      cursor: st.cursor.keys().mapBy(a => renum(keep, st.cursor.get(a))),
      ag: st.ag.keys().mapBy(a => { ...st.ag.get(a), snap: st.ag.get(a).snap.foldl([], (l, i) => l.append(renum(keep, i))) }) }
  }
  // one message shown to a: its effect on what a knows
  pure def show(st: State, a: str, id: int): State = {
    val m = st.log[id - 1]
    val st1 = { ...st, seen: if (COMPACT) st.seen else st.seen.setBy(a, l => l.append(id)), cursor: st.cursor.setBy(a, c => imax(c, id)) }
    if (m.kind == "answer" and ownerOf(st1, m.task) == a) { ...st1, pend: st1.pend.exclude(Set(m.task)) }
    else if (m.kind == "released") setAg(st1, a, g => { ...g, believes: g.believes.exclude(Set(m.task)) })
    else st1
  }
  pure def showAll(st: State, a: str, ids: List[int]): State = ids.foldl(st, (x, i) => show(x, a, i))
  pure def deliver(st: State, a: str): State = showAll(st, a, unread(st, a))
  // a takes t: it reads the task (task show), so an answer on it reaches a
  pure def takes(st: State, a: str, t: int): State = {
    val st1 = setAg(st, a, g => { ...g, believes: g.believes.union(Set(t)) })
    if (ANSWER_ON_TASK and st1.task.get(t).answer) { ...st1, pend: st1.pend.exclude(Set(t)) } else st1
  }
  // agents._release: every claim and lock of a
  pure def releaseAll(st: State, a: str): State = {
    val st1 = TASKS.fold(st, (x, t) =>
      if (x.task.get(t).owner == a and (x.task.get(t).st == "claimed" or x.task.get(t).st == "blocked"))
        setTask(x, t, k => { ...k, st: "open", owner: "", lease: false, hcq: false })
      else x)
    { ...st1, lock: st1.lock.keys().mapBy(p => if (st1.lock.get(p).holder == a) { holder: "", exp: false } else st1.lock.get(p)) }
  }

  // watchd.reap: a claimed task past its lease. RELEASE says which owners keep it.
  pure def keeps(g: Agent): bool =
    if (RELEASE == "ended") live(g)
    else if (RELEASE == "notWorking") g.st == "working"
    else live(g) and g.st != "idle"
  pure def reapTasks(st: State): State = IDS.foldl(st, (x, t) => {
    val k = x.task.get(t)
    if (k.st == "claimed" and not(k.lease) and not(keeps(agOf(x, k.owner)))) {
      val x1 = setTask(x, t, r => { ...r, st: "open", owner: "", lease: false })
      post(x1, { frm: "swarm", to: k.owner, urgent: false, kind: "released", task: t })
    } else x
  })
  pure def reapLocks(st: State): State =
    { ...st, lock: st.lock.keys().mapBy(p => if (st.lock.get(p).exp) { holder: "", exp: false } else st.lock.get(p)) }
  // watchd.lifecycle: end finished agents, tell reusable ones about new work, else spawn into free slots
  pure def finished(st: State, a: str): bool = {
    val g = st.ag.get(a)
    g.st == "idle" and g.aged and not(holds(st, a)) and not(lockHeld(st, a)) and g.reading == 0 and g.snap.length() == 0
  }
  pure def lifecycle(st: State): State = {
    val pl = pool(st)
    // since #116 one told of the whole pool, its inbox read, has passed it over: ended, not reusable;
    // since #119 one with no live waiter (it would never read a digest) is ended too
    val reusable = NAMES.filter(a => finished(st, a) and not(st.ag.get(a).big) and pl.size() > 0
      and not(PASSED_OVER and pl.subseteq(st.ag.get(a).told) and unread(st, a).length() == 0)
      and (st.ag.get(a).waiter or not(WAITER_ALIVE)))
    val ended = AGENTS.foldl(st, (x, a) =>
      if (finished(st, a) and not(reusable.contains(a))) releaseAll(setAg(x, a, g => { ...g, st: "ended", boot: false, believes: Set() }), a)
      else x)
    val told = AGENTS.foldl(ended, (x, a) =>
      if (reusable.contains(a) and not(pl.subseteq(x.ag.get(a).told)))
        post(setAg(x, a, g => { ...g, told: g.told.union(pl) }), { frm: "swarm", to: a, urgent: false, kind: "digest", task: 0 })
      else x)
    if (reusable.size() > 0) told
    else IDS.foldl(told, (x, t) =>
      if (pl.contains(t) and members(x) < ROSTER and nextAgent(x) != "") {
        val a = nextAgent(x)
        val x1 = setAg(x, a, _g => { ...NOBODY, st: "idle", boot: true })
        val x2 = { ...x1, cursor: x1.cursor.set(a, x1.log.length()), start: x1.start.set(a, if (COMPACT) 0 else x1.log.length()),
          seen: x1.seen.set(a, []) }
        setTask(x2, t, k => { ...k, st: "claimed", owner: a, lease: true })
      } else x)
  }
  pure def tickOf(st: State): State = lifecycle(reapLocks(reapTasks(st)))

  // ---------- actions ----------
  action init = s' = {
    task: TASKS.mapBy(_t => { st: "absent", owner: "", deps: Set(), lease: false, ev: false, answer: false, hcq: false }),
    ag: NAMES.mapBy(a => {
      st: if (AGENTS.indices().exists(i => i < ROSTER and AGENTS[i] == a)) "working" else "unborn",
      waiter: false, big: false, aged: false, cold: false, boot: false, told: Set(), believes: Set(), snap: [], reading: 0 }),
    lock: PATTERNS.mapBy(_p => { holder: "", exp: false }),
    log: [], cursor: NAMES.mapBy(_a => 0), start: NAMES.mapBy(_a => 0), seen: NAMES.mapBy(_a => []),
    pend: Set(), early: false, posts: 0
  }

  // an agent runs a command only with an empty inbox: the PreToolUse hook delivers before every one
  pure def working(st: State, a: str): bool = st.ag.get(a).st == "working" and unread(st, a).length() == 0
  pure def busy(st: State, a: str): bool = st.ag.get(a).st == "working"
  pure def ownsClaimed(st: State, a: str, t: int): bool = st.task.get(t).st == "claimed" and st.task.get(t).owner == a

  // swarm task claim: refuses while a dependency isn't done, then writes `where state='open'`
  action claim(a: str, t: int): bool = all {
    not(RACY), working(s, a), startable(s, t),
    s' = takes(setTask(s, t, k => { ...k, st: "claimed", owner: a, lease: true }), a, t)
  }
  // the same, as two steps: the dependency read, then the write (the write rechecks only state='open')
  action claimRead(a: str, t: int): bool = all {
    RACY, working(s, a), s.ag.get(a).reading == 0, startable(s, t),
    s' = setAg(s, a, g => { ...g, reading: t })
  }
  action claimWrite(a: str): bool = {
    val t = s.ag.get(a).reading
    all {
      RACY, t > 0,
      s' = if (s.task.get(t).st == "open" and (depsDone(s, t) or not(CLAIM_CHECKS_DEPS)))
          { ...takes(setTask(s, t, k => { ...k, st: "claimed", owner: a, lease: true }), a, t),
            early: s.early or not(depsDone(s, t)), ag: s.ag.setBy(a, g => { ...g, reading: 0, believes: g.believes.union(Set(t)) }) }
        else setAg(s, a, g => { ...g, reading: 0 })
    }
  }
  action renew(a: str, t: int): bool = all { working(s, a), ownsClaimed(s, a, t), s' = setTask(s, t, k => { ...k, lease: true }) }
  action release(a: str, t: int): bool = all {
    working(s, a), ownsClaimed(s, a, t),
    s' = setAg(setTask(s, t, k => { ...k, st: "open", owner: "", lease: false }), a, g => { ...g, believes: g.believes.exclude(Set(t)) })
  }
  action block(a: str, t: int): bool = all { on("block"), working(s, a), ownsClaimed(s, a, t), s' = setTask(s, t, k => { ...k, st: "blocked" }) }
  // swarm task done --evidence E: the CLI requires the flag; ev is whether E is non-empty
  action done(a: str, t: int, ev: bool): bool = all {
    working(s, a), ownsClaimed(s, a, t), ev or on("emptyEvidence"),
    s' = setAg(setTask(s, t, k => { ...k, st: "done", lease: false, ev: ev }), a, g => { ...g, believes: g.believes.exclude(Set(t)) })
  }
  // the owner drops its own claimed or blocked task
  action dropOwn(a: str, t: int): bool = all {
    working(s, a), s.task.get(t).owner == a, Set("claimed", "blocked").contains(s.task.get(t).st),
    s' = setAg(setTask(s, t, k => { ...k, st: "dropped", owner: "", lease: false }), a, g => { ...g, believes: g.believes.exclude(Set(t)) })
  }
  // swarm lock: refused while a live peer's lock (unexpired, holder not ended) covers it or it covers that one
  action lock(a: str, p: str): bool = all {
    working(s, a),
    PATTERNS.forall(q => {
      val l = s.lock.get(q)
      l.holder == "" or l.holder == a or l.exp or not(live(agOf(s, l.holder))) or not(refuses(p, q))
    }),
    s' = { ...s, lock: s.lock.set(p, { holder: a, exp: false }) }
  }
  action unlock(a: str, p: str): bool = all {
    working(s, a), s.lock.get(p).holder == a, s' = { ...s, lock: s.lock.set(p, { holder: "", exp: false }) }
  }
  action postTo(a: str, b: str, urgent: bool): bool = all {
    working(s, a), b != a, s.ag.get(b).st != "unborn", s.posts < MAX_POSTS, s.log.length() < MAX_LOG,
    s' = { ...post(s, { frm: a, to: b, urgent: urgent, kind: "dm", task: 0 }), posts: s.posts + 1 }
  }
  // swarm read, or a hook (prompt, post-tool): all unread, marked read
  action readAll(a: str): bool = all { busy(s, a), unread(s, a).length() > 0, s' = deliver(s, a) }
  // the Stop hook: idle, a waiter armed, its context size known. A small-context agent with work in the pool
  // and no claim takes it first (brief: take the next task), so only a big or busy one stops beside the pool.
  action stop(a: str, big: bool): bool = all {
    busy(s, a), s.ag.get(a).reading == 0, on("big") or not(big),
    big or holds(s, a) or pool(s).size() == 0,
    s' = setAg(s, a, g => { ...g, st: "idle", waiter: true, big: big, aged: false, cold: false })
  }

  // environment: time, the waiter, the human, hc
  // the waiter wakes the agent on a message: an urgent one always, others unless the agent is cold
  action wake(a: str): bool = all {
    not(RACY), s.ag.get(a).st == "idle", s.ag.get(a).waiter, wakes(s, a),
    s' = setAg(deliver(s, a), a, g => { ...g, st: "working", waiter: false, aged: false, cold: false })
  }
  action wakeRead(a: str): bool = all {
    RACY, s.ag.get(a).st == "idle", s.ag.get(a).waiter, s.ag.get(a).snap.length() == 0, wakes(s, a),
    s' = setAg(s, a, g => { ...g, snap: unread(s, a) })
  }
  action wakeWrite(a: str): bool = all {
    RACY, s.ag.get(a).snap.length() > 0,
    s' = {
      val snap = s.ag.get(a).snap
      // since #115 the write fails if another delivery moved the cursor past what was read, and reads again
      val x1 = if (DELIVER_CAS and s.cursor.get(a) >= snap[0]) deliver(s, a) else showAll(s, a, snap)
      setAg(x1, a, g => { ...g, snap: [], st: "working", waiter: false, aged: false, cold: false })
    }
  }
  // a turn the waiter didn't start (the human, a SendMessage nudge): the prompt hook delivers
  action prompt(a: str): bool = all {
    on("prompt"), s.ag.get(a).st == "idle", not(s.ag.get(a).boot),
    s' = setAg(deliver(s, a), a, g => { ...g, st: "working", aged: false, cold: false })
  }
  // a spawned agent's first turn: its brief says task show
  action boot(a: str): bool = all {
    s.ag.get(a).boot, s.ag.get(a).st == "idle",
    s' = {
      val t = IDS.foldl(0, (r, x) => if (r == 0 and ownsClaimed(s, a, x)) x else r)
      val x1 = setAg(deliver(s, a), a, g => { ...g, st: "working", boot: false })
      if (t > 0) takes(x1, a, t) else x1
    }
  }
  action waiterGone(a: str): bool = all { on("waiterGone"), s.ag.get(a).waiter, s' = setAg(s, a, g => { ...g, waiter: false }) }
  action age(a: str): bool = all { s.ag.get(a).st == "idle", not(s.ag.get(a).aged), s' = setAg(s, a, g => { ...g, aged: true }) }
  action cool(a: str): bool = all {
    on("cold"), s.ag.get(a).st == "idle", s.ag.get(a).aged, s.ag.get(a).big, not(s.ag.get(a).cold),
    s' = setAg(s, a, g => { ...g, cold: true })
  }
  action expire(t: int): bool = all { s.task.get(t).st == "claimed", s.task.get(t).lease, s' = setTask(s, t, k => { ...k, lease: false }) }
  action expireLock(p: str): bool = all { s.lock.get(p).holder != "", not(s.lock.get(p).exp), s' = { ...s, lock: s.lock.setBy(p, l => { ...l, exp: true }) } }
  // swarm leave, or reap of a dead terminal: ended, its claims and locks released
  action leave(a: str): bool = all {
    on("leave"), live(s.ag.get(a)), s.ag.get(a).reading == 0, s.ag.get(a).snap.length() == 0,
    s' = releaseAll(setAg(s, a, g => { ...g, st: "ended", waiter: false, boot: false, believes: Set() }), a)
  }
  // watchd sees an hc permission prompt: the agent and its first claimed task go blocked
  action hcPrompt(a: str): bool = all {
    on("hc"), busy(s, a), s.ag.get(a).reading == 0,
    s' = {
      val t = IDS.foldl(0, (r, x) => if (r == 0 and ownsClaimed(s, a, x)) x else r)
      val x1 = setAg(s, a, g => { ...g, st: "blocked" })
      if (t > 0) setTask(x1, t, k => { ...k, st: "blocked", hcq: true }) else x1
    }
  }
  // the prompt is answered: its tasks are claimed again with a fresh lease; the next tool's hook delivers
  action hcClear(a: str): bool = all {
    on("hc"), s.ag.get(a).st == "blocked",
    s' = {
      val x1 = TASKS.fold(s, (x, t) =>
        if (x.task.get(t).owner == a and x.task.get(t).st == "blocked" and x.task.get(t).hcq)
          setTask(x, t, k => { ...k, st: "claimed", hcq: false, lease: true })
        else x)
      setAg(deliver(x1, a), a, g => { ...g, st: "working" })
    }
  }

  // the communicator
  action add(deps: Set[int]): bool = {
    val t = nextTask(s)
    all {
      t <= NTASKS, deps.forall(d => d < t), on("deps") or deps == Set(),
      s' = setTask(s, t, k => { ...k, st: "open", deps: deps })
    }
  }
  action after(t: int, deps: Set[int]): bool = all {
    on("deps"), s.task.get(t).st == "open", deps.forall(d => s.task.get(d).st != "absent" and not(reaches(s, d, t))),
    s' = setTask(s, t, k => { ...k, deps: deps })
  }
  action unblock(t: int): bool = {
    val o = s.task.get(t).owner
    all {
      on("block"), s.task.get(t).st == "blocked",
      s' = {
        val x1 = setTask(s, t, k => { ...k, st: "claimed", lease: true, hcq: false, answer: k.answer or ANSWER_ON_TASK })
        { ...post(x1, { frm: COMMS, to: o, urgent: false, kind: "answer", task: t }), pend: x1.pend.union(Set(t)) }
      }
    }
  }
  // swarm task drop by the communicator: any task, in any state (a done one too)
  action drop(t: int): bool = all {
    s.task.get(t).st != "absent", s.task.get(t).st != "dropped",
    s' = setTask(s, t, k => { ...k, st: "dropped", owner: "", lease: false, hcq: false })
  }

  // watchd --once
  action tick: bool = all { tickOf(s) != s, s' = tickOf(s) }

  // agents' commands; the environment (time, waiters, the human, hc); the communicator; watchd. The environment and the
  // communicator are one branch each, so the simulator's even pick among enabled branches favours the agents.
  action agentStep = any {
    nondet a1 = NAMES.oneOf()
    nondet t1 = TASKS.oneOf()
    claim(a1, t1),
    nondet a2 = NAMES.oneOf()
    nondet t2 = TASKS.oneOf()
    claimRead(a2, t2),
    nondet a3 = NAMES.oneOf()
    claimWrite(a3),
    nondet a4 = NAMES.oneOf()
    nondet t4 = TASKS.oneOf()
    renew(a4, t4),
    nondet a5 = NAMES.oneOf()
    nondet t5 = TASKS.oneOf()
    release(a5, t5),
    nondet a6 = NAMES.oneOf()
    nondet t6 = TASKS.oneOf()
    block(a6, t6),
    nondet a7 = NAMES.oneOf()
    nondet t7 = TASKS.oneOf()
    nondet ev7 = Set(true, false).oneOf()
    done(a7, t7, ev7),
    nondet a8 = NAMES.oneOf()
    nondet t8 = TASKS.oneOf()
    dropOwn(a8, t8),
    nondet a9 = NAMES.oneOf()
    nondet p9 = PATTERNS.oneOf()
    lock(a9, p9),
    nondet a10 = NAMES.oneOf()
    nondet p10 = PATTERNS.oneOf()
    unlock(a10, p10),
    nondet a11 = NAMES.oneOf()
    nondet b11 = NAMES.oneOf()
    nondet u11 = Set(true, false).oneOf()
    postTo(a11, b11, u11),
    nondet a12 = NAMES.oneOf()
    readAll(a12),
    nondet a14 = NAMES.oneOf()
    nondet big14 = Set(true, false).oneOf()
    stop(a14, big14),
  }
  action envStep = any {
    nondet a15 = NAMES.oneOf()
    wake(a15),
    nondet a16 = NAMES.oneOf()
    wakeRead(a16),
    nondet a17 = NAMES.oneOf()
    wakeWrite(a17),
    nondet a18 = NAMES.oneOf()
    prompt(a18),
    nondet a19 = NAMES.oneOf()
    boot(a19),
    nondet a20 = NAMES.oneOf()
    waiterGone(a20),
    nondet a21 = NAMES.oneOf()
    age(a21),
    nondet a22 = NAMES.oneOf()
    cool(a22),
    nondet t23 = TASKS.oneOf()
    expire(t23),
    nondet p24 = PATTERNS.oneOf()
    expireLock(p24),
    nondet a25 = NAMES.oneOf()
    leave(a25),
    nondet a26 = NAMES.oneOf()
    hcPrompt(a26),
    nondet a27 = NAMES.oneOf()
    hcClear(a27),
  }
  pure val DEPSETS: Set[Set[int]] = TASKS.powerset()
  action commsStep = any {
    nondet d28 = DEPSETS.oneOf()
    add(d28),
    nondet t29 = TASKS.oneOf()
    nondet d29 = DEPSETS.oneOf()
    after(t29, d29),
    nondet t30 = TASKS.oneOf()
    unblock(t30),
    nondet t31 = TASKS.oneOf()
    drop(t31),
  }
  action step = any { agentStep, envStep, commsStep, tick }

  // ---------- safety ----------
  // S1. No task has two owners at work: no two agents, each working or at an hc prompt, both believe they hold it.
  val oneWorker: bool = TASKS.forall(t =>
    NAMES.filter(a => Set("working", "blocked").contains(s.ag.get(a).st) and s.ag.get(a).believes.contains(t)).size() <= 1)
  // S2. No task starts before the tasks it is after are done.
  val noEarlyStart: bool = not(s.early)
  // S3. No two live locks of different agents cover a common file.
  val locksDisjoint: bool = PATTERNS.forall(p => PATTERNS.forall(q => {
    val l = s.lock.get(p)
    val m = s.lock.get(q)
    not(p != q and l.holder != "" and m.holder != "" and l.holder != m.holder
      and not(l.exp) and not(m.exp) and live(agOf(s, l.holder)) and live(agOf(s, m.holder)) and overlap(p, q))
  }))
  // S4. A message is never shown twice, and a cursor never passes one it didn't show.
  val inboxExact: bool = NAMES.forall(a => {
    val seen = s.seen.get(a)
    val ascending = seen.indices().forall(i => i == 0 or seen[i - 1] < seen[i])
    val noGap = (s.start.get(a) + 1).to(s.cursor.get(a)).forall(i => not(addressed(s, a, i)) or seen.foldl(false, (b, x) => b or x == i))
    ascending and noGap
  })
  // S5. A done task has evidence.
  val doneHasEvidence: bool = TASKS.forall(t => s.task.get(t).st != "done" or s.task.get(t).ev)
  val safety: bool = oneWorker and noEarlyStart and locksDisjoint and inboxExact and doneHasEvidence

  // ---------- liveness, under fairness ----------
  val slotFree: bool = members(s) < ROSTER
  // L1. A startable task doesn't stay startable forever while a slot is free.
  temporal startableClaimed = TASKS.forall(t => always(eventually(not(startable(s, t) and slotFree))))
  // L2. A claimed task whose owner is idle is, eventually, done or open again (or its owner is back at work).
  temporal idleClaimFreed = TASKS.forall(t => NAMES.forall(a =>
    always((ownsClaimed(s, a, t) and s.ag.get(a).st == "idle") implies
      eventually(not(ownsClaimed(s, a, t)) or s.ag.get(a).st != "idle"))))
  // L3. An unblock answer reaches whoever holds the task (unless the task ends).
  temporal answerArrives = TASKS.forall(t =>
    always(s.pend.contains(t) implies eventually(not(s.pend.contains(t)) or Set("done", "dropped").contains(s.task.get(t).st))))

  // Fairness: watchd ticks; time passes (leases lapse, idle ages); a waiter with a wake-worthy message wakes;
  // a spawned agent boots; a working agent drains its hooks, finishes a two-step write, and takes work it is
  // repeatedly able to; an hc prompt is answered.
  temporal fair =
    weakFair(tick, s)
    and TASKS.forall(t => weakFair(expire(t), s))
    and NAMES.forall(a => weakFair(age(a), s) and weakFair(boot(a), s) and weakFair(wake(a), s)
      and weakFair(wakeRead(a), s) and weakFair(wakeWrite(a), s) and weakFair(claimWrite(a), s)
      and weakFair(hcClear(a), s) and weakFair(readAll(a), s)
      and strongFair(TASKS.exists(t => claim(a, t) or claimRead(a, t)), s))
  temporal L1 = fair implies startableClaimed
  temporal L2 = fair implies idleClaimFreed
  temporal L3 = fair implies answerArrives
}




// ---------- instances ----------
// The switches record each fix as a before and an after: RELEASE (#106 and its follow-up), CLAIM_CHECKS_DEPS (#112),
// "emptyEvidence" in OFF (#113), LOCK_OVERLAP (#114), DELIVER_CAS (#115), PASSED_OVER (#116), WAITER_ALIVE (#119).
// before: 624cf79, every switch off. first106: b04cf08's reap rule, the rest off. after: main now, every fix on.
// Those three have every feature on, for `quint run`. The s*_ and l*_ ones are what check.sh hands TLC: two agent
// slots (a spawn fills an ended one), what the property doesn't need turned off, and the switch under test set as
// the name says (racy/globs/before = the bug, fixed = the fix); S1 and liveness are per task, so one task.
module before {  // 624cf79: every fix off; every feature, for the simulator
  import swarm(AGENTS = ["m-1", "m-2", "m-3"], ROSTER = 2, NTASKS = 2, PATTERNS = Set("m/*.lua", "m/a*", "m/"),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "ended", ANSWER_ON_TASK = false, RACY = true, CLAIM_CHECKS_DEPS = false, LOCK_OVERLAP = false, DELIVER_CAS = false, PASSED_OVER = false, WAITER_ALIVE = false,
    OFF = Set(), COMPACT = false, MAX_LOG = 6, MAX_POSTS = 2, COMMS = "m-comms") .*
}
module first106 {  // b04cf08: its reap rule, later fixes off; every feature, for the simulator
  import swarm(AGENTS = ["m-1", "m-2", "m-3"], ROSTER = 2, NTASKS = 2, PATTERNS = Set("m/*.lua", "m/a*", "m/"),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "notWorking", ANSWER_ON_TASK = true, RACY = true, CLAIM_CHECKS_DEPS = false, LOCK_OVERLAP = false, DELIVER_CAS = false, PASSED_OVER = false, WAITER_ALIVE = false,
    OFF = Set(), COMPACT = false, MAX_LOG = 6, MAX_POSTS = 2, COMMS = "m-comms") .*
}
module after {  // main now: every fix on; every feature, for the simulator
  import swarm(AGENTS = ["m-1", "m-2", "m-3"], ROSTER = 2, NTASKS = 2, PATTERNS = Set("m/*.lua", "m/a*", "m/"),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = true, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("emptyEvidence"), COMPACT = false, MAX_LOG = 6, MAX_POSTS = 2, COMMS = "m-comms") .*
}
module s1_before {  // oneWorker
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "ended", ANSWER_ON_TASK = false, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("deps", "big", "cold", "waiterGone", "prompt", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module s1_first106 {  // oneWorker
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "notWorking", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("deps", "big", "cold", "waiterGone", "prompt", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module s1_after {  // oneWorker
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("deps", "big", "cold", "waiterGone", "prompt", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module s2_racy {  // noEarlyStart: claim before #112, a read, then a write that checks only state
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 3, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = true, CLAIM_CHECKS_DEPS = false, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("block", "big", "cold", "waiterGone", "leave", "hc", "prompt", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module s2_fixed {  // noEarlyStart: claim since #112: the write rechecks the deps
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 2, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = true, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("block", "big", "cold", "waiterGone", "leave", "hc", "prompt", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module s2_atomic {  // noEarlyStart: claim as one transaction
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 3, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("block", "big", "cold", "waiterGone", "leave", "hc", "prompt", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module s3_globs {  // locksDisjoint: two globs neither of which covers the other
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set("m/*.lua", "m/a*", "m/"),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = false, DELIVER_CAS = false, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("deps", "block", "big", "cold", "waiterGone", "hc", "prompt", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module s3_fixed {  // locksDisjoint since #114: lock refuses any common file
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set("m/*.lua", "m/a*", "m/"),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = false, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("deps", "block", "big", "cold", "waiterGone", "hc", "prompt", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module s3_plain {  // locksDisjoint: a directory and files, no globs
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set("m/", "m/a.lua", "m/b.lua"),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("deps", "block", "big", "cold", "waiterGone", "hc", "prompt", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module s4_racy {  // inboxExact: the waiter delivers as a read then a write
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = true, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = false, DELIVER_CAS = false, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("deps", "block", "big", "cold", "waiterGone", "leave", "hc", "emptyEvidence"), COMPACT = false, MAX_LOG = 3, MAX_POSTS = 2, COMMS = "m-comms") .*
}
module s4_fixed {  // inboxExact since #115: the waiter reads, then writes only if the cursor hasn't moved
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = true, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = false, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("deps", "block", "big", "cold", "waiterGone", "leave", "hc", "emptyEvidence"), COMPACT = false, MAX_LOG = 3, MAX_POSTS = 2, COMMS = "m-comms") .*
}
module s4_atomic {  // inboxExact: every delivery one step; doneHasEvidence before #113
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = false, DELIVER_CAS = false, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("deps", "block", "big", "cold", "waiterGone", "leave", "hc"), COMPACT = false, MAX_LOG = 3, MAX_POSTS = 2, COMMS = "m-comms") .*
}
module s5_fixed {  // doneHasEvidence since #113: done refuses empty evidence
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("deps", "block", "big", "cold", "waiterGone", "leave", "hc", "emptyEvidence"), COMPACT = false, MAX_LOG = 3, MAX_POSTS = 2, COMMS = "m-comms") .*
}
module l_before {  // liveness: waiters never time out
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "ended", ANSWER_ON_TASK = false, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = false, WAITER_ALIVE = false,
    OFF = Set("deps", "waiterGone", "hc", "prompt", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module l_first106 {  // liveness: waiters never time out
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "notWorking", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = false, WAITER_ALIVE = false,
    OFF = Set("deps", "waiterGone", "hc", "prompt", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module l_after {  // liveness: waiters never time out; edffafc, before #116
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = false, WAITER_ALIVE = false,
    OFF = Set("deps", "waiterGone", "hc", "prompt", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module l_fixed {  // liveness since #116: a reusable agent that passed the pool over is ended
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("deps", "waiterGone", "hc", "prompt", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module l_after_waiter {  // liveness: a waiter may time out; before #116
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = false, WAITER_ALIVE = false,
    OFF = Set("deps", "hc", "prompt", "cold", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module l_fixed_waiter {  // liveness since #116, before #119: a waiter may time out
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = false,
    OFF = Set("deps", "hc", "prompt", "cold", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module l_waiter {  // liveness since #119: a waiter may time out; one without a live waiter is ended
  import swarm(AGENTS = ["m-1", "m-2"], ROSTER = 2, NTASKS = 1, PATTERNS = Set(),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("deps", "hc", "prompt", "cold", "emptyEvidence"), COMPACT = true, MAX_LOG = 0, MAX_POSTS = 0, COMMS = "m-comms") .*
}
module replay {  // what cli_model_spec.lua drives the CLI with: atomic commands, no hc
  import swarm(AGENTS = ["m-1", "m-2", "m-3", "m-4"], ROSTER = 2, NTASKS = 4, PATTERNS = Set("m/*.lua", "m/a*", "m/", "m/a.lua"),
    PATHS = Set("m/a.lua", "m/b.lua", "m/a.txt"), RELEASE = "idle", ANSWER_ON_TASK = true, RACY = false, CLAIM_CHECKS_DEPS = true, LOCK_OVERLAP = true, DELIVER_CAS = true, PASSED_OVER = true, WAITER_ALIVE = true,
    OFF = Set("hc", "leave", "emptyEvidence"), COMPACT = false, MAX_LOG = 1000, MAX_POSTS = 6, COMMS = "m-comms") .*
}
