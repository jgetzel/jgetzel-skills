import Lean.Data.Json
import Claims.Util
import Claims.Host
import Claims.Admit

/-! sw-compute.md: sized claims on a machine's cores and memory. The ledger is a directory of files per machine and user,
kept by one `sh` script (`SCRIPT`) that runs here or through `hc exec`; this file holds the script, how it is run, and
the pure parts: reading and rendering the script's `ls`. -/

namespace Claims
open Lean (Json)

/-- Busy cores from two reads of /proc/stat's first line (Linux): `ncpu * Δnon-idle / Δtotal`; idle is idle + iowait,
total the first eight fields (guest is already in user). -/
def BUSY_AWK : String :=
  "{t=0; for(i=2;i<=8;i++)t+=$i; idle=$5+$6; if(NR==1){t1=t;i1=idle}else{dt=t-t1; printf(\"%.2f\", (dt>0 ? n*(dt-(idle-i1))/dt : 0))}}"

/-- Available KiB from macOS `vm_stat`: free + inactive + speculative + purgeable pages (as `Machine.darwinMem`). -/
def DARWIN_MEM_AWK : String :=
  "/page size of/{for(i=1;i<=NF;i++)if($i~/^[0-9]+$/)ps=$i} " ++
  "/^Pages (free|inactive|speculative|purgeable):/{gsub(/\\./,\"\",$NF); n+=$NF} END{print int(n*ps/1024)}"

/-- The admission decision (sw-compute-backfill.md §2.2-§2.4, §5), `Admit.decide` in awk; run as `LC_ALL=C awk -v … ADMIT_AWK`.
Variables: now ncpu total busy avail capc capm resc resm limc limm off id first since cores mem est (`busy` decimal,
`cores` a number or `all`, `est` a number or `-`, `resc resm` the file's values unclamped, `first` the requester's ticket's
first or `now`, `since` its `@since` or empty). Input: `c <claim line>` per live claim, `q <id> <ticket line>` per live
ticket (the requester's own is skipped). Output, one line: `off` | `never <capc> <capm>` | `ok <cores> <mem_kb>` |
`wait <max(0,fc)> <max(0,fm)> <ahead> <since|->` (`Admit.awkLine`; `try` prints the first four words). Ids compare as strings. -/
def ADMIT_AWK : String :=
"function mx(a, b) { return a > b ? a : b }
function mn(a, b) { return a < b ? a : b }
function before(f1, i1, f2, i2) { return f1 < f2 || (f1 == f2 && (i1 \"\") < (i2 \"\")) }
function endof(i) { return mx(now + 0, cs[i] + ce[i]) }
function held(j) {
  if (hs[j] && ts[j] + " ++ toString Admit.YIELD ++ " <= now + 0) return 1
  return tx[j] ? (!whole || resc + 0 != 0 || resm + 0 != 0) : (tc[j] > limc + 0 || tm[j] > fm + sm)
}
function fits(j, tau,  i, rc, rm) {
  if (tx[j]) { for (i = 1; i <= nc; i++) if (!he[i] || endof(i) > tau) return 0; return 1 }
  for (i = 1; i <= nc; i++) if (he[i] && endof(i) <= tau) { rc += cc_[i]; rm += cm_[i] }
  return tc[j] <= limc - sc + rc && tm[j] <= fm + rm
}
$1 == \"c\" { nc++; cc_[nc] = $2 + 0; cm_[nc] = $3 + 0; cs[nc] = $5 + 0
  if ($6 ~ /^~[0-9]+$/) { he[nc] = 1; ce[nc] = substr($6, 2) + 0 } else he[nc] = 0 }
$1 == \"q\" && ($2 \"\") != (id \"\") { nt++; tid[nt] = $2; tf[nt] = $3 + 0; tx[nt] = ($4 == \"all\"); tc[nt] = $4 + 0; tm[nt] = $5 + 0
  if ($6 ~ /^@[0-9]+$/) { hs[nt] = 1; ts[nt] = substr($6, 2) + 0 } else hs[nt] = 0 }
END {
  if (off + 0) { print \"off\"; exit }
  whole = (capc + 0 >= ncpu + 0 && capm + 0 >= total + 0)
  excl = (cores == \"all\")
  if (excl ? !whole : (cores + 0 > capc + 0 || mem + 0 > capm + 0)) { printf \"never %.0f %.0f\\n\", capc, capm; exit }
  for (i = 1; i <= nc; i++) { sc += cc_[i]; sm += cm_[i] }
  k = int(ncpu / 8); if (k < 1) k = 1
  out = int(busy - sc + 0.5) - k; if (out < 0) out = 0
  fc = mn(limc - sc, ncpu - sc - out); fm = mn(limm - sm, avail)
  quiet = (resc + 0 == 0 && resm + 0 == 0 && out == 0)
  ahead = 0; h = 0
  for (j = 1; j <= nt; j++)
    if (!held(j) && before(tf[j], tid[j], first + 0, id)) {
      ahead++
      if (!h || before(tf[j], tid[j], tf[h], tid[h])) h = j
    }
  bf = 0
  if (h && est != \"-\") {
    best = \"\"
    for (e = 0; e <= nc; e++) {
      if (e > 0 && !he[e]) continue
      tau = e ? endof(e) : now + 0
      if ((best == \"\" || tau < best) && fits(h, tau)) best = tau
    }
    bf = (best != \"\" && now + est <= best)
  }
  if (excl ? (nc == 0 && quiet) : (cores + 0 <= fc && mem + 0 <= fm)) fit = 1; else fit = 0
  if (fit && (ahead == 0 || bf)) { if (excl) printf \"ok %.0f %.0f\\n\", ncpu, avail; else printf \"ok %.0f %.0f\\n\", cores, mem; exit }
  # blocked only by unclaimed use (Admit.blockedOut): the clock of the yield
  bo = (nc == 0 && !fit && (excl ? (resc + 0 == 0 && resm + 0 == 0) : (cores + 0 <= limc + 0 && mem + 0 <= fm)))
  printf \"wait %.0f %.0f %d %s\\n\", mx(0, fc), mx(0, fm), ahead, (bo ? (since != \"\" ? sprintf(\"%.0f\", since) : sprintf(\"%.0f\", now)) : \"-\")
}"

/-- The command `cmd` as `sh -c` runs it, at the lowest CPU priority and, where `ionice` works, idle I/O (§4). The exit code is
the command's. -/
def lowPrioWith (tail : String) : String :=
  s!"if ionice -c3 true 2>/dev/null; then exec ionice -c3 nice -n 19 {tail}; else exec nice -n 19 {tail}; fi"

/-- `sh -c (lowPrio cmd)` runs the shell command `cmd` at the lowest priority. -/
def lowPrio (cmd : String) : String := lowPrioWith ("sh -c " ++ shquote cmd)

/-- `sh -c (memCap unit memKb cmd)` runs the shell command `cmd` in its own systemd user scope `unit` with
`MemoryMax=memKb` KiB and no swap, where the machine has one; elsewhere it warns on stderr and runs `cmd` uncapped. -/
def memCap (unit : String) (memKb : Int) (cmd : String) : String :=
  s!"if systemd-run --user --scope --quiet true 2>/dev/null; then exec systemd-run --user --scope --quiet --collect --unit={unit} -p MemoryMax={memKb}K -p MemorySwapMax=0 -- sh -c {shquote cmd}; " ++
  s!"else echo 'swarm: memory not capped here (no systemd user scope); --mem is a reservation only' >&2; exec sh -c {shquote cmd}; fi"

/-- The same for an argv: `sh -c LOWPRIO_ARGV sh cmd args…`. -/
def LOWPRIO_ARGV : String := lowPrioWith "\"$@\""

/-- The script's first half: the ledger's place, the machine's reading (`sample`), the lock and the cleaning. -/
def SCRIPT_A : String := "
d=\"${SWARM_COMPUTE_DIR:-${XDG_STATE_HOME:-$HOME/.local/state}/swarm-compute}\"
op=$1; shift
trap 'exit 1' INT TERM HUP
mkdir -p \"$d/claims\" \"$d/queue\" \"$d/notes\" || exit 1
num() { case $1 in ''|*[!0-9]*) return 1;; esac; }
okid() { case $1 in ''|*[!A-Za-z0-9._-]*) echo 'bad id' >&2; exit 2;; esac; }
sample() {
  if [ \"$(uname)\" = Darwin ]; then
    ncpu=$(sysctl -n hw.ncpu); total_kb=$(( $(sysctl -n hw.memsize) / 1024 ))
    busy=$(ps -A -o %cpu | awk 'NR>1{s+=$1} END{printf(\"%.2f\", s/100)}')
    avail_kb=$(vm_stat | awk '" ++ DARWIN_MEM_AWK ++ "')
  else
    st=${SWARM_COMPUTE_STAT:-/proc/stat}
    ncpu=$(grep -c '^cpu[0-9]' \"$st\")
    if [ -n \"$SWARM_COMPUTE_BUSY\" ]; then busy=$SWARM_COMPUTE_BUSY; else
      a=$(head -n 1 \"$st\"); sleep 0.5; b=$(head -n 1 \"$st\")
      busy=$(printf '%s\\n%s\\n' \"$a\" \"$b\" | awk -v n=\"$ncpu\" '" ++ BUSY_AWK ++ "')
    fi
    mm=$(awk '/^MemTotal:/{t=$2} /^MemAvailable:/{a=$2} END{print t+0, a+0}' \"${SWARM_COMPUTE_MEM:-/proc/meminfo}\")
    total_kb=${mm% *}; avail_kb=${mm#* }
  fi
  # a reading a failed fork left empty is no idle machine
  num \"$ncpu\" && num \"$total_kb\" && num \"$avail_kb\" || exit 1
  case $busy in ''|*[!0-9.-]*) exit 1;; esac
}
# a lock over a minute old with no live pid: a younger one may have been taken just after the pid read
stale() {
  p=$(cat \"$d/$1/pid\" 2>/dev/null)
  [ -n \"$(find \"$d/$1\" -prune -mmin +1 2>/dev/null)\" ] && { [ -z \"$p\" ] || ! kill -0 \"$p\" 2>/dev/null; }
}
# a stale lock is broken only by the one holding $d/break, which re-checks the lock first: a waiter that judged it stale
# earlier cannot delete a lock taken since. A stale break (its breaker died) is removed on the same test; that removal is
# unguarded, so the one case left is a breaker and a holder both crashing and two waiters then clearing the break at once:
# one can delete the other's fresh break, and two breakers may run together (a minute-old window, never seen to matter)
lock() {
  until mkdir \"$d/lock\" 2>/dev/null; do
    if stale lock; then
      if mkdir \"$d/break\" 2>/dev/null; then
        trap 'rm -rf \"$d/break\"' EXIT
        echo $$ > \"$d/break/pid\"
        if stale lock; then rm -rf \"$d/lock\"; fi
        rm -rf \"$d/break\"; trap - EXIT
      elif stale break; then rm -rf \"$d/break\"; fi
    fi
    sleep 0.1
  done
  echo $$ > \"$d/lock/pid\"
  trap 'rm -rf \"$d/lock\"' EXIT
  now=${SWARM_COMPUTE_NOW:-$(date +%s)}
  num \"$now\" || exit 1
}
clean() {
  for f in \"$d\"/claims/*; do
    [ -f \"$f\" ] || continue
    read -r c m h rest < \"$f\"
    case $h in
      p*) kill -0 \"${h#p}\" 2>/dev/null || rm -f \"$f\";;
      t*) [ \"${h#t}\" -gt \"$now\" ] 2>/dev/null || rm -f \"$f\";;
      *) rm -f \"$f\";;
    esac
  done
  find \"$d/queue\" -type f -mmin +1 -exec rm -f {} +
  for f in \"$d\"/notes/*; do
    [ -f \"$f\" ] || continue
    read -r h _ < \"$f\"
    case $h in
      p*) kill -0 \"${h#p}\" 2>/dev/null || rm -f \"$f\";;
      t*) [ \"${h#t}\" -gt \"$now\" ] 2>/dev/null || rm -f \"$f\";;
      *) rm -f \"$f\";;
    esac
  done
}
caps() {
  capc=$ncpu; capm=$total_kb
  if [ -f \"$d/cap\" ]; then
    read -r cc cm < \"$d/cap\"
    if num \"$cc\"; then capc=$cc; fi
    if num \"$cm\"; then capm=$cm; fi
  fi
  resc=0; resm=0
  if [ -f \"$d/reserve\" ]; then
    read -r rcv rmv < \"$d/reserve\"
    if num \"$rcv\"; then resc=$rcv; fi
    if num \"$rmv\"; then resm=$rmv; fi
  fi
  # the room sized jobs may take: the cap, less the reservation clamped to the machine (Admit.lim)
  limc=$((ncpu - (resc < ncpu ? resc : ncpu))); if [ \"$limc\" -gt \"$capc\" ]; then limc=$capc; fi
  limm=$((total_kb - (resm < total_kb ? resm : total_kb))); if [ \"$limm\" -gt \"$capm\" ]; then limm=$capm; fi
}
"

/-- The script's second half: the ops. -/
def SCRIPT_B : String := "
try_() {
  id=$1; cores=$2; mem=$3; est=$4; holder=$5; who=$6; cmd=$7
  okid \"$id\"
  cmd=$(printf %s \"$cmd\" | tr '\\n\\t' '  ' | cut -c1-200)
  who=$(printf %s \"$who\" | tr -c 'A-Za-z0-9._:-' '_')
  if [ \"$cores\" = all ]; then mem=0; elif ! num \"$cores\" || [ \"$cores\" -lt 1 ]; then echo 'bad size' >&2; exit 2; fi
  if ! num \"$mem\" || { [ \"$est\" != - ] && ! num \"$est\"; }; then echo 'bad size' >&2; exit 2; fi
  sample; lock; clean; caps
  if [ \"$holder\" = t ]; then holder=t$((now + 900)); fi
  first=$now; osince=
  if [ -f \"$d/queue/$id\" ]; then
    read -r first _ _ s4 _ < \"$d/queue/$id\"
    case $s4 in @*) if num \"${s4#@}\"; then osince=${s4#@}; fi;; esac
  fi
  offv=0; if [ -e \"$d/off\" ]; then offv=1; fi
  # the ledger read by builtins alone: a `cat` whose fork failed (a loaded machine) gave awk part of it, and a grant past the cap
  in=; nl='\n'
  for f in \"$d\"/claims/*; do if [ -f \"$f\" ] && read -r l < \"$f\"; then in=\"${in}c $l$nl\"; fi; done
  for f in \"$d\"/queue/*; do if [ -f \"$f\" ] && read -r l < \"$f\"; then in=\"${in}q ${f##*/} $l$nl\"; fi; done
  dec=$(printf %s \"$in\" |
    LC_ALL=C awk -v now=\"$now\" -v ncpu=\"$ncpu\" -v total=\"$total_kb\" -v busy=\"$busy\" -v avail=\"$avail_kb\" -v capc=\"$capc\" -v capm=\"$capm\" \\
      -v resc=\"$resc\" -v resm=\"$resm\" -v limc=\"$limc\" -v limm=\"$limm\" -v off=\"$offv\" -v id=\"$id\" -v first=\"$first\" -v since=\"$osince\" \\
      -v cores=\"$cores\" -v mem=\"$mem\" -v est=\"$est\" '" ++ ADMIT_AWK ++ "')
  case $dec in
    ok*)
      set -- $dec
      if [ \"$est\" = - ]; then e=; else e=\"~$est \"; fi
      printf '%s %s %s %s %s%s %s\\n' \"$2\" \"$3\" \"$holder\" \"$now\" \"$e\" \"$who\" \"$cmd\" > \"$d/claims/.$id\" && mv \"$d/claims/.$id\" \"$d/claims/$id\" || exit 1
      rm -f \"$d/queue/$id\";;
    wait*)
      set -- $dec
      dec=\"$1 $2 $3 $4\"
      if [ \"$5\" = - ]; then s=; else s=\"@$5 \"; fi
      if [ \"$cores\" = all ]; then echo \"$first all 0 $s$who\" > \"$d/queue/$id\"; else echo \"$first $cores $mem $s$who\" > \"$d/queue/$id\"; fi;;
    '') exit 1;;
    *) rm -f \"$d/queue/$id\";;
  esac
  echo \"$dec\"
}
case $op in
  try) try_ \"$@\";;
  drop) okid \"$1\"; rm -f \"$d/claims/$1\" \"$d/queue/$1\";;
  # the claim's holder becomes pid $2, or with `t` a timed holder's 15 minutes start again (a pid's claim is kept as it is);
  # a claim gone (lapsed, its holder dead, or dropped) fails with exit 3
  hold)
    okid \"$1\"
    if [ \"$2\" != t ] && ! num \"$2\"; then echo 'bad pid' >&2; exit 2; fi
    lock; clean
    f=\"$d/claims/$1\"
    if [ ! -f \"$f\" ] || ! read -r c m h rest < \"$f\"; then echo \"no claim $1\" >&2; exit 3; fi
    if [ \"$2\" = t ]; then
      case $h in t*) nh=t$((now + 900));; *) exit 0;; esac
    else nh=p$2; fi
    printf '%s %s %s %s\\n' \"$c\" \"$m\" \"$nh\" \"$rest\" > \"$d/claims/.$1\" && mv \"$d/claims/.$1\" \"$f\";;
  # a display-only note: holds no cores and no place in line; `qadd id owner who est ttl pid cmd` (est, pid: - for none)
  qadd)
    id=$1; owner=$2; who=$3; est=$4; ttl=$5; pid=$6; cmd=$7
    okid \"$id\"
    if ! num \"$ttl\" || [ \"$ttl\" -lt 1 ] || { [ \"$est\" != - ] && ! num \"$est\"; } || { [ \"$pid\" != - ] && ! num \"$pid\"; }; then echo 'bad size' >&2; exit 2; fi
    cmd=$(printf %s \"$cmd\" | tr '\\n\\t' '  ' | cut -c1-200)
    who=$(printf %s \"$who\" | tr -c 'A-Za-z0-9._:-' '_')
    if [ \"$owner\" = - ]; then owner=${USER:-${LOGNAME:-human}}; fi
    owner=$(printf %s \"$owner\" | tr -c 'A-Za-z0-9._:-' '_')
    lock; clean
    if [ \"$pid\" != - ]; then holder=p$pid; else holder=t$((now + ttl)); fi
    since=$now
    if [ -f \"$d/notes/$id\" ]; then read -r _ _ since _ < \"$d/notes/$id\"; fi
    printf '%s %s %s %s %s %s\\n' \"$holder\" \"$est\" \"$since\" \"$who\" \"$owner\" \"$cmd\" > \"$d/notes/.$id\" && mv \"$d/notes/.$id\" \"$d/notes/$id\";;
  qrm) okid \"$1\"; rm -f \"$d/notes/$1\";;
  ls)
    sample; lock; clean; caps
    offv=0; if [ -e \"$d/off\" ]; then offv=1; fi
    rcv=$resc; if [ \"$rcv\" -gt \"$ncpu\" ]; then rcv=$ncpu; fi
    rmv=$resm; if [ \"$rmv\" -gt \"$total_kb\" ]; then rmv=$total_kb; fi
    echo \"$ncpu $busy $total_kb $avail_kb $capc $capm $offv $rcv $rmv\"
    for f in \"$d\"/claims/*; do if [ -f \"$f\" ]; then printf 'c '; cat \"$f\"; fi; done
    for f in \"$d\"/queue/*; do if [ -f \"$f\" ]; then printf 'q %s ' \"${f##*/}\"; cat \"$f\"; fi; done
    for f in \"$d\"/notes/*; do if [ -f \"$f\" ]; then printf 'n '; cat \"$f\"; fi; done;;
  cap)
    # `=` keeps that field as it is
    old='- -'; if [ -f \"$d/cap\" ]; then old=$(cat \"$d/cap\"); fi
    oc=${old% *}; om=${old#* }
    nc=$1; nm=$2
    if [ \"$nc\" = = ]; then nc=$oc; fi
    if [ \"$nm\" = = ]; then nm=$om; fi
    for v in \"$nc\" \"$nm\"; do if [ \"$v\" != - ] && ! num \"$v\"; then echo 'bad cap' >&2; exit 2; fi; done
    echo \"$nc $nm\" > \"$d/cap.tmp.$$\" && mv \"$d/cap.tmp.$$\" \"$d/cap\";;
  reserve)
    for v in \"$1\" \"$2\"; do if ! num \"$v\"; then echo 'bad reserve' >&2; exit 2; fi; done
    if [ \"$1\" -eq 0 ] && [ \"$2\" -eq 0 ]; then rm -f \"$d/reserve\"
    else echo \"$1 $2\" > \"$d/reserve.tmp.$$\" && mv \"$d/reserve.tmp.$$\" \"$d/reserve\"; fi;;
  off) : > \"$d/off\";;
  on) rm -f \"$d/off\";;
  *) echo \"unknown op: $op\" >&2; exit 2;;
esac
"

/-- The script: `sh -c SCRIPT sh <op> <args…>`; ops `try`, `drop`, `hold`, `ls`, `cap`, `off`, `on` (sw-compute.md §2). -/
def SCRIPT : String := SCRIPT_A ++ SCRIPT_B

/-- What `try` answered. -/
inductive Try
  /-- granted: the cores and memory the claim holds (an exclusive claim's are the script's) -/
  | ok (cores mem_kb : Int)
  | wait (cores mem_kb : Int) (ahead : Int)
  | never (cap_cores cap_mem_kb : Int)
  | off
  /-- the machine did not answer, or not in words -/
  | gone
  deriving BEq, Repr

/-- The script's `try` line. -/
def parseTry (s : String) : Try :=
  match words s with
  | ["ok", c, g] => match parseInt c, parseInt g with
    | some c, some g => .ok c g
    | _, _ => .gone
  | ["wait", a, b, c] => match parseInt a, parseInt b, parseInt c with
    | some a, some b, some c => .wait a b c
    | _, _, _ => .gone
  | ["never", a, b] => match parseInt a, parseInt b with
    | some a, some b => .never a b
    | _, _ => .gone
  | ["off"] => .off
  | _ => .gone

/-- The argv that runs the script's op on a machine (none: here). -/
def opArgv (mach : Option String) (args : List String) : List String :=
  match mach with
  | none => ["sh", "-c", SCRIPT, "sh"] ++ args
  | some n => ["hc", "exec", "--on", n, "--timeout", "20", "sh", "-c", SCRIPT, "sh"] ++ args

/-- Runs the script's op on a machine (none: here): its exit code and stdout, none when it did not start. -/
def callRaw {m : Type → Type} [Monad m] (h : Host m) (mach : Option String) (args : List String) : m (Option (Int × String)) :=
  h.run (opArgv mach args)

/-- Runs the script's op on a machine (none: here) and returns its stdout; none when it failed or did not answer. -/
def call {m : Type → Type} [Monad m] (h : Host m) (mach : Option String) (args : List String) : m (Option String) := do
  return (← callRaw h mach args).bind fun (c, o) => if c == 0 then some o else none

/-- Removes a claim and ticket (their absence is no error). -/
def release {m : Type → Type} [Monad m] (h : Host m) (mach : Option String) (id : String) : m Unit :=
  discard <| call h mach ["drop", id]

/-- Makes pid `pid` (on that machine) the holder of claim `id`: false when the claim is gone (it lapsed, its holder died,
or it was dropped). -/
def hold {m : Type → Type} [Monad m] (h : Host m) (mach : Option String) (id : String) (pid : Int) : m Bool := do
  return (← call h mach ["hold", id, toString pid]).isSome

/-- Starts a timed claim's 15 minutes again (a claim held by a pid is kept as it is): false when the claim is gone (exit
3), not when the machine did not answer. -/
def renew {m : Type → Type} [Monad m] (h : Host m) (mach : Option String) (id : String) : m Bool := do
  return (← callRaw h mach ["hold", id, "t"]).all (·.1 != 3)

/-- A claim row of `ls`. -/
structure Claim where
  cores : Int
  mem_kb : Int
  holder : String
  start : Int
  /-- the estimate (s) the request carried, none for a claim without one -/
  est : Option Int := none
  who : String
  cmd : String
  deriving BEq, Repr

/-- A queued note row of `ls`: display only, it holds no cores and no place in line. `est` is seconds. -/
structure Note where
  since : Int
  est : Option Int
  who : String
  owner : String
  cmd : String
  deriving BEq, Repr

/-- A ticket row of `ls`; `cores` none: an exclusive (`all`) request. `id` is its file's name; `since` when it was first
found blocked only by unclaimed use (`Admit.Ticket.since`). -/
structure Ticket where
  id : String := ""
  first : Int
  cores : Option Int
  mem_kb : Int
  since : Option Int := none
  who : String
  deriving BEq, Repr

/-- One machine's `ls`. -/
structure Ls where
  ncpu : Int
  busy : Float
  total_kb : Int
  avail_kb : Int
  cap_cores : Int
  cap_mem_kb : Int
  off : Bool
  /-- the reservation, clamped to the machine -/
  res_cores : Int := 0
  res_mem_kb : Int := 0
  claims : List Claim := []
  queue : List Ticket := []
  notes : List Note := []

/-- The script's `ls` output. -/
def parseLs (s : String) : Option Ls := do
  let ls := splitlines s
  let [a, b, c, d, e, f, g, h, i] := words (← ls.head?) | none
  let mut r : Ls := { ncpu := ← parseInt a, busy := ← parseFloat b, total_kb := ← parseInt c, avail_kb := ← parseInt d,
                      cap_cores := ← parseInt e, cap_mem_kb := ← parseInt f, off := (← parseInt g) != 0,
                      res_cores := ← parseInt h, res_mem_kb := ← parseInt i }
  for l in ls.tail do
    match words l with
    | "c" :: x :: y :: h :: z :: rest =>
      let (est, rest) ← match rest with
        | e :: tl => if e.startsWith "~" then pure (some (← parseInt (e.drop 1).toString), tl) else pure (none, rest)
        | [] => none
      let w :: cmd := rest | none
      r := { r with claims := r.claims ++ [{ cores := ← parseInt x, mem_kb := ← parseInt y, holder := h, start := ← parseInt z, est,
                                              who := w, cmd := " ".intercalate cmd }] }
    | "q" :: i :: x :: y :: z :: rest =>
      let cores ← if y == "all" then pure none else (parseInt y).map some
      let (since, rest) ← match rest with
        | e :: tl => if e.startsWith "@" then pure (some (← parseInt (e.drop 1).toString), tl) else pure (none, rest)
        | [] => pure (none, [])
      let [w] := rest | none
      r := { r with queue := r.queue ++ [{ id := i, first := ← parseInt x, cores, mem_kb := ← parseInt z, since, who := w }] }
    | "n" :: _ :: e :: s :: w :: o :: cmd =>
      let est ← if e == "-" then pure none else (parseInt e).map some
      r := { r with notes := r.notes ++ [{ since := ← parseInt s, est, who := w, owner := o, cmd := " ".intercalate cmd }] }
    | _ => pure ()
  return r

/-- The model's machine for an `ls` (tickets named by their place) at `now`. -/
def Ls.model (l : Ls) (now : Int) : Admit.Machine where
  ncpu := l.ncpu
  total := l.total_kb
  busy := (l.busy * 100).round.toInt64.toInt
  avail := l.avail_kb
  cap := (some l.cap_cores, some l.cap_mem_kb)
  res := (l.res_cores, l.res_mem_kb)
  off := l.off
  now
  claims := l.claims.map fun c => ⟨c.cores, c.mem_kb, c.start, c.est⟩
  tickets := l.queue.map fun q => ⟨q.id, q.first, q.cores, q.mem_kb, q.since⟩

def Ticket.model (q : Ticket) : Admit.Ticket := ⟨q.id, q.first, q.cores, q.mem_kb, q.since⟩

/-- KiB as GiB, one decimal, no unit. -/
def gi (kb : Int) : String := fixed (Float.ofInt kb / 1048576) 1

/-- A span of seconds as `45s`, `4m` or `2h`. -/
def span (s : Int) : String := let s := max 0 s; if s < 60 then s!"{s}s" else if s < 3600 then s!"{s / 60}m" else s!"{s / 3600}h"

/-- A span of seconds as `45s`, `4m` or `2h10m`. -/
def spanHM (s : Int) : String :=
  let s := max 0 s
  if s < 3600 then span s else s!"{s / 3600}h{if s % 3600 / 60 = 0 then "" else s!"{s % 3600 / 60}m"}"

/-- The busy cores no claim explains, one decimal (`outside` before the noise floor). -/
def Ls.unclaimed (l : Ls) : String :=
  let cc : Int := (l.claims.map (·.cores)).sum
  fixed (if l.busy > Float.ofInt cc then l.busy - Float.ofInt cc else 0) 1

/-- Why a waiting ticket is held (the model's `held`), in words: none when it is not held. -/
def Ls.whyHeld (l : Ls) (now : Int) (q : Ticket) : List String :=
  let m := l.model now
  if !Admit.held m q.model then [] else
  if Admit.yielded m q.model then [s!"held: {l.unclaimed} cores unclaimed use"] else
  match q.cores with
  | some c =>
    if c > Admit.limC m || q.mem_kb > Admit.limM m then ["held by the reservation"] else ["held by unclaimed memory use"]
  | none =>
    let rs := (if m.res != (0, 0) then ["reserved"] else []) ++ (if Admit.whole m then [] else ["cap below the machine"])
    ["held: " ++ ", ".intercalate rs]

/-- A claim, for a wait line: `who (4 cores, no estimate, 2h10m)` or `who (4 cores, ~12m left)`. -/
def Claim.brief (c : Claim) (now : Int) : String :=
  s!"{c.who} ({c.cores} cores, " ++ match c.est with
    | none => s!"no estimate, {spanHM (now - c.start)})"
    | some e => s!"~{spanHM (c.start + e - now)} left)"

/-- A ticket's size in words. -/
def Ticket.what (q : Ticket) : String := q.cores.elim "whole machine" fun c => s!"{c} cores {gi q.mem_kb}G"

/-- What a waiting ticket that is not held waits on, in words, as if it were the head: the claims it waits for (by
name, those without an estimate as such, since nothing passes a head that waits on one), unclaimed use (with the
yield's time left once it runs), or memory. -/
def Ls.waitsOn (l : Ls) (now : Int) (q : Ticket) : String :=
  let m := l.model now
  let t := q.model
  let r : Admit.Req := ⟨q.id, q.cores, q.mem_kb, none⟩
  let noEst := l.claims.filter (·.est.isNone)
  let yieldIn := match q.since with
    | some s => s!", yields in {spanHM (s + Admit.YIELD - now)}"
    | none => if Admit.blockedOut m r then s!", yields in {spanHM Admit.YIELD}" else ""
  let unclaimed := s!"{l.unclaimed} cores unclaimed use{yieldIn}"
  let byClaims : Option String :=
    if l.claims.isEmpty then none else
    match q.cores with
    | some c => if c ≤ Admit.limC m - Admit.cc m then none else some ""
    | none => some ""
  let claimsPart : Option String := byClaims.map fun _ =>
    match Admit.shadow m t with
    | none => ", ".intercalate (noEst.map (·.brief now))
    | some τ =>
      let ending := l.claims.filter fun c => (c.est.map (fun e => max now (c.start + e))).any (· ≤ τ)
      ", ".intercalate (ending.map (·.brief now))
  let coresOut := match q.cores with
    | some c => c > Admit.freeC m && c ≤ Admit.limC m - Admit.cc m
    | none => l.claims.isEmpty && Admit.outside m > 0
  let memPart : Option String := match q.cores with
    | some _ => if q.mem_kb > Admit.freeM m then some s!"memory ({gi (max 0 (Admit.freeM m))}G free)" else none
    | none => none
  let parts := claimsPart.toList ++ (if coresOut then [unclaimed] else []) ++ memPart.toList
  if parts.isEmpty then (if Admit.fitsNow m r then "waits its turn" else "waits for room") else "waits on " ++ "; ".intercalate parts

/-- The wait line of the request whose ticket is `id`: what it, or the head before it, waits on; none when the ledger has
no such ticket. -/
def Ls.waitLine (l : Ls) (now : Int) (id : String) : Option String := do
  let q ← l.queue.find? (·.id == id)
  let m := l.model now
  let r : Admit.Req := ⟨q.id, q.cores, q.mem_kb, none⟩
  let held := l.whyHeld now q
  if !held.isEmpty then return s!"{q.what} {", ".intercalate held}; younger jobs go first"
  match Admit.head m r with
  | none => return s!"{q.what} {l.waitsOn now q}"
  | some h =>
    let n := (Admit.aheadOf m r).length
    let hq := (l.queue.find? (·.id == h.id)).getD q
    return s!"{q.what}, {n} ahead: {hq.who} ({hq.what}, {spanHM (now - hq.first)}) {l.waitsOn now hq}"

/-- A wait line with its numbers taken out: what `acquire` compares to say it again only when the reason changes. -/
def waitKey (s : String) : String := String.ofList (s.toList.filter fun c => !c.isDigit && c != '.')

/-- `swarm compute`'s lines for a machine (sw-compute.md §4, sw-compute-backfill.md §3.1). -/
def render (name : String) (l : Ls) (now : Int) : List String :=
  let cc := (l.claims.map (·.cores)).sum
  let cm := (l.claims.map (·.mem_kb)).sum
  let m := l.model now
  let resC := if l.res_cores > 0 then s!"{l.res_cores} reserved, " else ""
  let resM := if l.res_mem_kb > 0 then s!"{gi l.res_mem_kb}G reserved, " else ""
  if l.off && l.claims.isEmpty && l.queue.isEmpty && l.notes.isEmpty then [s!"{name}: off"] else
  [s!"{name}: {if l.off then "off, " else ""}{cc} of {Admit.limC m} cores claimed (cap {l.cap_cores} of {l.ncpu}, {resC}{fixed l.busy 1} busy), " ++
    s!"{gi cm} of {gi (Admit.limM m)}G claimed ({resM}{gi l.avail_kb}G available)"] ++
  l.claims.map (fun c => s!"  {c.who}   {c.cores} cores  {gi c.mem_kb}G  {span (now - c.start)}{c.est.elim "" fun e => s!" of ~{span e}"}  {c.cmd}") ++
  (l.queue.map fun q =>
    s!"  waiting: {q.who} {q.what} {span (now - q.first)}" ++
      (match l.whyHeld now q with | [] => "" | w => ", " ++ ", ".intercalate w)) ++
  l.notes.map fun n =>
    s!"  queued: {n.who} {n.cmd} (owner {n.owner}){n.est.elim "" fun e => s!" ~{span e}"}, since {span (now - n.since)}"

/-- An integer as JSON. -/
def jint (i : Int) : Json := .num (Lean.JsonNumber.fromInt i)

/-- A float as JSON: an integral one as the integer, as cjson's `%.16g` prints it. -/
def jfloat (f : Float) : Json :=
  if f == f.floor && f.abs < 1e15 then jint f.toInt64.toInt else Lean.toJson f

/-- A machine's `ls` as JSON (sw-compute-backfill.md §3.2); `now` is for `held`. -/
def Ls.json (l : Ls) (now : Int) : Json :=
  let m := l.model now
  Json.mkObj [("ncpu", jint l.ncpu), ("busy", jfloat l.busy), ("total_kb", jint l.total_kb), ("avail_kb", jint l.avail_kb),
    ("cap_cores", jint l.cap_cores), ("cap_mem_kb", jint l.cap_mem_kb), ("off", .bool l.off),
    ("reserve_cores", jint l.res_cores), ("reserve_mem_kb", jint l.res_mem_kb),
    ("limit_cores", jint (Admit.limC m)), ("limit_mem_kb", jint (Admit.limM m)),
    ("claims", .arr (l.claims.toArray.map fun c => Json.mkObj [("cores", jint c.cores), ("mem_kb", jint c.mem_kb),
      ("holder", .str c.holder), ("start", jint c.start), ("est_s", c.est.elim .null jint), ("who", .str c.who), ("cmd", .str c.cmd)])),
    ("queue", .arr (l.queue.toArray.map fun q => Json.mkObj [("id", .str q.id), ("first", jint q.first), ("cores", jint (q.cores.getD l.ncpu)),
      ("mem_kb", jint q.mem_kb), ("who", .str q.who), ("exclusive", .bool q.cores.isNone),
      ("held", .bool !(l.whyHeld now q).isEmpty), ("since", q.since.elim .null jint)])),
    ("queued", .arr (l.notes.toArray.map fun n => Json.mkObj [("since", jint n.since), ("est_s", n.est.elim .null jint),
      ("who", .str n.who), ("owner", .str n.owner), ("cmd", .str n.cmd)]))]

end Claims
