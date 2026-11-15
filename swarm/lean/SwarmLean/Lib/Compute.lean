import SwarmLean.Sys
import SwarmLean.Lib.Json
import SwarmLean.Lib.Cost

/-! sw-compute.md: sized claims on a machine's cores and memory. The ledger is a directory of files per machine and user,
kept by one `sh` script (`SCRIPT`) that runs here or through `hc exec`; this file holds the script, how it is run, and
the pure parts: sizing a job from the cmd-cost history, reading and rendering the script's `ls`. -/

namespace SwarmLean.Compute
open Lean (Json)

/-- With no history, what a job claims. -/
def DEFAULT_CORES : Int := 2
/-- ... and its memory (KiB): 2 GiB. -/
def DEFAULT_MEM_KB : Int := 2097152

/-- Busy cores from two reads of /proc/stat's first line (Linux): `ncpu * Δnon-idle / Δtotal`; idle is idle + iowait,
total the first eight fields (guest is already in user). -/
def BUSY_AWK : String :=
  "{t=0; for(i=2;i<=8;i++)t+=$i; idle=$5+$6; if(NR==1){t1=t;i1=idle}else{dt=t-t1; printf(\"%.2f\", (dt>0 ? n*(dt-(idle-i1))/dt : 0))}}"

/-- Available KiB from macOS `vm_stat`: free + inactive + speculative + purgeable pages (as `Machine.darwinMem`). -/
def DARWIN_MEM_AWK : String :=
  "/page size of/{for(i=1;i<=NF;i++)if($i~/^[0-9]+$/)ps=$i} " ++
  "/^Pages (free|inactive|speculative|purgeable):/{gsub(/\\./,\"\",$NF); n+=$NF} END{print int(n*ps/1024)}"

/-- The script's first half: the ledger's place, the machine's reading (`sample`), the lock and the cleaning. -/
def SCRIPT_A : String := "
d=\"${SWARM_COMPUTE_DIR:-${XDG_STATE_HOME:-$HOME/.local/state}/swarm-compute}\"
op=$1; shift
trap 'exit 1' INT TERM HUP
mkdir -p \"$d/claims\" \"$d/queue\" || exit 1
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
    a=$(head -n 1 \"$st\"); sleep 0.5; b=$(head -n 1 \"$st\")
    busy=$(printf '%s\\n%s\\n' \"$a\" \"$b\" | awk -v n=\"$ncpu\" '" ++ BUSY_AWK ++ "')
    mm=$(awk '/^MemTotal:/{t=$2} /^MemAvailable:/{a=$2} END{print t+0, a+0}' \"${SWARM_COMPUTE_MEM:-/proc/meminfo}\")
    total_kb=${mm% *}; avail_kb=${mm#* }
  fi
}
# only a lock over a minute old with no live pid is broken: a younger one may have been taken just after the pid read
lock() {
  until mkdir \"$d/lock\" 2>/dev/null; do
    p=$(cat \"$d/lock/pid\" 2>/dev/null)
    if [ -n \"$(find \"$d/lock\" -prune -mmin +1 2>/dev/null)\" ] && { [ -z \"$p\" ] || ! kill -0 \"$p\" 2>/dev/null; }; then
      rm -rf \"$d/lock\"
    fi
    sleep 0.1
  done
  echo $$ > \"$d/lock/pid\"
  trap 'rm -rf \"$d/lock\"' EXIT
  now=$(date +%s)
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
}
caps() {
  capc=$ncpu; capm=$total_kb
  if [ -f \"$d/cap\" ]; then
    read -r cc cm < \"$d/cap\"
    if num \"$cc\"; then capc=$cc; fi
    if num \"$cm\"; then capm=$cm; fi
  fi
}
"

/-- The script's second half: the ops. -/
def SCRIPT_B : String := "
try_() {
  id=$1; cores=$2; mem=$3; holder=$4; who=$5; cmd=$6
  okid \"$id\"
  cmd=$(printf %s \"$cmd\" | tr '\\n\\t' '  ' | cut -c1-200)
  who=$(printf %s \"$who\" | tr -c 'A-Za-z0-9._:-' '_')
  sample; lock; clean; caps
  if [ \"$holder\" = t ]; then holder=t$((now + 900)); fi
  if [ \"$cores\" = all ]; then cores=$capc; fi
  if ! num \"$cores\" || ! num \"$mem\"; then echo 'bad size' >&2; exit 2; fi
  if [ -e \"$d/off\" ]; then rm -f \"$d/queue/$id\"; echo off; return; fi
  if [ \"$cores\" -gt \"$capc\" ] || [ \"$mem\" -gt \"$capm\" ]; then rm -f \"$d/queue/$id\"; echo \"never $capc $capm\"; return; fi
  first=$now
  if [ -f \"$d/queue/$id\" ]; then read -r first _ < \"$d/queue/$id\"; fi
  ahead=0
  for f in \"$d\"/queue/*; do
    [ -f \"$f\" ] || continue
    o=${f##*/}
    [ \"$o\" = \"$id\" ] && continue
    read -r of _ < \"$f\"
    if [ \"$of\" -lt \"$first\" ] || { [ \"$of\" -eq \"$first\" ] && [ \"$(printf '%s\\n%s\\n' \"$o\" \"$id\" | sort | head -n 1)\" = \"$o\" ]; }; then
      ahead=$((ahead + 1))
    fi
  done
  free=$(cat \"$d\"/claims/* 2>/dev/null | awk -v busy=\"$busy\" -v ncpu=\"$ncpu\" -v capc=\"$capc\" -v capm=\"$capm\" -v av=\"$avail_kb\" '
    {cc+=$1; cm+=$2}
    END{k=int(ncpu/8); if(k<1)k=1; o=int(busy-cc+0.5)-k; if(o<0)o=0
      a=capc-cc; b=ncpu-cc-o; fc=(a<b)?a:b
      x=capm-cm; fm=(x<av)?x:av
      print fc, fm}')
  fc=${free% *}; fm=${free#* }
  if [ \"$cores\" -le \"$fc\" ] && [ \"$mem\" -le \"$fm\" ] && [ \"$ahead\" -eq 0 ]; then
    printf '%s %s %s %s %s %s\\n' \"$cores\" \"$mem\" \"$holder\" \"$now\" \"$who\" \"$cmd\" > \"$d/claims/.$id\" && mv \"$d/claims/.$id\" \"$d/claims/$id\"
    rm -f \"$d/queue/$id\"
    echo \"ok $cores\"
  else
    if [ -f \"$d/queue/$id\" ]; then touch \"$d/queue/$id\"; else echo \"$now $cores $mem $who\" > \"$d/queue/$id\"; fi
    echo \"wait $((fc > 0 ? fc : 0)) $((fm > 0 ? fm : 0)) $ahead\"
  fi
}
case $op in
  try) try_ \"$@\";;
  drop) okid \"$1\"; rm -f \"$d/claims/$1\" \"$d/queue/$1\";;
  ls)
    sample; lock; clean; caps
    offv=0; if [ -e \"$d/off\" ]; then offv=1; fi
    echo \"$ncpu $busy $total_kb $avail_kb $capc $capm $offv\"
    for f in \"$d\"/claims/*; do if [ -f \"$f\" ]; then printf 'c '; cat \"$f\"; fi; done
    for f in \"$d\"/queue/*; do if [ -f \"$f\" ]; then printf 'q '; cat \"$f\"; fi; done;;
  cap)
    # `=` keeps that field as it is
    old='- -'; if [ -f \"$d/cap\" ]; then old=$(cat \"$d/cap\"); fi
    oc=${old% *}; om=${old#* }
    nc=$1; nm=$2
    if [ \"$nc\" = = ]; then nc=$oc; fi
    if [ \"$nm\" = = ]; then nm=$om; fi
    for v in \"$nc\" \"$nm\"; do if [ \"$v\" != - ] && ! num \"$v\"; then echo 'bad cap' >&2; exit 2; fi; done
    echo \"$nc $nm\" > \"$d/cap.tmp.$$\" && mv \"$d/cap.tmp.$$\" \"$d/cap\";;
  off) : > \"$d/off\";;
  on) rm -f \"$d/off\";;
  *) echo \"unknown op: $op\" >&2; exit 2;;
esac
"

/-- The script: `sh -c SCRIPT sh <op> <args…>`; ops `try`, `drop`, `ls`, `cap`, `off`, `on` (sw-compute.md §2). -/
def SCRIPT : String := SCRIPT_A ++ SCRIPT_B

/-- What `try` answered. -/
inductive Try
  | ok (cores : Int)
  | wait (cores mem_kb : Int) (ahead : Int)
  | never (cap_cores cap_mem_kb : Int)
  | off
  /-- the machine did not answer, or not in words -/
  | gone
  deriving BEq, Repr

/-- The script's `try` line. -/
def parseTry (s : String) : Try :=
  match words s with
  | ["ok", c] => (parseInt c).elim .gone .ok
  | ["wait", a, b, c] => match parseInt a, parseInt b, parseInt c with
    | some a, some b, some c => .wait a b c
    | _, _, _ => .gone
  | ["never", a, b] => match parseInt a, parseInt b with
    | some a, some b => .never a b
    | _, _ => .gone
  | ["off"] => .off
  | _ => .gone

/-- Runs the script's op on a machine (none: here) and returns its stdout; none when it failed or did not answer. -/
def sh {m : Type → Type} [Monad m] [Proc m] [Sys m] (mach : Option String) (args : List String) : m (Option String) := do
  match mach with
  | none =>
    let r ← Sys.exec (["sh", "-c", SCRIPT, "sh"] ++ args) {}
    return if r.code == 0 then some r.stdout else none
  | some n =>
    let r ← Proc.output (["hc", "exec", "--on", n, "--timeout", "20", "sh", "-c", SCRIPT, "sh"] ++ args) none []
    return r.bind fun r => if r.code == 0 then some r.stdout else none

/-- Removes a claim and ticket (their absence is no error). -/
def release {m : Type → Type} [Monad m] [Proc m] [Sys m] (mach : Option String) (id : String) : m Unit :=
  discard <| sh mach ["drop", id]

/-- A claim row of `ls`. -/
structure Claim where
  cores : Int
  mem_kb : Int
  holder : String
  start : Int
  who : String
  cmd : String
  deriving BEq, Repr

/-- A ticket row of `ls`. -/
structure Ticket where
  first : Int
  cores : Int
  mem_kb : Int
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
  claims : List Claim := []
  queue : List Ticket := []

/-- The script's `ls` output. -/
def parseLs (s : String) : Option Ls := do
  let ls := splitlines s
  let [a, b, c, d, e, f, g] := words (← ls.head?) | none
  let mut r : Ls := { ncpu := ← parseInt a, busy := ← parseFloat b, total_kb := ← parseInt c, avail_kb := ← parseInt d,
                      cap_cores := ← parseInt e, cap_mem_kb := ← parseInt f, off := (← parseInt g) != 0 }
  for l in ls.tail do
    match words l with
    | "c" :: x :: y :: h :: z :: w :: cmd =>
      r := { r with claims := r.claims ++ [{ cores := ← parseInt x, mem_kb := ← parseInt y, holder := h, start := ← parseInt z, who := w, cmd := " ".intercalate cmd }] }
    | ["q", x, y, z, w] => r := { r with queue := r.queue ++ [{ first := ← parseInt x, cores := ← parseInt y, mem_kb := ← parseInt z, who := w }] }
    | _ => pure ()
  return r

/-- KiB as GiB, one decimal, no unit. -/
def gi (kb : Int) : String := fixed (Float.ofInt kb / 1048576) 1

/-- A span of seconds as `45s`, `4m` or `2h`. -/
def span (s : Int) : String := let s := max 0 s; if s < 60 then s!"{s}s" else if s < 3600 then s!"{s / 60}m" else s!"{s / 3600}h"

/-- `swarm compute`'s lines for a machine (sw-compute.md §4). -/
def render (name : String) (l : Ls) (now : Int) : List String :=
  let cc := (l.claims.map (·.cores)).sum
  let cm := (l.claims.map (·.mem_kb)).sum
  if l.off && l.claims.isEmpty && l.queue.isEmpty then [s!"{name}: off"] else
  [s!"{name}: {if l.off then "off, " else ""}{cc} of {l.cap_cores} cores claimed (cap {l.cap_cores} of {l.ncpu}, {fixed l.busy 1} busy), " ++
    s!"{gi cm} of {gi l.cap_mem_kb}G claimed ({gi l.avail_kb}G available)"] ++
  l.claims.map (fun c => s!"  {c.who}   {c.cores} cores  {gi c.mem_kb}G  {span (now - c.start)}  {c.cmd}") ++
  l.queue.map fun q => s!"  waiting: {q.who} {q.cores} cores {gi q.mem_kb}G {span (now - q.first)}"

/-- A machine's `ls` as JSON. -/
def Ls.json (l : Ls) : Json :=
  Json.mkObj [("ncpu", Json.int l.ncpu), ("busy", Json.float l.busy), ("total_kb", Json.int l.total_kb), ("avail_kb", Json.int l.avail_kb),
    ("cap_cores", Json.int l.cap_cores), ("cap_mem_kb", Json.int l.cap_mem_kb), ("off", .bool l.off),
    ("claims", .arr (l.claims.toArray.map fun c => Json.mkObj [("cores", Json.int c.cores), ("mem_kb", Json.int c.mem_kb),
      ("holder", .str c.holder), ("start", Json.int c.start), ("who", .str c.who), ("cmd", .str c.cmd)])),
    ("queue", .arr (l.queue.toArray.map fun q => Json.mkObj [("first", Json.int q.first), ("cores", Json.int q.cores),
      ("mem_kb", Json.int q.mem_kb), ("who", .str q.who)]))]

/-- What a job claims, from its history rows (wall_s, cpu_s, peak_kb, source) on any machine: cores are the default or the
largest `cpu_s / wall_s` rounded up over rows with a CPU reading that `swarm run` did not itself record (`source` run holds
a %CPU sample), whichever is more, so history only raises it; memory is the largest peak × 1.25 over every row; none
without a row that has a wall time. -/
def size (rows : List (Int × Int × Int × String)) : Option (Int × Int) :=
  let rs := rows.filter (·.1 > 0)
  if rs.isEmpty then none else
  let cores := rs.foldl (fun a r => if r.2.1 > 0 && r.2.2.2 != "run" then max a ((r.2.1 + r.1 - 1) / r.1) else a) DEFAULT_CORES
  let peak := rs.foldl (fun a r => max a r.2.2.1) 0
  some (cores, if peak ≤ 0 then DEFAULT_MEM_KB else (peak * 5 + 3) / 4)

/-- The cmd-cost rows (wall_s, cpu_s, peak_kb) of this repo's command `line`, from any machine. -/
def history {m : Type → Type} [Monad m] [Env m] [Sys m] [Git m] (line : String) : m (List (Int × Int × Int × String)) := do
  if !(← Cost.exists?) then return []
  let some repo ← Cost.repoName | return []
  let rows := ((← Sys.sqlAt (← Cost.path) Cost.SCHEMA [("select wall_s,cpu_s,peak_kb,source from cmd where repo=? and key=?",
    [.text repo, .text (Cost.key line)])]).headD #[]).toList
  return rows.map fun r => (Cost.vi (r.getD 0 .null), Cost.vi (r.getD 1 .null), Cost.vi (r.getD 2 .null), Cost.vs (r.getD 3 .null))

end SwarmLean.Compute
