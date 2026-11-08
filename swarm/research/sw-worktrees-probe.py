#!/usr/bin/env python3
"""Time per-agent checkout options for a repo, in a scratch dir.

usage: python3 -I sw-worktrees-probe.py <repo> <scratch> [runs]
Reads <repo> only (a --shared bare clone is the base). Prints the median
seconds and disk of each option; ext4 has no reflink, so that row says so.
"""
import os, shutil, statistics, subprocess, sys, time

repo, scratch = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
runs = int(sys.argv[3]) if len(sys.argv) > 3 else 5
bare = os.path.join(scratch, "bare.git")


def sh(*a, cwd=None):
    return subprocess.run(a, cwd=cwd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)


def du(p):
    return subprocess.run(["du", "-sk", p], capture_output=True, text=True).stdout.split()[0] + "K"


def timed(name, make):
    ts, out = [], None
    for i in range(runs):
        dst = os.path.join(scratch, f"{name}-{i}")
        shutil.rmtree(dst, ignore_errors=True)
        t = time.perf_counter()
        r = make(dst)
        ts.append(time.perf_counter() - t)
        if r is not None and r.returncode:
            print(f"{name:<22} failed: {r.stderr.strip()[:120]}")
            return
        out = dst
    print(f"{name:<22} {statistics.median(ts) * 1000:7.0f} ms  {du(out):>8}")


def sparse(dst):
    sh("git", "worktree", "add", "-q", "--no-checkout", "--detach", dst, "HEAD", cwd=bare)
    sh("git", "sparse-checkout", "set", "--cone", "server", cwd=dst)
    return sh("git", "checkout", "-q", cwd=dst)


os.makedirs(scratch, exist_ok=True)
shutil.rmtree(bare, ignore_errors=True)
assert sh("git", "clone", "-q", "--bare", "--shared", repo, bare).returncode == 0
src = os.path.join(scratch, "src")
shutil.rmtree(src, ignore_errors=True)
sh("git", "worktree", "add", "-q", "--detach", src, "HEAD", cwd=bare)

timed("worktree add", lambda d: sh("git", "worktree", "add", "-q", "--detach", d, "HEAD", cwd=bare))
timed("worktree add sparse", sparse)
timed("clone --shared", lambda d: sh("git", "clone", "-q", "--shared", repo, d))
timed("clone --reference", lambda d: sh("git", "clone", "-q", "--reference", repo, repo, d))
timed("clone --no-local", lambda d: sh("git", "clone", "-q", "--no-local", repo, d))
timed("cp -r worktree", lambda d: sh("cp", "-r", src, d))
r = sh("cp", "--reflink=always", os.path.join(src, "README.md"), os.path.join(scratch, "reflink-test"))
print(f"{'cp --reflink=always':<22} {'ok' if r.returncode == 0 else 'unsupported: ' + r.stderr.strip()[-40:]}")
sh("git", "worktree", "prune", cwd=bare)
