#!/usr/bin/env python3
"""Measure what the proposed watchd conflict tick would report for a live repo, without writing to it.
usage: sw-locks-probe.py REPO SCRATCH   (SCRATCH gets a --shared bare clone; REPO's worktrees are only read)"""
import difflib, itertools, os, re, subprocess, sys, tempfile, time

TOK = re.compile(r"\w+|[^\w\s]|\n")
HUNK = re.compile(r"^<<<<<<< .*?\n(.*?)^\|\|\|\|\|\|\| .*?\n(.*?)^=======\n(.*?)^>>>>>>> ", re.S | re.M)


def edits(base, side):
    """Base-token spans one side changed, half-open; i1 == i2 is an insertion at i1."""
    return [(i1, i2) for op, i1, i2, _, _ in difflib.SequenceMatcher(None, base, side, autojunk=False).get_opcodes()
            if op != "equal"]


def clash(a, b):
    """Two spans clash if both change a common base token, or one inserts strictly inside the other's change."""
    (a1, a2), (b1, b2) = a, b
    if a1 == a2 and b1 == b2:
        return False
    if a1 == a2:
        return b1 < a1 < b2
    if b1 == b2:
        return a1 < b1 < a2
    return a1 < b2 and b1 < a2


def real_hunk(base, ours, theirs):
    b = TOK.findall(base)
    return any(clash(x, y) for x in edits(b, TOK.findall(ours)) for y in edits(b, TOK.findall(theirs)))


assert not real_hunk("module L (a, b) where\n", "module L (a, b, c) where\n", "module L (a, b, d) where\n")
assert not real_hunk("f a b\n", "f a x b\n", "g a b\n")
assert real_hunk("x = f a\n", "x = g a\n", "x = h a\n")
assert not real_hunk("f a b c\n", "f a b c d\n", "f z\n")  # an insertion at the edge of a replaced span merges
assert real_hunk("f a b c\n", "f a x b c\n", "f z\n")  # an insertion inside a replaced span does not


def sh(*a, **kw):
    return subprocess.run(a, capture_output=True, text=True, **kw)


def snapshot(gd, wt, env):
    """Commit wt's working state (tracked + untracked, not ignored) into gd; return (commit, changed paths)."""
    with tempfile.NamedTemporaryFile() as idx:
        idx.write(open(sh("git", "-C", wt, "rev-parse", "--path-format=absolute", "--git-path", "index").stdout.strip(), "rb").read())
        idx.flush()
        e = dict(env, GIT_WORK_TREE=wt, GIT_INDEX_FILE=idx.name)
        head = sh("git", "-C", wt, "rev-parse", "HEAD").stdout.strip()
        sh(*gd, "add", "-A", env=e)
        tree = sh(*gd, "write-tree", env=e).stdout.strip()
    commit = sh(*gd, "commit-tree", tree, "-p", head, "-m", "snap", env=env).stdout.strip()
    return commit


def main(repo, scratch):
    gdir = os.path.join(scratch, "probe.git")
    if not os.path.isdir(gdir):
        sh("git", "clone", "-q", "--shared", "--bare", repo, gdir)
    common = sh("git", "-C", repo, "rev-parse", "--path-format=absolute", "--git-common-dir").stdout.strip()
    os.makedirs(os.path.join(gdir, "info"), exist_ok=True)
    ex = os.path.join(common, "info", "exclude")
    if os.path.exists(ex):  # the clone must ignore what the repo ignores, or add -A hashes build output
        open(os.path.join(gdir, "info", "exclude"), "w").write(open(ex).read())
    sh("git", "--git-dir", gdir, "fetch", "-q", repo, "+refs/heads/*:refs/heads/*")
    gd = ["git", "-c", "merge.conflictStyle=diff3", "--git-dir", gdir]
    env = dict(os.environ, GIT_DIR=gdir, GIT_OPTIONAL_LOCKS="0")
    main_ = sh(*gd, "rev-parse", "main").stdout.strip()
    wts = [l.split()[1] for l in sh("git", "-C", repo, "worktree", "list", "--porcelain").stdout.splitlines()
           if l.startswith("worktree ")]
    t0 = time.perf_counter()
    snap, files = {}, {}
    for w in wts:
        n = os.path.relpath(w, repo)
        snap[n] = snapshot(gd, w, env)
        mb = sh(*gd, "merge-base", main_, snap[n]).stdout.strip()
        files[n] = set(sh(*gd, "diff", "--name-only", mb, snap[n]).stdout.split())
    t1 = time.perf_counter()
    pairs = [(a, b) for a, b in itertools.combinations(sorted(snap), 2) if files[a] & files[b]]
    shared = sum(len(files[a] & files[b]) for a, b in pairs)
    line_files = line_pairs = hunks = 0
    real = {}
    for a, b in pairs:
        r = sh(*gd, "merge-tree", "--write-tree", "--name-only", "--no-messages", snap[a], snap[b])
        if r.returncode != 1:
            continue
        line_pairs += 1
        tree, *cf = r.stdout.splitlines()
        for f in set(cf):
            line_files += 1
            for m in HUNK.finditer(sh(*gd, "show", f"{tree}:{f}").stdout):
                hunks += 1
                if real_hunk(m.group(2), m.group(1), m.group(3)):
                    real.setdefault((a, b), set()).add(f)
    t2 = time.perf_counter()
    print(f"worktrees {len(snap)}: snapshots {t1 - t0:.2f}s")
    print(f"file overlap: {len(pairs)} pairs, {shared} (pair, file)")
    print(f"line conflicts (git): {line_pairs} pairs, {line_files} (pair, file), {hunks} hunks")
    print(f"token conflicts: {len(real)} pairs, {sum(map(len, real.values()))} (pair, file)")
    print(f"merges + classify {t2 - t1:.2f}s; tick {t2 - t0:.2f}s")
    for k, v in sorted(real.items()):
        print("  ", *k, sorted(v))


if __name__ == "__main__":
    main(os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2]))
