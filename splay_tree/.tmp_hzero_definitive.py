"""Definitive: does gap_after_lower > 0 ever occur for a genuine 231-avoiding
sequence (done++i::future), with z = the actual next lower key in future?

Exhaustive for small q (all rooted trees, all 231-avoiding value-sequences, all
positions) + heavy random for large q. Print the first/smallest witness, or
declare hzero_after_lower empirically TRUE.
"""
from __future__ import annotations
import importlib.util, random
from itertools import product
from pathlib import Path

BASE = Path(__file__).with_name(".tmp_pair_certificate_search.py")
SPEC = importlib.util.spec_from_file_location("b", BASE)
assert SPEC and SPEC.loader
base = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl, splay, N, E = base.path_len, base.splay, base.N, base.E
random.seed(0)


def keys(t):
    return [] if not t else keys(t[0]) + [t[1]] + keys(t[2])


def splay_after(t, seq):
    for x in seq:
        t = splay(t, x)
    return t


def reset_after(t, seq, q):
    for x in seq:
        if x < q:
            t = splay(splay(t, x), q)
    return t


def gap_after_lower(init, q, done, i, future):
    a = splay_after(init, done + [i])
    r = reset_after(init, done + [i], q)
    for z in future:
        if z < q:
            return max(0, spl(a, z) + spl(splay(a, z), q) - spl(a, q)
                       - spl(r, z) - spl(splay(r, z), q))
    return 0


witnesses = []

# Exhaustive small q
for q in range(2, 7):
    for L in base.trees(0, q):
        init = N(L, q, E)
        for length in range(2, 7):
            for seq in product(range(q), repeat=length):
                s = list(seq)
                if not base.avoids231(s):
                    continue
                for pos in range(length - 1):
                    if s[pos] >= q:
                        continue
                    g = gap_after_lower(init, q, s[:pos], s[pos], s[pos + 1:])
                    if g > 0:
                        witnesses.append((q, keys(L), s, pos, g))
    if witnesses:
        break

phase = "exhaustive q<=6"
# Heavy random large q if nothing small
if not witnesses:
    phase = "random up to q=60"
    for trial in range(200000):
        q = random.choice([8, 13, 21, 34, 55, 60])
        shape = random.choice(("left", "balanced", "right", "random"))
        init = base.rooted_tree(q, 0, shape)
        if keys(init) != list(range(q + 1)):
            continue
        s = base.random_avoiding_seq(0, q, random.choice([q, 2 * q, 3 * q]))
        s = [v for v in s if v < q]
        if len(s) < 2 or not base.avoids231(s):
            continue
        for pos in range(len(s) - 1):
            g = gap_after_lower(init, q, s[:pos], s[pos], s[pos + 1:])
            if g > 0:
                witnesses.append((q, "rand", s, pos, g))
                break
        if len(witnesses) >= 3:
            break

print(f"phase: {phase}")
print(f"witnesses with gap_after_lower > 0: {len(witnesses)}")
for q, lk, s, pos, g in witnesses[:5]:
    print(f"  q={q} leftKeys={lk} seq={s} pos={pos} done={s[:pos]} i={s[pos]} future={s[pos+1:]} gap={g}")
print("\nCONCLUSION:", "hzero_after_lower is FALSE (counterexample exists)"
      if witnesses else "hzero_after_lower holds on ALL tested 231-avoiding inputs (Codex's route can close it)")
