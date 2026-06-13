"""Pivotal: is actualResetFirstLowerPairGapPotential after a lower access ALWAYS 0
for 231-AVOIDING sequences? (If yes, Codex's hzero_after_lower is true and closes
the upper block; if no, the budget kernel is required.)

Test descending and random-avoiding sequences (231-avoiding) at growing q, over
left-spine / balanced / random initial trees, scanning all prefix positions.
"""
from __future__ import annotations
import importlib.util, random
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


worst = {}
mincex = None
for q in range(3, 22):
    for shape in ("left", "balanced", "right", "random"):
        c = base.rooted_tree(q, 0, shape)          # keys 0..q, q at root
        if keys(c) != list(range(q + 1)):
            continue
        seqs = [list(reversed(range(q)))]          # descending (231-avoiding)
        for _ in range(40):
            seqs.append(base.random_avoiding_seq(0, q, random.choice([q, 2 * q])))
        for seq in seqs:
            seq = [v for v in seq if v < q]
            if len(seq) < 2 or not base.avoids231(seq):
                continue
            for pos in range(len(seq) - 1):
                g = gap_after_lower(c, q, seq[:pos], seq[pos], seq[pos + 1:])
                if g > worst.get(q, 0):
                    worst[q] = g
                if g > 0 and (mincex is None or (q, len(seq), pos) < mincex[0]):
                    mincex = ((q, len(seq), pos), shape, list(seq), pos, g)

print("  q : max gap_after_lower over 231-avoiding seqs")
for q in sorted(worst):
    print(f"  {q:>3}: {worst[q]}")
print("\nhzero_after_lower holds for ALL tested 231-avoiding seqs:",
      all(v == 0 for v in worst.values()))
if mincex:
    _, shape, seq, pos, g = mincex
    print(f"\nSMALLEST COUNTEREXAMPLE: q in tree shape '{shape}', seq={seq}")
    print(f"  done={seq[:pos]}  i={seq[pos]}  future={seq[pos+1:]}  -> gap_after_lower={g} (>0)")
