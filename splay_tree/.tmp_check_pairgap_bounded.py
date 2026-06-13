"""Is the per-step pair gap `actualResetLowerPairGapAt` bounded by a CONSTANT?

pair_gap(actual, reset, z) =
   max(0,  actual.spl(z) + splay(actual,z).spl(q)
         - actual.spl(q) - reset.spl(z) - splay(reset,z).spl(q))

where (actual, reset) are REACHABLE states after some 231-avoiding prefix of
lower accesses from a tree rooted at q, and z < q is a key.

If max pair_gap is bounded as q grows  -> hlocal/gap_drop_of_local_bound can
close the general case with that constant.
If it grows with q -> the local reduction is too weak; hlower_drop must be
proved directly (the full step holds with D=1 per earlier test, but not via
this lossy local lemma).
"""
from __future__ import annotations
import importlib.util, random, time
from itertools import product
from pathlib import Path

BASE = Path(__file__).with_name(".tmp_pair_certificate_search.py")
SPEC = importlib.util.spec_from_file_location("b", BASE)
assert SPEC and SPEC.loader
base = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl, splay, N, E = base.path_len, base.splay, base.N, base.E


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


def pair_gap(actual, reset, z, q):
    v = (spl(actual, z) + spl(splay(actual, z), q)
         - spl(actual, q) - spl(reset, z) - spl(splay(reset, z), q))
    return max(0, v)


def main():
    random.seed(11)
    deadline = time.time() + 110
    worst = {}

    def rec(q, v, info):
        if q not in worst or v > worst[q][0]:
            worst[q] = (v, info)

    # exhaustive small q
    for q in range(1, 7):
        for L in base.trees(0, q):
            init = N(L, q, E)
            for dlen in range(0, 5):
                for done in product(range(q), repeat=dlen):
                    if not base.avoids231(list(done)):
                        continue
                    a = splay_after(init, list(done))
                    r = reset_after(init, list(done), q)
                    for z in range(q):
                        rec(q, pair_gap(a, r, z, q), f"q={q} done={list(done)} z={z}")
        if time.time() > deadline:
            break

    # structured large q (left spine + sequential prefixes = the hard family)
    while time.time() < deadline:
        q = random.choice([8, 13, 21, 34, 55, 89, 144])
        for shape in ("left", "balanced", "random", "right"):
            c = base.rooted_tree(q - 1, 0, shape)
            if keys(c) != list(range(q)):
                continue
            init = N(c, q, E)
            for done in (list(range(q)), list(reversed(range(q))),
                         list(range(0, q, 2)), base.random_avoiding_seq(0, q, q)):
                done = [v for v in done if v < q]
                if not base.avoids231(done):
                    continue
                for cut in (0, q // 3, q // 2, 2 * q // 3, len(done)):
                    pre = done[:cut]
                    a = splay_after(init, pre)
                    r = reset_after(init, pre, q)
                    for z in set(done):
                        rec(q, pair_gap(a, r, z, q), f"{shape} cut={cut} z={z}")

    print("  q :  max pair_gap (reachable)")
    for q in sorted(worst):
        v, info = worst[q]
        print(f"  {q:>4}:   {v:5.1f}   @ {info}")
    vals = [worst[q][0] for q in worst]
    print("\nVERDICT:", "pair_gap BOUNDED -> generalize hzero with that constant"
          if max(vals) < 6 else "pair_gap GROWS with q -> need DIRECT proof of hlower_drop (not via local lemma)")


if __name__ == "__main__":
    main()
