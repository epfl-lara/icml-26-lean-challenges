"""Pin down the SHARPER reset-budget-drop lemma needed to prove hlower_drop
DIRECTLY (the current gap_drop_of_local_bound only uses Delta_bb >= 1, too weak
because the next-step pair gap g1 ~ log q).

Rearranged hlower_drop (G=1):   g1 <= D + A*Delta_bb + H*(qb - qa)
with reachable (actual,reset) after a 231-avoiding lower prefix `done`, then a
lower head i, then future; g1 = pair gap of first lower key in future.

  Delta_bb = bb(reset, i::future, q) - bb(reset_after_i, future, q)   (>=1 known)
  qb = actual.spl(q),  qa = splay(actual, Yi).spl(q)   (qa <= qb+2 known)

We report worst-case of:
  S_direct = g1 - (D + A*Delta_bb + H*(qb-qa))      [must be <= 0 : the target]
  S_dropreq = (g1 + 1) - 3*Delta_bb                  [<=0  =>  Delta_bb >= (g1+1)/3]
  S_path   = g1 - 3*(reset.spl(Yi) - 1)              [is path-to-i a usable proxy?]
with (A,G,H,D) = (3,1,2,3).
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
A, G, H, D = 3.0, 1.0, 2.0, 3.0


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


def bb(t, seq, q):
    hull = set(base.search_path_keys(t, q))
    for x in seq:
        hull.update(base.search_path_keys(t, x))
    return len(seq) + len(hull)


def pair_gap(a, r, z, q):
    return max(0, spl(a, z) + spl(splay(a, z), q) - spl(a, q) - spl(r, z) - spl(splay(r, z), q))


def first_lower(seq, q):
    for v in seq:
        if v < q:
            return v
    return None


def step_metrics(init, q, done, i, future):
    a = splay_after(init, done)
    r = reset_after(init, done, q)
    if i >= q:
        return None
    qb = spl(a, q)
    qa = spl(splay(a, i), q)
    a2 = splay(a, i)            # actual after accessing i (no q reroot)
    r2 = splay(splay(r, i), q)  # reset after i
    z = first_lower(future, q)
    g1 = 0.0 if z is None else pair_gap(a2, r2, z, q)
    dbb = bb(r, [i] + future, q) - bb(r2, future, q)
    s_direct = g1 - (D + A * dbb + H * (qb - qa))
    s_dropreq = (g1 + 1) - 3 * dbb
    s_path = g1 - 3 * (spl(r, i) - 1)
    s_b1 = (spl(r, i) - 1) - dbb          # B1: Delta_bb >= reset.spl(i) - 1 ?
    return s_direct, s_dropreq, s_path, dbb, s_b1


def main():
    random.seed(13)
    deadline = time.time() + 110
    worst = {}

    def rec(q, key, v, info):
        worst.setdefault(q, {})
        if key not in worst[q] or v > worst[q][key][0]:
            worst[q][key] = (v, info)

    for q in range(1, 6):
        for L in base.trees(0, q):
            init = N(L, q, E)
            for length in range(1, 6):
                for seq in product(range(q), repeat=length):
                    if not base.avoids231(list(seq)):
                        continue
                    seq = list(seq)
                    for pos in range(length):
                        if seq[pos] >= q:
                            continue
                        m = step_metrics(init, q, seq[:pos], seq[pos], seq[pos + 1:])
                        if m is None:
                            continue
                        sd, sr, sp, dbb, sb1 = m
                        rec(q, "direct", sd, f"seq={seq} pos={pos} dbb={dbb}")
                        rec(q, "dropreq", sr, f"seq={seq} pos={pos} dbb={dbb}")
                        rec(q, "path", sp, f"seq={seq} pos={pos}")
                        rec(q, "b1", sb1, f"seq={seq} pos={pos} dbb={dbb}")
        if time.time() > deadline:
            break

    while time.time() < deadline:
        q = random.choice([8, 13, 21, 34, 55, 89, 144])
        for shape in ("left", "balanced", "random", "right"):
            c = base.rooted_tree(q - 1, 0, shape)
            if keys(c) != list(range(q)):
                continue
            init = N(c, q, E)
            length = random.choice([q, 2 * q])
            for seq in (list(range(q)), list(reversed(range(q))),
                        base.random_avoiding_seq(0, q, min(length, 200))):
                seq = [v for v in seq if v < q]
                if not base.avoids231(seq):
                    continue
                for pos in range(0, len(seq), max(1, len(seq) // 8)):
                    m = step_metrics(init, q, seq[:pos], seq[pos], seq[pos + 1:])
                    if m is None:
                        continue
                    sd, sr, sp, dbb, sb1 = m
                    rec(q, "direct", sd, f"{shape} pos={pos} dbb={dbb}")
                    rec(q, "dropreq", sr, f"{shape} pos={pos} dbb={dbb}")
                    rec(q, "path", sp, f"{shape} pos={pos}")
                    rec(q, "b1", sb1, f"{shape} pos={pos} dbb={dbb}")

    print("worst-case per q  (<=0 is GOOD).  direct = target ineq;  dropreq: Delta_bb>=(g1+1)/3;  path: g1<=3(spl_r(i)-1)")
    for q in sorted(worst):
        d = worst[q]
        print(f"  q={q:>4}:  direct={d['direct'][0]:+5.1f}   dropreq={d['dropreq'][0]:+6.1f}   path={d['path'][0]:+6.1f}   b1={d['b1'][0]:+6.1f}")
    allok = all(worst[q]['direct'][0] <= 0 for q in worst)
    print("\nDIRECT target holds everywhere:", allok)
    dropok = all(worst[q]['dropreq'][0] <= 0 for q in worst)
    print("Clean sub-lemma  Delta_bb >= (g1+1)/3  holds everywhere:", dropok)
    if not allok:
        bad = max(worst, key=lambda q: worst[q]['direct'][0])
        print("  worst direct @ q=", bad, worst[bad]['direct'])


if __name__ == "__main__":
    main()
