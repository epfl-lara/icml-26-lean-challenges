"""Faithful empirical test of the EXACT Lean obligations consumed by
`traversal_conjecture_of_potential_upper_blocks`, instantiated with
`upperResetFirstPairQPotential A G H`.

Lean potential (see .tmp_traversal_lemmas.lean):
  Psi(done, future) =
      A * boundaryBudget(suffixResetTreeAfter init done, future, q)
    + G * actualResetFirstLowerPairGapPotential(init, done, future)
    + H * search_path_len(splayTreeAfter init done, q)

where actualResetFirstLowerPairGapPotential charges the PAIR gap of the
FIRST index j in `future` with X j < q:
    max(0,  a.spl(x) + splay(a,x).spl(q)
          - a.spl(q) - r.spl(x) - splay(r,x).spl(q))
  with a = splayTreeAfter(init,done), r = suffixResetTreeAfter(init,done,q).

Obligations (must hold for constant D, with G<=H and G+H<=D, A,G,H,D>=0):
  hlt_step (head x<q):
     a.spl(x) + splay(a,x).spl(q) + Psi(done+[x], future)
       <= a.spl(q) + r.spl(x) + splay(r,x).spl(q) + D + Psi(done, x::future)
  heq_step (head x=q):
     Psi(done+[q], future) <= D + Psi(done, q::future)

We report, per total_n, the worst-case slack actually required:
  Dlt = max over lower-head splits of (LHS - (RHS - D))   [i.e. minimal D needed]
  Deq = max over pivot-head splits of (Psi(after) - Psi(before))
If Dlt is bounded as total_n grows -> the potential closes the proof.
If Dlt grows with n -> this Psi is too weak; needs strengthening.
"""
from __future__ import annotations

import argparse
import importlib.util
import random
import time
from itertools import product
from pathlib import Path

BASE_PATH = Path(__file__).with_name(".tmp_pair_certificate_search.py")
SPEC = importlib.util.spec_from_file_location("splay_search_base", BASE_PATH)
assert SPEC is not None and SPEC.loader is not None
base = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(base)

spl = base.path_len
splay = base.splay


def splay_after(t, seq):
    for x in seq:
        t = splay(t, x)
    return t


def suffix_reset_after(t, seq, q):
    for x in seq:
        if x < q:
            t = splay(splay(t, x), q)
    return t


def boundary_budget(t, seq, q):
    hull = set(base.search_path_keys(t, q))
    for x in seq:
        hull.update(base.search_path_keys(t, x))
    return len(seq) + len(hull)


def first_lower_pair_gap(init, q, done, future):
    """PAIR gap of the first index in `future` whose value < q (else 0)."""
    x = None
    for v in future:
        if v < q:
            x = v
            break
    if x is None:
        return 0.0
    a = splay_after(init, done)
    r = suffix_reset_after(init, done, q)
    val = (spl(a, x) + spl(splay(a, x), q)
           - spl(a, q) - spl(r, x) - spl(splay(r, x), q))
    return float(max(0, val))


def psi(init, q, done, future, A, G, H):
    a = splay_after(init, done)
    r = suffix_reset_after(init, done, q)
    return (A * boundary_budget(r, future, q)
            + G * first_lower_pair_gap(init, q, done, future)
            + H * spl(a, q))


def hlt_need(init, q, done, x, future, A, G, H):
    """Minimal D required by hlt_step at this lower-head split."""
    a = splay_after(init, done)
    r = suffix_reset_after(init, done, q)
    lhs = spl(a, x) + spl(splay(a, x), q) + psi(init, q, done + [x], future, A, G, H)
    rhs0 = spl(a, q) + spl(r, x) + spl(splay(r, x), q) + psi(init, q, done, [x] + future, A, G, H)
    return lhs - rhs0


def heq_need(init, q, done, future, A, G, H):
    """Minimal D required by heq_step at this pivot-head split."""
    return psi(init, q, done + [q], future, A, G, H) - psi(init, q, done, [q] + future, A, G, H)


def valid_upper(seq, q):
    return all(x <= q for x in seq) and base.avoids231(seq)


def update(best, key, n, value, payload):
    cur = best.setdefault(key, {})
    prev = cur.get(n)
    if prev is None or value > prev[0]:
        cur[n] = (value, payload)


def exhaustive(args, deadline, best):
    cases = 0
    for total_n in range(2, args.total_n + 1):
        for q in range(1, total_n):
            rooted = [base.N(l, q, r)
                      for l in base.trees(0, q)
                      for r in base.trees(q + 1, total_n - q - 1)]
            for length in range(1, args.length + 1):
                for seq0 in product(range(q + 1), repeat=length):
                    if time.time() > deadline:
                        return cases
                    seq = list(seq0)
                    if not valid_upper(seq, q):
                        continue
                    for init in rooted:
                        for pos, x in enumerate(seq):
                            done, future = seq[:pos], seq[pos + 1:]
                            pl = {"total_n": total_n, "q": q, "seq": seq,
                                  "pos": pos, "x": x}
                            if x < q:
                                update(best, "lt", total_n,
                                       hlt_need(init, q, done, x, future, args.a, args.g, args.h), pl)
                            else:
                                update(best, "eq", total_n,
                                       heq_need(init, q, done, future, args.a, args.g, args.h), pl)
                            cases += 1
    return cases


def structured(args, deadline, best):
    cases = 0
    shapes = ("balanced", "left", "right", "random")
    qs = [5, 8, 13, 21, 34, 55, 89, 144]
    lengths = [2, 3, 5, 8, 13, 21, 34, 55, 89]
    while time.time() < deadline:
        q = random.choice(qs)
        total_n = q + 1 + random.choice([0, 1, q // 2, q, 2 * q])
        init = base.rooted_tree(q, total_n - q - 1, random.choice(shapes))
        length = random.choice(lengths)
        for seq in ([0] * length,
                    [0 if i % 2 == 0 else q for i in range(length)],
                    sorted(random.randrange(q + 1) for _ in range(length)),
                    base.random_avoiding_seq(0, q, length)):
            if not valid_upper(seq, q):
                continue
            for pos, x in enumerate(seq):
                done, future = seq[:pos], seq[pos + 1:]
                pl = {"q": q, "total_n": total_n, "seq_len": len(seq), "pos": pos, "x": x}
                if x < q:
                    update(best, "lt", q, hlt_need(init, q, done, x, future, args.a, args.g, args.h), pl)
                else:
                    update(best, "eq", q, heq_need(init, q, done, future, args.a, args.g, args.h), pl)
                cases += 1
    return cases


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--seconds", type=float, default=120.0)
    p.add_argument("--seed", type=int, default=20260605)
    p.add_argument("--total-n", type=int, default=9)
    p.add_argument("--length", type=int, default=7)
    p.add_argument("--a", type=float, default=64.0)
    p.add_argument("--g", type=float, default=1.0)
    p.add_argument("--h", type=float, default=2.0)
    args = p.parse_args()
    random.seed(args.seed)
    deadline = time.time() + args.seconds
    best: dict = {}
    print(f"# A={args.a} G={args.g} H={args.h}  (constraints: G<=H {args.g<=args.h}; need G+H<=D)")
    n_ex = exhaustive(args, deadline, best)
    n_st = structured(args, min(deadline, time.time() + args.seconds), best) if time.time() < deadline else 0
    print(f"# exhaustive cases={n_ex}  structured cases={n_st}")
    for key, label in (("lt", "hlt_step required D"), ("eq", "heq_step required slack (<=G+H?)")):
        print(f"\n== {label} : worst-case by n ==")
        for n in sorted(best.get(key, {})):
            val, pl = best[key][n]
            print(f"  n/q={n:>4}:  need = {val:+.1f}   @ {pl}")


if __name__ == "__main__":
    main()
