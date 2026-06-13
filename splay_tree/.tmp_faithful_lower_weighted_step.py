"""Faithful test of the RESET WEIGHTED STEP that `hlower` reduces to
(see pivotResetLowerPathSum_..._of_weighted_step_... in the Lean file):

  spl(t,x) + spl(splay(t,x), q) + A * bb(splay(splay(t,x),q), xs, q)
      <=  C + A * bb(t, x::xs, q)

for t a BST rooted at q, x<q, all of (x::xs) < q, and (x::xs) 231-avoiding.
bb = boundaryBudget = len + |hull|, hull = search paths to q and to each elt.

This is the shape whose A=16,C=0 instance was refuted earlier; here we
look for ANY (A,C) and, crucially, whether the minimal C scales with q.
"""
from __future__ import annotations
import argparse, importlib.util, random, time
from itertools import product
from pathlib import Path

BASE = Path(__file__).with_name(".tmp_pair_certificate_search.py")
SPEC = importlib.util.spec_from_file_location("b", BASE)
assert SPEC and SPEC.loader
base = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(base)
spl, splay = base.path_len, base.splay


def bb(t, seq, q):
    hull = set(base.search_path_keys(t, q))
    for x in seq:
        hull.update(base.search_path_keys(t, x))
    return len(seq) + len(hull)


def avoids231(seq):
    return base.avoids231(list(seq))


def need(t, q, x, xs, A):
    after = splay(splay(t, x), q)
    lhs = spl(t, x) + spl(splay(t, x), q) + A * bb(after, xs, q)
    return lhs - A * bb(t, [x] + xs, q)


def rooted_at_q(q):
    """All BSTs that are node(L, q, empty) with L a BST on {0..q-1}."""
    return [base.N(L, q, base.E) for L in base.trees(0, q)]


def upd(best, q, v, pl):
    if q not in best or v > best[q][0]:
        best[q] = (v, pl)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--seconds", type=float, default=150.0)
    p.add_argument("--qmax-exhaustive", type=int, default=6)
    p.add_argument("--len", type=int, default=6)
    p.add_argument("--seed", type=int, default=7)
    p.add_argument("--A", type=str, default="2,3,4")
    args = p.parse_args()
    random.seed(args.seed)
    As = [float(a) for a in args.A.split(",")]
    deadline = time.time() + args.seconds
    best = {A: {} for A in As}

    # exhaustive small q
    for q in range(1, args.qmax_exhaustive + 1):
        trees = rooted_at_q(q)
        for length in range(1, args.len + 1):
            for seq in product(range(q), repeat=length):
                if not avoids231(seq):
                    continue
                x, xs = seq[0], list(seq[1:])
                for t in trees:
                    for A in As:
                        upd(best[A], q, need(t, q, x, xs, A),
                            {"q": q, "seq": list(seq)})
        if time.time() > deadline:
            break

    # structured large q
    shapes = ("left", "balanced", "random", "right")
    qs = [8, 13, 21, 34, 55, 89]
    while time.time() < deadline:
        q = random.choice(qs)
        t = base.rooted_tree(q, 0, random.choice(shapes))  # keys 0..q, q at root
        length = random.choice([3, 5, 8, 13, 21, 34, 55])
        for seq in ([0] * length,
                    list(range(min(length, q))),                 # sorted ascending
                    list(range(min(length, q) - 1, -1, -1)),     # descending
                    base.random_avoiding_seq(0, q, length)):
            seq = [v for v in seq if v < q]
            if len(seq) < 1 or not avoids231(seq):
                continue
            x, xs = seq[0], seq[1:]
            for A in As:
                upd(best[A], q, need(t, q, x, xs, A),
                    {"q": q, "len": len(seq), "shape": "struct"})

    for A in As:
        print(f"\n==== reset weighted step: A={A}  (minimal C needed = worst 'need') ====")
        for q in sorted(best[A]):
            v, pl = best[A][q]
            print(f"  q={q:>4}:  C_needed = {v:+.1f}   @ {pl}")


if __name__ == "__main__":
    main()
