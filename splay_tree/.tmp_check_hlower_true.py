"""Is hlower actually TRUE?  hlower:  pivotResetLowerPathSum(t,xs) <= K * boundaryBudget(t,xs,q)
for a CONSTANT K, over BST t rooted at q, xs all < q, 231-avoiding.

We measure the worst-case ratio  pivotResetLowerPathSum / boundaryBudget  and
also / length, as q and length grow. If the ratio stays bounded -> hlower true
(constant K exists). If it grows with q -> hlower itself is false.
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


def reset_lower_sum(t, q, xs):
    s = 0.0
    for x in xs:
        s += spl(t, x)
        t = splay(splay(t, x), q)
    return s


def bb(t, seq, q):
    hull = set(base.search_path_keys(t, q))
    for x in seq:
        hull.update(base.search_path_keys(t, x))
    return len(seq) + len(hull)


def main():
    random.seed(3)
    deadline = time.time() + 120
    worst = {}  # q -> (ratio_bb, ratio_len, info)

    def rec(q, val_bb, val_len, info):
        cur = worst.get(q)
        if cur is None or val_bb > cur[0]:
            worst[q] = (val_bb, val_len, info)

    # exhaustive small q
    for q in range(1, 7):
        for L in base.trees(0, q):
            t = N(L, q, E)
            for length in range(1, 7):
                for xs in product(range(q), repeat=length):
                    if not base.avoids231(list(xs)):
                        continue
                    xs = list(xs)
                    s = reset_lower_sum(t, q, xs)
                    b = bb(t, xs, q)
                    rec(q, s / b, s / len(xs), f"exh seq={xs}")
        if time.time() > deadline:
            break

    # structured large q: sequential + adversarial, left spine and others
    while time.time() < deadline:
        q = random.choice([8, 13, 21, 34, 55, 89, 144])
        cand_L = None
        for shape in ("left", "balanced", "random", "right"):
            c = base.rooted_tree(q - 1, 0, shape)
            if keys(c) == list(range(q)):
                cand_L = c
                t = N(cand_L, q, E)
                for length in [q, 2 * q, 3 * q]:
                    for xs in (list(range(q)) * (length // q + 1),
                               (list(range(q)) + list(range(q)))[:length],
                               base.random_avoiding_seq(0, q, min(length, 200))):
                        xs = [v for v in xs[:length] if v < q]
                        if not xs or not base.avoids231(xs):
                            continue
                        s = reset_lower_sum(t, q, xs)
                        b = bb(t, xs, q)
                        rec(q, s / b, s / len(xs), f"{shape} len={len(xs)}")

    print("  q :  max(reset_lower_sum / boundaryBudget) , (… / length)")
    for q in sorted(worst):
        rbb, rlen, info = worst[q]
        print(f"  {q:>4}:   ratio_bb={rbb:5.2f}   ratio_len={rlen:6.2f}   @ {info}")
    rbbs = [worst[q][0] for q in worst]
    print("\nVERDICT:", "ratio_bb looks BOUNDED -> hlower plausibly TRUE"
          if max(rbbs) < 4 else "ratio grows -> investigate")


if __name__ == "__main__":
    main()
