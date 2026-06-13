"""Decisive test for the hlower reroute via the induction hypothesis.

reset_lower_sum(t,q,xs) = len(xs) + sum_k spl(leftsub(r_k), x_k)   [q pinned at root]
where leftsub(r_k) is the left subtree of the reset tree after k steps.

Let modified_sum = sum_k spl(leftsub(r_k), x_k).
Let plain_sum    = splayPathSum(L, xs)  (plain splaying inside L = t's left subtree).

QUESTION: is  modified_sum <= plain_sum + C * len(xs)  for a small CONSTANT C
(equivalently (modified_sum - plain_sum)/len bounded as q grows)?

If yes -> reset_lower_sum <= splayPathSum(L,xs) + (C+1)*len, and since L is a
strictly smaller instance, hlower follows from the IH:  splayPathSum(L,xs) <=
K*boundaryBudget(L,xs)  =>  hlower with constant.  We report worst (diff/len).
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


def diffs(L, q, xs):
    r = N(L, q, E)
    modified = 0.0
    for x in xs:
        modified += spl(r[0], x)          # left subtree of current reset tree
        r = splay(splay(r, x), q)
    l = L
    plain = 0.0
    for x in xs:
        plain += spl(l, x)
        l = splay(l, x)
    return modified, plain


def main():
    random.seed(5)
    deadline = time.time() + 110
    worst = {}

    def rec(q, dperlen, info):
        cur = worst.get(q)
        if cur is None or dperlen > cur[0]:
            worst[q] = (dperlen, info)

    for q in range(1, 7):
        for L in base.trees(0, q):
            for length in range(1, 7):
                for xs in product(range(q), repeat=length):
                    if not base.avoids231(list(xs)):
                        continue
                    xs = list(xs)
                    m, p = diffs(L, q, xs)
                    rec(q, (m - p) / len(xs), f"exh seq={xs} mod={m} plain={p}")
        if time.time() > deadline:
            break

    while time.time() < deadline:
        q = random.choice([8, 13, 21, 34, 55, 89, 144])
        L = None
        for shape in ("left", "balanced", "random", "right"):
            c = base.rooted_tree(q - 1, 0, shape)
            if keys(c) == list(range(q)):
                L = c
                for length in [q, 2 * q]:
                    for xs in (list(range(q)) * (length // max(q, 1) + 1),
                               list(reversed(range(q))) * (length // max(q, 1) + 1),
                               base.random_avoiding_seq(0, q, min(length, 200))):
                        xs = [v for v in xs[:length] if v < q]
                        if not xs or not base.avoids231(xs):
                            continue
                        m, p = diffs(L, q, xs)
                        rec(q, (m - p) / len(xs), f"{shape} len={len(xs)}")

    print("  q :  max( (modified_sum - plain_sum) / len )   [bounded => hlower via IH works]")
    for q in sorted(worst):
        d, info = worst[q]
        print(f"  {q:>4}:   {d:+6.2f}   @ {info}")
    mx = max(worst[q][0] for q in worst)
    print("\nVERDICT:", "diff/len BOUNDED -> reset_lower <= plain + O(len); hlower from IH"
          if mx < 5 else "diff/len GROWS -> modified process costlier than plain; need other route")


if __name__ == "__main__":
    main()
