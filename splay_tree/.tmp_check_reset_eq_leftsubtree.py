"""Linchpin check for the proposed hlower reroute:

Claim: for t = node(L, q, R) (BST, q at root) and accesses x < q,
the suffix-reset process keeps q at the root and evolves its LEFT subtree
*exactly* as plain splaying inside L. Concretely, with
  r_0 = t,  r_{k+1} = splay(splay(r_k, x_k), q),
we claim  r_k = node(L_k, q, R)  where  L_0 = L, L_{k+1} = splay(L_k, x_k),
and hence  search_path_len(r_k, x_k) = 1 + search_path_len(L_k, x_k).

If true, pivotResetLowerPathSum(t, xs) = len(xs) + splayPathSum(L, xs),
so hlower follows from the IH applied to L (strictly smaller). We test:
  (1) structural identity r_k == node(L_k, q, R)   [exact tree equality]
  (2) per-step path identity spl(r_k,x_k) == 1 + spl(L_k,x_k)
and report worst-case violation (0 == perfect).
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


def check_seq(L, q, R, xs):
    """Return (struct_ok, path_ok)."""
    r = N(L, q, R)
    Lk = L
    struct_ok = path_ok = True
    for x in xs:
        if spl(r, x) != 1 + spl(Lk, x):
            path_ok = False
        r2 = splay(splay(r, x), q)
        Lk2 = splay(Lk, x)
        if r2 != N(Lk2, q, R):
            struct_ok = False
        r, Lk = r2, Lk2
    return struct_ok, path_ok


def main():
    random.seed(1)
    deadline = time.time() + 90
    bad_struct = bad_path = 0
    total = 0
    # exhaustive: q up to 6, R empty and small, xs length up to 6
    for q in range(1, 7):
        Ls = list(base.trees(0, q))            # BSTs on {0..q-1}
        Rs = [E] + list(base.trees(q + 1, 1)) + list(base.trees(q + 1, 2))
        for L in Ls:
            for R in Rs:
                for length in range(1, 7):
                    for xs in product(range(q), repeat=length):
                        if not base.avoids231(list(xs)):
                            continue
                        s, p = check_seq(L, q, R, list(xs))
                        total += 1
                        bad_struct += (not s)
                        bad_path += (not p)
                        if time.time() > deadline:
                            print(f"[partial] total={total} bad_struct={bad_struct} bad_path={bad_path}")
                            return
    # structured large q
    while time.time() < deadline:
        q = random.choice([8, 13, 21, 34, 55, 89])
        L = base.rooted_tree(q - 1, 0, random.choice(("left", "balanced", "random", "right"))) if q >= 2 else E
        # rooted_tree builds keys 0..(q-1) when given (q-1,0)? guard with keys check
        if keys(L) != list(range(q)):
            # fall back to a guaranteed BST on 0..q-1
            L = None
            for cand in [base.rooted_tree(q - 1, 0, "left"),
                         base.rooted_tree(q - 1, 0, "balanced")]:
                if keys(cand) == list(range(q)):
                    L = cand; break
            if L is None:
                continue
        R = E
        length = random.choice([5, 8, 13, 21, 34])
        for xs in ([0] * length, list(range(min(length, q))),
                   list(range(min(length, q) - 1, -1, -1)),
                   base.random_avoiding_seq(0, q, length)):
            xs = [v for v in xs if v < q]
            if not xs or not base.avoids231(xs):
                continue
            s, p = check_seq(L, q, R, xs)
            total += 1
            bad_struct += (not s); bad_path += (not p)

    print(f"total={total}  bad_struct={bad_struct}  bad_path={bad_path}")
    print("VERDICT:", "reset == plain splay in left subtree (EXACT)"
          if bad_struct == 0 and bad_path == 0 else "NOT exact — reroute needs care")


if __name__ == "__main__":
    main()
