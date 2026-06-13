from __future__ import annotations

from functools import lru_cache
from itertools import product
import random

E = ()


def N(l, k, r):
    return (l, k, r)


def num(t):
    return 0 if t == E else 1 + num(t[0]) + num(t[2])


def inorder(t):
    return [] if t == E else inorder(t[0]) + [t[1]] + inorder(t[2])


@lru_cache(None)
def trees(lo, n):
    if n == 0:
        return (E,)
    out = []
    for left_n in range(n):
        k = lo + left_n
        right_n = n - 1 - left_n
        for l in trees(lo, left_n):
            for r in trees(k + 1, right_n):
                out.append(N(l, k, r))
    return tuple(out)


def rotate_right(t):
    if t and t[0]:
        a, x, b = t[0]
        y, c = t[1], t[2]
        return N(a, x, N(b, y, c))
    return t


def rotate_left(t):
    if t and t[2]:
        a, x = t[0], t[1]
        b, y, c = t[2]
        return N(N(a, x, b), y, c)
    return t


def rotate(t, kind):
    if kind == "zigZig":
        return rotate_right(rotate_right(t))
    if kind == "zagZag":
        return rotate_left(rotate_left(t))
    if kind == "zig":
        return rotate_right(t)
    if kind == "zag":
        return rotate_left(t)
    if kind == "zigZag":
        if t:
            l, k, r = t
            return rotate_right(N(rotate_left(l), k, r))
        return t
    if kind == "zagZig":
        if t:
            l, k, r = t
            return rotate_left(N(l, k, rotate_right(r)))
        return t
    raise ValueError(kind)


def splay(t, q):
    if not t:
        return E
    l, k, r = t
    if q == k:
        return t
    if q < k:
        if not l:
            return t
        ll, lk, lr = l
        if q < lk:
            if not ll:
                return rotate(N(l, k, r), "zig")
            return rotate(N(N(splay(ll, q), lk, lr), k, r), "zigZig")
        if lk < q:
            if not lr:
                return rotate(N(l, k, r), "zig")
            return rotate(N(N(ll, lk, splay(lr, q)), k, r), "zigZag")
        return rotate(t, "zig")
    if not r:
        return t
    rl, rk, rr = r
    if q < rk:
        if not rl:
            return rotate(N(l, k, r), "zag")
        return rotate(N(l, k, N(splay(rl, q), rk, rr)), "zagZig")
    if rk < q:
        if not rr:
            return rotate(N(l, k, r), "zag")
        return rotate(N(l, k, N(rl, rk, splay(rr, q))), "zagZag")
    return rotate(t, "zag")


def cost(t, q):
    if not t:
        return 0
    l, k, r = t
    if q == k:
        return 0
    if q < k:
        if not l:
            return 0
        ll, lk, lr = l
        if q < lk:
            return 1 if not ll else cost(ll, q) + 2
        if lk < q:
            return 1 if not lr else cost(lr, q) + 2
        return 1
    if not r:
        return 0
    rl, rk, rr = r
    if q < rk:
        return 1 if not rl else cost(rl, q) + 2
    if rk < q:
        return 1 if not rr else cost(rr, q) + 2
    return 1


def seq_cost(t, seq):
    total = 0
    for q in seq:
        total += cost(t, q)
        t = splay(t, q)
    return total


def contains_strict_pattern(seq, pat):
    # Matches Lean's definition: all pairwise strict comparisons agree.
    m = len(pat)
    n = len(seq)

    def rec(start, chosen):
        if len(chosen) == m:
            vals = [seq[i] for i in chosen]
            return all((pat[a] < pat[b]) == (vals[a] < vals[b])
                       for a in range(m) for b in range(m))
        for i in range(start, n):
            if rec(i + 1, chosen + [i]):
                return True
        return False

    return rec(0, [])


def avoids_231(seq):
    return not contains_strict_pattern(seq, (2, 3, 1))


def right_spine(n):
    t = E
    for k in reversed(range(n)):
        t = N(E, k, t)
    return t


def left_spine(n):
    t = E
    for k in range(n):
        t = N(t, k, E)
    return t


def balanced(vals):
    if not vals:
        return E
    mid = len(vals) // 2
    return N(balanced(vals[:mid]), vals[mid], balanced(vals[mid + 1:]))


@lru_cache(None)
def avoiding_functions(n):
    return tuple(seq for seq in product(range(n), repeat=n) if avoids_231(seq))


def random_avoiding_perm(vals):
    vals = list(vals)
    if not vals:
        return []
    # Catalan decomposition for 231-avoiding permutations:
    # choose max, left block contains smaller prefix of values, right block larger suffix.
    maxv = vals[-1]
    rest = vals[:-1]
    split = random.randrange(len(rest) + 1)
    return (
        random_avoiding_perm(rest[:split])
        + [maxv]
        + random_avoiding_perm(rest[split:])
    )


def audit_satisfiable_examples():
    examples = [
        (1, (0,), N(E, 0, E)),
        (2, (1, 0), N(E, 0, N(E, 1, E))),
        (3, (2, 0, 2), N(N(E, 0, E), 1, N(E, 2, E))),
    ]
    for n, seq, t in examples:
        assert num(t) == n
        assert inorder(t) == list(range(n))
        assert all(q in inorder(t) for q in seq)
        assert avoids_231(seq)
        print("satisfiable", n, seq, "cost", seq_cost(t, seq))


def exhaustive_functions(max_n):
    for n in range(1, max_n + 1):
        seqs = avoiding_functions(n)
        ts = trees(0, n)
        best = (-1, None, None)
        for seq in seqs:
            for t in ts:
                c = seq_cost(t, seq)
                if c > best[0]:
                    best = (c, seq, t)
        print(
            "all-functions",
            "n", n,
            "avoid", len(seqs),
            "trees", len(ts),
            "max", best[0],
            "ratio", best[0] / n,
            "seq", best[1],
        )


def structured_search(max_n, samples):
    families = [
        ("right", right_spine),
        ("left", left_spine),
        ("balanced", lambda n: balanced(list(range(n)))),
    ]
    for n in range(2, max_n + 1):
        candidates = [
            tuple(n - 1 if i % 2 == 0 else 0 for i in range(n)),
            tuple(0 if i % 2 == 0 else n - 1 for i in range(n)),
            tuple(random_avoiding_perm(range(n))),
        ]
        for _ in range(samples):
            candidates.append(tuple(random_avoiding_perm(range(n))))
        for name, make_tree in families:
            best = (-1, None)
            for seq in candidates:
                if not avoids_231(seq):
                    continue
                c = seq_cost(make_tree(n), seq)
                if c > best[0]:
                    best = (c, seq)
            print("structured", "n", n, name, "max", best[0], "ratio", best[0] / n, "seq", best[1])


if __name__ == "__main__":
    random.seed(20260602)
    audit_satisfiable_examples()
    exhaustive_functions(6)
    structured_search(80, 200)
