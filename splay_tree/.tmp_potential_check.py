from __future__ import annotations

from functools import lru_cache
from itertools import combinations, product
import random
import sys


class T:
    __slots__ = ("l", "k", "r")

    def __init__(self, l: "T | None", k: int, r: "T | None") -> None:
        self.l = l
        self.k = k
        self.r = r


def tup(t: T | None):
    return None if t is None else (tup(t.l), t.k, tup(t.r))


def rotR(t: T | None) -> T | None:
    if t is not None and t.l is not None:
        return T(t.l.l, t.l.k, T(t.l.r, t.k, t.r))
    return t


def rotL(t: T | None) -> T | None:
    if t is not None and t.r is not None:
        return T(T(t.l, t.k, t.r.l), t.r.k, t.r.r)
    return t


def rotate(t: T | None, rt: str) -> T | None:
    if rt == "zigZig":
        return rotR(rotR(t))
    if rt == "zagZag":
        return rotL(rotL(t))
    if rt == "zig":
        return rotR(t)
    if rt == "zag":
        return rotL(t)
    if rt == "zigZag":
        return rotR(T(rotL(t.l), t.k, t.r)) if t is not None else t
    if rt == "zagZig":
        return rotL(T(t.l, t.k, rotR(t.r))) if t is not None else t
    raise ValueError(rt)


def splay(t: T | None, q: int) -> T | None:
    if t is None:
        return None
    l, k, r = t.l, t.k, t.r
    if q == k:
        return t
    if q < k:
        if l is None:
            return t
        ll, lk, lr = l.l, l.k, l.r
        if q < lk:
            if ll is None:
                return rotate(T(l, k, r), "zig")
            return rotate(T(T(splay(ll, q), lk, lr), k, r), "zigZig")
        if lk < q:
            if lr is None:
                return rotate(T(l, k, r), "zig")
            return rotate(T(T(ll, lk, splay(lr, q)), k, r), "zigZag")
        return rotate(t, "zig")
    if r is None:
        return t
    rl, rk, rr = r.l, r.k, r.r
    if q < rk:
        if rl is None:
            return rotate(T(l, k, r), "zag")
        return rotate(T(l, k, T(splay(rl, q), rk, rr)), "zagZig")
    if rk < q:
        if rr is None:
            return rotate(T(l, k, r), "zag")
        return rotate(T(l, k, T(rl, rk, splay(rr, q))), "zagZag")
    return rotate(t, "zag")


def path(t: T | None, q: int) -> list[int]:
    if t is None:
        return []
    if q == t.k:
        return [t.k]
    if q < t.k:
        return [t.k] + path(t.l, q) if t.l is not None else [t.k]
    return [t.k] + path(t.r, q) if t.r is not None else [t.k]


def left_edges(t: T | None) -> int:
    if t is None:
        return 0
    return left_edges(t.r) if t.l is None else 1 + left_edges(t.l) + left_edges(t.r)


def right_edges(t: T | None) -> int:
    if t is None:
        return 0
    return right_edges(t.l) if t.r is None else 1 + right_edges(t.l) + right_edges(t.r)


def strong(t: T | None) -> int:
    return 10 * left_edges(t) + 5 * right_edges(t)


def revstrong(t: T | None) -> int:
    return 10 * right_edges(t) + 5 * left_edges(t)


def active_budget(X: tuple[int, ...], t: T | None, idxs: list[int]) -> int:
    keys = set()
    for i in idxs:
        keys.update(path(t, X[i]))
    return len(idxs) + len(keys)


def avoids231(X: tuple[int, ...]) -> bool:
    for i, j, k in combinations(range(len(X)), 3):
        if X[k] < X[i] < X[j]:
            return False
    return True


@lru_cache(None)
def shapes(keys: tuple[int, ...]) -> tuple[T | None, ...]:
    if not keys:
        return (None,)
    out = []
    for p, k in enumerate(keys):
        for l in shapes(keys[:p]):
            for r in shapes(keys[p + 1 :]):
                out.append(T(l, k, r))
    return tuple(out)


def left_spine(n: int) -> T | None:
    t = None
    for k in range(n):
        t = T(t, k, None)
    return t


def right_spine(n: int) -> T | None:
    t = None
    for k in reversed(range(n)):
        t = T(None, k, t)
    return t


def balanced(lo: int, hi: int) -> T | None:
    if lo >= hi:
        return None
    mid = (lo + hi) // 2
    return T(balanced(lo, mid), mid, balanced(mid + 1, hi))


def step_worst(X: tuple[int, ...], t: T | None, beta: int, gamma: int, delta: int, C: int):
    cur = t
    worst = (-10**9, None)
    for p in range(len(X)):
        future = list(range(p + 1, len(X)))
        after = splay(cur, X[p])
        lhs = (
            len(path(cur, X[p]))
            + beta * strong(after)
            + gamma * revstrong(after)
            + delta * active_budget(X, after, future)
        )
        rhs = (
            C
            + beta * strong(cur)
            + gamma * revstrong(cur)
            + delta * active_budget(X, cur, [p] + future)
        )
        gap = lhs - rhs
        if gap > worst[0]:
            worst = (gap, (p, tup(cur), tup(after), lhs, rhs))
        cur = after
    return worst


def exhaustive(n: int, coeffs: tuple[int, int, int, int]):
    beta, gamma, delta, C = coeffs
    worst = (-10**9, None, None)
    count = 0
    for X in product(range(n), repeat=n):
        if not avoids231(X):
            continue
        count += 1
        for t in shapes(tuple(range(n))):
            gap, info = step_worst(X, t, beta, gamma, delta, C)
            if gap > worst[0]:
                worst = (gap, X, info)
            if gap > 0:
                return False, count, worst, (X, tup(t), gap, info)
    return True, count, worst, None


def random_avoiding(n: int) -> tuple[int, ...]:
    # Monotone samples are a high-signal stress family for the first-step spine case.
    if random.random() < 0.6:
        return tuple(sorted(random.randrange(n) for _ in range(n)))
    while True:
        X = tuple(random.randrange(n) for _ in range(n))
        if avoids231(X):
            return X


def random_stress(n: int, coeffs: tuple[int, int, int, int], tries: int):
    beta, gamma, delta, C = coeffs
    pools = [left_spine(n), right_spine(n), balanced(0, n)]
    worst = (-10**9, None, None)
    for _ in range(tries):
        X = random_avoiding(n)
        for t in pools:
            gap, info = step_worst(X, t, beta, gamma, delta, C)
            if gap > worst[0]:
                worst = (gap, X, info)
            if gap > 0:
                return False, worst, (X, tup(t), gap, info)
    return True, worst, None


def main() -> int:
    coeffs = tuple(map(int, sys.argv[1].split(","))) if len(sys.argv) > 1 else (2, 1, 3, 8)
    max_n = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    tries = int(sys.argv[3]) if len(sys.argv) > 3 else 5000
    print("COEFF", coeffs, flush=True)
    for n in range(1, max_n + 1):
        ok, count, worst, bad = exhaustive(n, coeffs)
        print(" exhaustive", n, "ok", ok, "seqs", count, "worst", worst[0], flush=True)
        if not ok:
            print(" BAD", bad, flush=True)
            return 1
    for n in [8, 10, 12, 16, 24]:
        ok, worst, bad = random_stress(n, coeffs, tries)
        print(" random", n, "ok", ok, "worst", worst[0], flush=True)
        if not ok:
            print(" BAD", bad, flush=True)
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
