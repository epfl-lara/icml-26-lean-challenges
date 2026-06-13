from functools import lru_cache
from itertools import product, permutations
import random


E = ()


def N(l, k, r):
    return (l, k, r)


def rotR(t):
    if t and t[0]:
        a, x, b = t[0]
        y = t[1]
        c = t[2]
        return N(a, x, N(b, y, c))
    return t


def rotL(t):
    if t and t[2]:
        a = t[0]
        x = t[1]
        b, y, c = t[2]
        return N(N(a, x, b), y, c)
    return t


def rotate(s, rt):
    if rt == "zigZig":
        return rotR(rotR(s))
    if rt == "zigZag":
        if s:
            return rotR(N(rotL(s[0]), s[1], s[2]))
        return s
    if rt == "zagZag":
        return rotL(rotL(s))
    if rt == "zagZig":
        if s:
            return rotL(N(s[0], s[1], rotR(s[2])))
        return s
    if rt == "zig":
        return rotR(s)
    if rt == "zag":
        return rotL(s)
    raise ValueError(rt)


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


def path(t, q):
    out = []
    while t:
        l, k, r = t
        out.append(k)
        if q < k:
            t = l
        elif k < q:
            t = r
        else:
            break
    return out


def keys(t):
    if not t:
        return []
    return keys(t[0]) + [t[1]] + keys(t[2])


@lru_cache(None)
def shapes(vals):
    vals = tuple(vals)
    if not vals:
        return [E]
    out = []
    for idx, k in enumerate(vals):
        for l in shapes(vals[:idx]):
            for r in shapes(vals[idx + 1 :]):
                out.append(N(l, k, r))
    return out


def avoids231(seq):
    n = len(seq)
    for i in range(n):
        for j in range(i + 1, n):
            if not (seq[i] < seq[j]):
                continue
            for k in range(j + 1, n):
                if seq[k] < seq[i]:
                    return False
    return True


def source_keys(seq, t, done, future):
    touched = {seq[i] for i in done}
    future_paths = set()
    for j in future:
        future_paths.update(path(t, seq[j]))
    return [k for k in keys(t) if k in touched and k in future_paths]


def active_keys(seq, t, xs):
    active = set()
    for j in xs:
        active.update(path(t, seq[j]))
    return [k for k in keys(t) if k in active]


def step_slacks(seq, t):
    cur = t
    worst = -10**9
    worst_data = None
    for p, q in enumerate(seq):
        done = list(range(p))
        future = list(range(p + 1, len(seq)))
        old = source_keys(seq, cur, done, [p] + future)
        newt = splay(cur, q)
        new = source_keys(seq, newt, done + [p], future)
        slack = len(new) + len(path(cur, q)) - len(old)
        if slack > worst:
            worst = slack
            worst_data = (p, q, cur, old, new, path(cur, q))
        cur = newt
    return worst, worst_data


def active_step_slacks(seq, t):
    cur = t
    worst = -10**9
    worst_data = None
    for p, q in enumerate(seq):
        old = active_keys(seq, cur, list(range(p, len(seq))))
        newt = splay(cur, q)
        new = active_keys(seq, newt, list(range(p + 1, len(seq))))
        slack = len(new) + len(path(cur, q)) - len(old)
        if slack > worst:
            worst = slack
            worst_data = (p, q, cur, old, new, path(cur, q))
        cur = newt
    return worst, worst_data


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
    vals = list(vals)
    if not vals:
        return E
    m = len(vals) // 2
    return N(balanced(vals[:m]), vals[m], balanced(vals[m + 1 :]))


def exhaustive(max_n=7):
    for n in range(1, max_n + 1):
        worst = -1
        worst_active = -1
        arg = None
        arg_active = None
        trees = shapes(tuple(range(n)))
        seqs = product(range(n), repeat=n) if n <= 6 else permutations(range(n))
        cnt = 0
        for seq in seqs:
            if not avoids231(seq):
                continue
            cnt += 1
            for t in trees:
                s, data = step_slacks(seq, t)
                if s > worst:
                    worst = s
                    arg = (seq, t, data)
                sa, dataa = active_step_slacks(seq, t)
                if sa > worst_active:
                    worst_active = sa
                    arg_active = (seq, t, dataa)
        print("exhaustive", n, "seqs", cnt, "trees", len(trees),
              "source_worst", worst, "source_arg", arg[:2] if arg else None, "source_step", arg[2][:2] if arg else None,
              "active_worst", worst_active, "active_arg", arg_active[:2] if arg_active else None, "active_step", arg_active[2][:2] if arg_active else None)


def structured(max_n=300):
    patterns = [
        ("inc", lambda n: tuple(range(n))),
        ("dec", lambda n: tuple(reversed(range(n)))),
        ("dup-min", lambda n: tuple([0] * n)),
        ("saw-low", lambda n: tuple((i // 2 if i % 2 == 0 else n - 1 - i // 2) for i in range(n))),
    ]
    trees = [
        ("left", left_spine),
        ("right", right_spine),
        ("bal", lambda n: balanced(range(n))),
    ]
    for n in [10, 20, 50, 100, 200, max_n]:
        for pname, pf in patterns:
            seq = pf(n)
            if not avoids231(seq):
                continue
            for tname, tf in trees:
                s, data = step_slacks(seq, tf(n))
                sa, dataa = active_step_slacks(seq, tf(n))
                print("structured", n, pname, tname, "source_worst", s, "source_step", data[:2], "active_worst", sa, "active_step", dataa[:2])


if __name__ == "__main__":
    exhaustive(6)
    structured()
