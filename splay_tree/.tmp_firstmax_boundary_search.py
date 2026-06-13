from functools import lru_cache
from itertools import product, permutations
import random

E = ()


def N(l, k, r):
    return (l, k, r)


def trees(vals):
    vals = tuple(vals)
    if not vals:
        yield E
        return
    for i, k in enumerate(vals):
        for l in trees(vals[:i]):
            for r in trees(vals[i + 1 :]):
                yield N(l, k, r)


def to_keys(t):
    if not t:
        return []
    l, k, r = t
    return to_keys(l) + [k] + to_keys(r)


def search_path_keys(t, q):
    if not t:
        return []
    l, k, r = t
    if q < k:
        return [k] + search_path_keys(l, q)
    if k < q:
        return [k] + search_path_keys(r, q)
    return [k]


def path_len(t, q):
    return len(search_path_keys(t, q))


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


def rotate(t, rt):
    if rt == "zigZig":
        return rotR(rotR(t))
    if rt == "zagZag":
        return rotL(rotL(t))
    if rt == "zig":
        return rotR(t)
    if rt == "zag":
        return rotL(t)
    if rt == "zigZag":
        if not t:
            return t
        l, k, r = t
        return rotR(N(rotL(l), k, r))
    if rt == "zagZig":
        if not t:
            return t
        l, k, r = t
        return rotL(N(l, k, rotR(r)))
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


def path_sum(t, seq):
    total = 0
    for q in seq:
        total += path_len(t, q)
        t = splay(t, q)
    return total


def avoids231(seq):
    n = len(seq)
    for i in range(n):
        for j in range(i + 1, n):
            if not seq[i] < seq[j]:
                continue
            for k in range(j + 1, n):
                if seq[k] < seq[i]:
                    return False
    return True


def first_max_index(seq):
    m = max(seq)
    return next(i for i, x in enumerate(seq) if x == m)


def boundary_budget(t, seq, q):
    keys = set(search_path_keys(t, q))
    for x in seq:
        keys.update(search_path_keys(t, x))
    return len(seq) + len(keys)


def run(max_n=7):
    for n in range(1, max_n + 1):
        all_trees = list(trees(range(n)))
        if n <= 6:
            seqs = product(range(n), repeat=n)
            seq_kind = "functions"
        else:
            seqs = permutations(range(n))
            seq_kind = "permutations"
        cnt = 0
        worst = -1.0
        worst_data = None
        for seq in seqs:
            if not avoids231(seq):
                continue
            cnt += 1
            m = first_max_index(seq)
            q = seq[m]
            for t in all_trees:
                ps = path_sum(t, seq)
                bb = boundary_budget(t, seq, q)
                ratio = ps / bb if bb else 0.0
                if ratio > worst:
                    worst = ratio
                    worst_data = (seq, m, q, t, ps, bb)
        print(
            "n",
            n,
            "trees",
            len(all_trees),
            seq_kind,
            "avoid",
            cnt,
            "worst",
            worst,
            "data",
            worst_data,
            flush=True,
        )


def left_spine(n):
    t = E
    for k in range(n):
        t = N(t, k, E)
    return t


def right_spine(n):
    t = E
    for k in reversed(range(n)):
        t = N(E, k, t)
    return t


def balanced(vals):
    vals = tuple(vals)
    if not vals:
        return E
    m = len(vals) // 2
    return N(balanced(vals[:m]), vals[m], balanced(vals[m + 1 :]))


def random_bst(vals):
    vals = tuple(vals)
    if not vals:
        return E
    k = random.choice(vals)
    i = vals.index(k)
    return N(random_bst(vals[:i]), k, random_bst(vals[i + 1 :]))


def random_avoiding_perm(vals):
    vals = tuple(vals)
    if not vals:
        return ()
    q = vals[-1]
    cut = random.randrange(len(vals))
    left = vals[:cut]
    right = vals[cut:-1]
    return random_avoiding_perm(left) + (q,) + random_avoiding_perm(right)


def random_avoiding_func(length, values):
    values = tuple(values)
    if length == 0:
        return ()
    if len(values) == 1:
        return (values[0],) * length
    q_index = random.randrange(len(values))
    q = values[q_index]
    low_values = values[: q_index + 1]
    high_values = values[q_index:]
    m = random.randrange(length)
    return (
        random_avoiding_func(m, low_values)
        + (q,)
        + random_avoiding_func(length - m - 1, high_values)
    )


def run_random(samples=20000):
    random.seed(0)
    for n in [8, 10, 12, 16, 24, 32, 50, 80, 120, 200]:
        shapes = [
            ("left", left_spine(n)),
            ("right", right_spine(n)),
            ("balanced", balanced(range(n))),
        ]
        for r in range(5):
            shapes.append((f"random{r}", random_bst(tuple(range(n)))))
        worst = -1.0
        worst_data = None
        for s in range(samples):
            if s % 2 == 0:
                seq = random_avoiding_perm(tuple(range(n)))
            else:
                seq = random_avoiding_func(n, tuple(range(n)))
            if not avoids231(seq):
                raise AssertionError(seq)
            m = first_max_index(seq)
            q = seq[m]
            for name, t in shapes:
                ps = path_sum(t, seq)
                bb = boundary_budget(t, seq, q)
                ratio = ps / bb if bb else 0.0
                if ratio > worst:
                    worst = ratio
                    worst_data = (name, seq[:20], m, q, ps, bb)
        print("random n", n, "samples", samples, "worst", worst, "data", worst_data, flush=True)


if __name__ == "__main__":
    run()
    run_random()
