from itertools import product, permutations
from functools import lru_cache


E = ()


def N(l, k, r):
    return (l, k, r)


@lru_cache(None)
def gen(lo, n):
    if n == 0:
        return (E,)
    out = []
    for leftn in range(n):
        rightn = n - 1 - leftn
        k = lo + leftn
        for l in gen(lo, leftn):
            for r in gen(k + 1, rightn):
                out.append(N(l, k, r))
    return tuple(out)


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
    if rt == "zigZag":
        return rotR(N(rotL(t[0]), t[1], t[2])) if t else t
    if rt == "zagZig":
        return rotL(N(t[0], t[1], rotR(t[2]))) if t else t
    if rt == "zig":
        return rotR(t)
    if rt == "zag":
        return rotL(t)
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
                return rotate(t, "zig")
            return rotate(N(N(splay(ll, q), lk, lr), k, r), "zigZig")
        if lk < q:
            if not lr:
                return rotate(t, "zig")
            return rotate(N(N(ll, lk, splay(lr, q)), k, r), "zigZag")
        return rotate(t, "zig")
    if not r:
        return t
    rl, rk, rr = r
    if q < rk:
        if not rl:
            return rotate(t, "zag")
        return rotate(N(l, k, N(splay(rl, q), rk, rr)), "zagZig")
    if rk < q:
        if not rr:
            return rotate(t, "zag")
        return rotate(N(l, k, N(rl, rk, splay(rr, q))), "zagZag")
    return rotate(t, "zag")


def path_keys(t, q):
    if not t:
        return []
    l, k, r = t
    if q < k:
        return [k] + path_keys(l, q)
    if k < q:
        return [k] + path_keys(r, q)
    return [k]


def path_len(t, q):
    return len(path_keys(t, q))


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


def source_potential(seq, t, done, future):
    touched = {seq[i] for i in done}
    future_paths = set()
    for j in future:
        future_paths.update(path_keys(t, seq[j]))
    return 2 * len(touched & future_paths)


def check_seq_tree(seq, init, limit=6):
    t = init
    n = len(seq)
    worst = -10**9
    worst_data = None
    done = []
    for i in range(n):
        future = list(range(i + 1, n))
        before = source_potential(seq, t, done, [i] + future)
        after_t = splay(t, seq[i])
        after = source_potential(seq, after_t, done + [i], future)
        step = path_len(t, seq[i]) + after - before
        if step > worst:
            worst = step
            worst_data = (i, t, before, after, path_len(t, seq[i]), step)
        if step > limit:
            return False, worst, worst_data
        t = after_t
        done.append(i)
    return True, worst, worst_data


def run(max_n=7, functions_up_to=6, limit=6):
    for n in range(1, max_n + 1):
        trees = gen(0, n)
        if n <= functions_up_to:
            seqs = (seq for seq in product(range(n), repeat=n) if avoids231(seq))
            mode = "functions"
        else:
            seqs = (seq for seq in permutations(range(n)) if avoids231(seq))
            mode = "permutations"
        count = 0
        worst = -10**9
        worst_arg = None
        for seq in seqs:
            count += 1
            for t in trees:
                ok, w, data = check_seq_tree(seq, t, limit)
                if w > worst:
                    worst = w
                    worst_arg = (seq, t, data)
                if not ok:
                    print("FAIL", n, mode, "seq", seq, "tree", t, "data", data)
                    return
        print("n", n, mode, "seqs", count, "trees", len(trees), "worst", worst, "arg", worst_arg[0] if worst_arg else None)


if __name__ == "__main__":
    run()
