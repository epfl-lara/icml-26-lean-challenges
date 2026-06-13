from __future__ import annotations

from functools import lru_cache
from itertools import product
import argparse
import random
import time

E = ()


def N(l, k, r):
    return (l, k, r)


def keys(t):
    return [] if t == E else keys(t[0]) + [t[1]] + keys(t[2])


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


def balanced(vals):
    vals = list(vals)
    if not vals:
        return E
    mid = len(vals) // 2
    return N(balanced(vals[:mid]), vals[mid], balanced(vals[mid + 1:]))


def left_spine(vals):
    t = E
    for k in vals:
        t = N(t, k, E)
    return t


def right_spine(vals):
    t = E
    for k in reversed(list(vals)):
        t = N(E, k, t)
    return t


def random_tree(vals):
    vals = list(vals)
    if not vals:
        return E
    i = random.randrange(len(vals))
    return N(random_tree(vals[:i]), vals[i], random_tree(vals[i + 1:]))


def rooted_tree(q, right_n, shape):
    left_vals = list(range(q))
    right_vals = list(range(q + 1, q + 1 + right_n))
    if shape == "balanced":
        return N(balanced(left_vals), q, balanced(right_vals))
    if shape == "left":
        return N(left_spine(left_vals), q, left_spine(right_vals))
    if shape == "right":
        return N(right_spine(left_vals), q, right_spine(right_vals))
    if shape == "random":
        return N(random_tree(left_vals), q, random_tree(right_vals))
    raise ValueError(shape)


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


def contains_strict_pattern(seq, pat):
    n = len(seq)
    m = len(pat)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                vals = (seq[i], seq[j], seq[k])
                ok = True
                for a in range(m):
                    for b in range(m):
                        if (pat[a] < pat[b]) != (vals[a] < vals[b]):
                            ok = False
                            break
                    if not ok:
                        break
                if ok:
                    return True
    return False


def avoids231(seq):
    if len(seq) < 3:
        return True
    maxv = max(seq)
    minv = min(seq)
    if minv < 0:
        return not contains_strict_pattern(seq, (2, 3, 1))
    suffix_min = [0] * len(seq)
    suffix_min[-1] = seq[-1]
    for i in range(len(seq) - 2, -1, -1):
        suffix_min[i] = min(seq[i], suffix_min[i + 1])
    prefix_counts = [0] * (maxv + 1)
    prefix_counts[seq[0]] += 1
    for j in range(1, len(seq) - 1):
        lo = suffix_min[j + 1] + 1
        hi = seq[j]
        if lo < hi:
            for a in range(lo, hi):
                if prefix_counts[a]:
                    return False
        prefix_counts[seq[j]] += 1
    return True


def pivot_reset_pair(t, seq, q):
    total = 0
    for x in seq:
        total += path_len(t, x)
        tx = splay(t, x)
        total += path_len(tx, q)
        t = splay(tx, q)
    return total


def with_final(t, seq, q):
    total = 0
    for x in seq:
        total += path_len(t, x)
        t = splay(t, x)
    total += path_len(t, q)
    return total


def boundary_budget(t, seq, q):
    hull = set(search_path_keys(t, q))
    for x in seq:
        hull.update(search_path_keys(t, x))
    return len(seq) + len(hull)


def seq_summary(seq):
    seq = tuple(seq)
    prefix = seq[:12]
    suffix = seq[-12:] if len(seq) > 12 else ()
    return {
        "len": len(seq),
        "distinct": tuple(sorted(set(seq))),
        "prefix": prefix,
        "suffix": suffix,
    }


def random_avoiding_seq(lo, hi, length):
    if length <= 0:
        return []
    if hi <= lo:
        return [lo] * length
    left_len = random.randrange(length)
    right_len = length - 1 - left_len
    split = random.randrange(lo, hi)
    return (
        random_avoiding_seq(lo, split, left_len)
        + [hi]
        + random_avoiding_seq(split, hi, right_len)
    )


def record(best, label, q, right_n, shape, seq, t, max_final, max_budget):
    pair = pivot_reset_pair(t, seq, q)
    final = with_final(t, seq, q)
    budget = boundary_budget(t, seq, q)
    if final == 0 or budget == 0:
        raise AssertionError("zero denominator")
    rf = pair / final
    rb = pair / budget
    if rf > best["final"][0]:
        best["final"] = (rf, pair, final, label, q, right_n, shape, seq_summary(seq))
    if rb > best["budget"][0]:
        best["budget"] = (rb, pair, budget, label, q, right_n, shape, seq_summary(seq))
    if pair > max_final * final:
        print(
            f"COUNTER pair<={max_final}*final",
            pair,
            final,
            label,
            q,
            right_n,
            shape,
            seq_summary(seq),
            flush=True,
        )
        raise SystemExit(2)
    if pair > max_budget * budget:
        print(
            f"COUNTER pair<={max_budget}*budget",
            pair,
            budget,
            label,
            q,
            right_n,
            shape,
            seq_summary(seq),
            flush=True,
        )
        raise SystemExit(3)


def exhaustive_small(best, deadline, max_final, max_budget):
    cases = 0
    for total_n in range(2, 9):
        for q in range(1, total_n):
            rooted = []
            for l in trees(0, q):
                for r in trees(q + 1, total_n - q - 1):
                    rooted.append(N(l, q, r))
            max_len = min(7, q + 3)
            for length in range(max_len + 1):
                for seq in product(range(q), repeat=length):
                    if time.time() > deadline:
                        return cases
                    if not avoids231(seq):
                        continue
                    for idx, t in enumerate(rooted):
                        record(
                            best,
                            "exhaustive",
                            q,
                            total_n - q - 1,
                            f"rooted#{idx}",
                            seq,
                            t,
                            max_final,
                            max_budget,
                        )
                        cases += 1
        print("exhaustive-total-n", total_n, "cases", cases, "best", best, flush=True)
    return cases


def structured_random(best, deadline, max_final, max_budget):
    cases = 0
    shapes = ("balanced", "left", "right", "random")
    while time.time() < deadline:
        q = random.choice([2, 3, 4, 5, 8, 13, 21, 34, 55, 89, 144, 233])
        right_n = random.choice([0, 1, q // 3, q, 2 * q])
        length = random.choice([0, 1, 2, 3, 5, 8, 13, 25, 50, 100, 250, 1000, 5000])
        shape = random.choice(shapes)
        t = rooted_tree(q, right_n, shape)
        candidates = []
        if length:
            candidates.append([q - 1 if i % 2 == 0 else 0 for i in range(length)])
            candidates.append([0 if i % 2 == 0 else q - 1 for i in range(length)])
            mid = q // 2
            candidates.append([mid if i % 2 == 0 else 0 for i in range(length)])
            candidates.append(random_avoiding_seq(0, q - 1, length))
        else:
            candidates.append([])
        for seq in candidates:
            if not avoids231(seq):
                print("bad-generator", q, seq[:20], flush=True)
                raise SystemExit(4)
            record(best, "structured", q, right_n, shape, seq, t, max_final, max_budget)
            cases += 1
        if cases % 1000 == 0:
            print("random-cases", cases, "best", best, flush=True)
    return cases


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=180.0)
    parser.add_argument("--seed", type=int, default=20260602)
    parser.add_argument("--max-final", type=float, default=16.0)
    parser.add_argument("--max-budget", type=float, default=16.0)
    parser.add_argument(
        "--mode",
        choices=("all", "exhaustive", "random"),
        default="all",
    )
    args = parser.parse_args()
    random.seed(args.seed)
    deadline = time.time() + args.seconds
    best = {"final": (0.0, None), "budget": (0.0, None)}
    exhaustive_cases = 0
    random_cases = 0
    if args.mode in ("all", "exhaustive"):
        exhaustive_cases = exhaustive_small(
            best, deadline, args.max_final, args.max_budget
        )
    if args.mode in ("all", "random") and time.time() < deadline:
        random_cases = structured_random(
            best, deadline, args.max_final, args.max_budget
        )
    print("DONE", "exhaustive", exhaustive_cases, "random", random_cases, "best", best, flush=True)


if __name__ == "__main__":
    main()
