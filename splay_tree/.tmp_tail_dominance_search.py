from __future__ import annotations

import argparse
import importlib.util
import random
import time
from itertools import product
from pathlib import Path


BASE_PATH = Path(__file__).with_name(".tmp_pair_certificate_search.py")
SPEC = importlib.util.spec_from_file_location("splay_search_base", BASE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"could not load {BASE_PATH}")
base = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(base)


def splay_path_sum(t, seq):
    total = 0
    for x in seq:
        total += base.path_len(t, x)
        t = base.splay(t, x)
    return total


def suffix_reset_upper(t, seq, q):
    total = 0
    for x in seq:
        if x < q:
            total += base.path_len(t, x)
            tx = base.splay(t, x)
            total += base.path_len(tx, q)
            t = base.splay(tx, q)
        else:
            total += 1
    return total


def record(best, label, q, right_n, shape, x, xs, t, args):
    tx = base.splay(t, x)
    tr = base.splay(tx, q)
    lhs = splay_path_sum(tx, xs)
    reset = suffix_reset_upper(tr, xs, q)
    path_q = base.path_len(tx, q)
    rhs = path_q + reset + args.d * len(xs)
    gap = lhs - rhs
    payload = {
        "gap": gap,
        "lhs": lhs,
        "path_q": path_q,
        "reset": reset,
        "len": len(xs),
        "label": label,
        "q": q,
        "x": x,
        "right_n": right_n,
        "shape": shape,
        "xs": base.seq_summary(xs),
    }
    if gap > best["gap"][0]:
        best["gap"] = (gap, payload)
    if lhs > rhs:
        print("COUNTER tail-dominance", "D", args.d, payload, flush=True)
        raise SystemExit(2)


def exhaustive(best, deadline, args):
    cases = 0
    for total_n in range(2, args.exhaustive_total_n + 1):
        for q in range(1, total_n):
            rooted = []
            for l in base.trees(0, q):
                for r in base.trees(q + 1, total_n - q - 1):
                    rooted.append(base.N(l, q, r))
            max_len = min(args.exhaustive_len, q + args.exhaustive_extra)
            for x in range(q):
                for length in range(max_len + 1):
                    for xs in product(range(q + 1), repeat=length):
                        if time.time() > deadline:
                            return cases
                        if args.avoid and not base.avoids231((x,) + xs):
                            continue
                        for idx, t in enumerate(rooted):
                            record(
                                best,
                                "exhaustive",
                                q,
                                total_n - q - 1,
                                f"rooted#{idx}",
                                x,
                                list(xs),
                                t,
                                args,
                            )
                            cases += 1
        print("exhaustive-total-n", total_n, "cases", cases, "best", best, flush=True)
    return cases


def random_avoiding_with_head(q, x, length):
    for _ in range(200):
        xs = base.random_avoiding_seq(0, q, length)
        if base.avoids231([x] + xs):
            return xs
    return [q for _ in range(length)]


def variants(q, x, length):
    near = max(0, q - 1)
    mid = q // 2
    third = q // 3
    if length == 0:
        return [[]]
    out = [
        [q for _ in range(length)],
        [x for _ in range(length)],
        [near if i % 2 == 0 else q for i in range(length)],
        [q if i % 2 == 0 else near for i in range(length)],
        [0 if i % 2 == 0 else q for i in range(length)],
        [q if i % 2 == 0 else 0 for i in range(length)],
        [mid if i % 3 == 0 else (third if i % 3 == 1 else q) for i in range(length)],
        random_avoiding_with_head(q, x, length),
    ]
    return out


def structured(best, deadline, args):
    cases = 0
    shapes = ("balanced", "left", "right", "random")
    qs = [2, 3, 4, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987]
    lengths = [0, 1, 2, 3, 5, 8, 13, 25, 50, 100, 250, 1000, 5000, 20000]
    while time.time() < deadline:
        q = random.choice(qs)
        x = random.randrange(q)
        right_n = random.choice([0, 1, q // 3, q, 2 * q])
        length = random.choice(lengths)
        shape = random.choice(shapes)
        t = base.rooted_tree(q, right_n, shape)
        for xs in variants(q, x, length):
            if args.avoid and not base.avoids231([x] + xs):
                continue
            record(best, "structured", q, right_n, shape, x, xs, t, args)
            cases += 1
        if cases % args.progress_every == 0:
            print("structured-cases", cases, "best", best, flush=True)
    return cases


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=300.0)
    parser.add_argument("--seed", type=int, default=20260603)
    parser.add_argument("--mode", choices=("all", "exhaustive", "structured"), default="all")
    parser.add_argument("--d", type=float, default=1.0)
    parser.add_argument("--avoid", action="store_true")
    parser.add_argument("--exhaustive-total-n", type=int, default=7)
    parser.add_argument("--exhaustive-len", type=int, default=7)
    parser.add_argument("--exhaustive-extra", type=int, default=3)
    parser.add_argument("--progress-every", type=int, default=1000)
    args = parser.parse_args()
    random.seed(args.seed)
    deadline = time.time() + args.seconds
    best = {"gap": (float("-inf"), None)}
    ex_cases = 0
    st_cases = 0
    if args.mode in ("all", "exhaustive"):
        ex_cases = exhaustive(best, deadline, args)
    if args.mode in ("all", "structured") and time.time() < deadline:
        st_cases = structured(best, deadline, args)
    print("DONE", "exhaustive", ex_cases, "structured", st_cases, "best", best, flush=True)


if __name__ == "__main__":
    main()
