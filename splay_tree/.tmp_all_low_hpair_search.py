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


def splay_after(t, seq):
    for x in seq:
        t = base.splay(t, x)
    return t


def suffix_reset_after(t, seq, q):
    for x in seq:
        if x < q:
            t = base.splay(base.splay(t, x), q)
    return t


def rooted_trees(total_n, q):
    for l in base.trees(0, q):
        for r in base.trees(q + 1, total_n - q - 1):
            yield base.N(l, q, r)


def pair_gap(init, q, done, x):
    actual = splay_after(init, done)
    reset = suffix_reset_after(init, done, q)
    lhs = base.path_len(actual, x) + base.path_len(base.splay(actual, x), q)
    rhs = base.path_len(actual, q) + base.path_len(reset, x) + base.path_len(base.splay(reset, x), q)
    return lhs - rhs, lhs, rhs, actual, reset


def record(best, label, total_n, q, init, done, x):
    gap, lhs, rhs, actual, reset = pair_gap(init, q, done, x)
    item = {
        "label": label,
        "total_n": total_n,
        "q": q,
        "x": x,
        "done": base.seq_summary(done),
        "gap": gap,
        "lhs": lhs,
        "rhs": rhs,
        "actual_root": None if not actual else actual[1],
        "reset_root": None if not reset else reset[1],
    }
    if gap > best["gap"][0]:
        best["gap"] = (gap, item)
    if gap > 0:
        print("COUNTER all-low-hpair", item, flush=True)
        print("init", init, flush=True)
        print("actual_after", actual, flush=True)
        print("reset_after", reset, flush=True)
        raise SystemExit(2)


def exhaustive(args, deadline):
    cases = 0
    best = {"gap": (float("-inf"), None)}
    for total_n in range(2, args.total_n + 1):
        for q in range(1, total_n):
            trees = list(rooted_trees(total_n, q))
            for x in range(q):
                max_len = min(args.length, x + 1 + args.extra)
                for length in range(max_len + 1):
                    for done in product(range(x + 1), repeat=length):
                        if args.avoid and not base.avoids231(done + (x,)):
                            continue
                        for init in trees:
                            if time.time() > deadline:
                                return cases, best
                            record(best, "exhaustive", total_n, q, init, list(done), x)
                            cases += 1
        print("total-n", total_n, "cases", cases, "best", best, flush=True)
    return cases, best


def random_avoiding_low(x, length):
    for _ in range(200):
        xs = [random.randrange(x + 1) for _ in range(length)]
        if base.avoids231(tuple(xs) + (x,)):
            return xs
    return [x] * length


def structured(args, deadline):
    cases = 0
    best = {"gap": (float("-inf"), None)}
    shapes = ("left", "right", "balanced", "random")
    lengths = [0, 1, 2, 3, 5, 8, 13, 25, 50, 100, 250, 1000]
    while time.time() < deadline:
        q = random.choice([2, 3, 4, 5, 8, 13, 21, 34, 55, 89, 144])
        total_n = q + 1 + random.choice([0, 1, q // 2, q])
        x = random.randrange(q)
        shape = random.choice(shapes)
        init = base.rooted_tree(q, total_n - q - 1, shape)
        length = random.choice(lengths)
        candidates = [
            [0] * length,
            [x] * length,
            list(range(min(length, x + 1))),
            list(reversed(range(min(length, x + 1)))),
            [random.randrange(x + 1) for _ in range(length)],
        ]
        if args.avoid:
            candidates.append(random_avoiding_low(x, length))
        for done in candidates:
            if any(y > x for y in done):
                continue
            if args.avoid and not base.avoids231(tuple(done) + (x,)):
                continue
            record(best, f"structured-{shape}", total_n, q, init, done, x)
            cases += 1
            if cases % args.progress_every == 0:
                print("structured cases", cases, "best", best, flush=True)
    return cases, best


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=180.0)
    parser.add_argument("--seed", type=int, default=20260605)
    parser.add_argument("--mode", choices=("all", "exhaustive", "structured"), default="all")
    parser.add_argument("--avoid", action="store_true")
    parser.add_argument("--total-n", type=int, default=8)
    parser.add_argument("--length", type=int, default=10)
    parser.add_argument("--extra", type=int, default=3)
    parser.add_argument("--progress-every", type=int, default=10000)
    args = parser.parse_args()
    random.seed(args.seed)
    deadline = time.time() + args.seconds
    total_cases = 0
    best = {"gap": (float("-inf"), None)}
    if args.mode in ("all", "exhaustive"):
        cases, b = exhaustive(args, deadline)
        total_cases += cases
        if b["gap"][0] > best["gap"][0]:
            best = b
    if args.mode in ("all", "structured") and time.time() < deadline:
        cases, b = structured(args, deadline)
        total_cases += cases
        if b["gap"][0] > best["gap"][0]:
            best = b
    print("DONE", "cases", total_cases, "best", best, flush=True)


if __name__ == "__main__":
    main()
