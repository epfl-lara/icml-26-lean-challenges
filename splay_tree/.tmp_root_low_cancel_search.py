from __future__ import annotations

import argparse
import importlib.util
import random
import time
from pathlib import Path

BASE_PATH = Path(__file__).with_name(".tmp_pair_certificate_search.py")
SPEC = importlib.util.spec_from_file_location("splay_base", BASE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"could not load {BASE_PATH}")
base = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(base)


def rooted_trees(total_n: int, q: int):
    for l in base.trees(0, q):
        for r in base.trees(q + 1, total_n - q - 1):
            yield base.N(l, q, r)


def root_key(t):
    if t == base.E:
        return None
    return t[1]


def check(actual, reset, q: int, x: int, slack: int):
    r = root_key(actual)
    if r is None or not (r <= x < q):
        return None
    lhs = base.path_len(actual, q) + base.path_len(base.splay(reset, x), q)
    rhs0 = base.path_len(base.splay(actual, x), q)
    gap = lhs - (rhs0 + slack)
    payload = {
        "q": q,
        "x": x,
        "actual_root": r,
        "lhs": lhs,
        "rhs_without_slack": rhs0,
        "slack": slack,
        "actual_path_q": base.path_len(actual, q),
        "reset_after_x_path_q": base.path_len(base.splay(reset, x), q),
        "actual_after_x_path_q": rhs0,
        "actual": actual,
        "reset": reset,
    }
    if gap > 0:
        return payload
    return None


def exhaustive(args, deadline):
    cases = 0
    best = (float("-inf"), None)
    for total_n in range(2, args.total_n + 1):
        trees = base.trees(0, total_n)
        for q in range(1, total_n):
            resets = list(rooted_trees(total_n, q))
            for actual in trees:
                r = root_key(actual)
                if r is None:
                    continue
                for reset in resets:
                    for x in range(q):
                        if time.time() > deadline:
                            return cases, best
                        if not (r <= x):
                            continue
                        lhs = base.path_len(actual, q) + base.path_len(base.splay(reset, x), q)
                        rhs0 = base.path_len(base.splay(actual, x), q)
                        gap = lhs - (rhs0 + args.slack)
                        if gap > best[0]:
                            best = (gap, {
                                "total_n": total_n,
                                "q": q,
                                "x": x,
                                "actual_root": r,
                                "lhs": lhs,
                                "rhs_without_slack": rhs0,
                                "slack": args.slack,
                                "actual_path_q": base.path_len(actual, q),
                                "reset_after_x_path_q": base.path_len(base.splay(reset, x), q),
                                "actual_after_x_path_q": rhs0,
                            })
                        cases += 1
                        ce = check(actual, reset, q, x, args.slack)
                        if ce:
                            print("COUNTER root-low-cancel", {"total_n": total_n, **ce}, flush=True)
                            raise SystemExit(2)
            print("total_n", total_n, "q", q, "cases", cases, "best", best, flush=True)
    return cases, best


def structured(args, deadline):
    cases = 0
    best = (float("-inf"), None)
    shapes = ["balanced", "left", "right", "random"]
    while time.time() < deadline:
        total_n = random.choice([8, 13, 21, 34, 55, 89, 144, 233])
        q = random.randrange(1, total_n)
        x = random.randrange(q)
        actual_vals = range(total_n)
        if random.random() < 0.5:
            actual = base.random_tree(actual_vals)
        else:
            root = random.randrange(x + 1)
            actual = base.N(base.random_tree(range(root)), root, base.random_tree(range(root + 1, total_n)))
        r = root_key(actual)
        if r is None or not (r <= x):
            continue
        shape = random.choice(shapes)
        if shape == "random":
            reset = base.N(base.random_tree(range(q)), q, base.random_tree(range(q + 1, total_n)))
        else:
            reset = base.rooted_tree(q, total_n - q - 1, shape)
        lhs = base.path_len(actual, q) + base.path_len(base.splay(reset, x), q)
        rhs0 = base.path_len(base.splay(actual, x), q)
        gap = lhs - (rhs0 + args.slack)
        if gap > best[0]:
            best = (gap, {
                "total_n": total_n,
                "q": q,
                "x": x,
                "shape": shape,
                "actual_root": r,
                "lhs": lhs,
                "rhs_without_slack": rhs0,
                "slack": args.slack,
                "actual_path_q": base.path_len(actual, q),
                "reset_after_x_path_q": base.path_len(base.splay(reset, x), q),
                "actual_after_x_path_q": rhs0,
            })
        cases += 1
        ce = check(actual, reset, q, x, args.slack)
        if ce:
            print("COUNTER root-low-cancel structured", {"total_n": total_n, **ce}, flush=True)
            raise SystemExit(2)
        if cases % args.progress_every == 0:
            print("structured", cases, "best", best, flush=True)
    return cases, best


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("all", "exhaustive", "structured"), default="all")
    parser.add_argument("--seconds", type=float, default=120.0)
    parser.add_argument("--seed", type=int, default=20260605)
    parser.add_argument("--total-n", type=int, default=8)
    parser.add_argument("--slack", type=int, default=8)
    parser.add_argument("--progress-every", type=int, default=50000)
    args = parser.parse_args()
    random.seed(args.seed)
    deadline = time.time() + args.seconds
    total = 0
    best = (float("-inf"), None)
    if args.mode in ("all", "exhaustive"):
        cases, b = exhaustive(args, deadline)
        total += cases
        best = max(best, b, key=lambda z: z[0])
    if args.mode in ("all", "structured") and time.time() < deadline:
        cases, b = structured(args, deadline)
        total += cases
        best = max(best, b, key=lambda z: z[0])
    print("DONE", "cases", total, "best", best, flush=True)


if __name__ == "__main__":
    main()
