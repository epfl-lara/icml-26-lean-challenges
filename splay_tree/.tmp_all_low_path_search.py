from __future__ import annotations

import argparse
import importlib.util
import random
import time
from itertools import product
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


def run_actual_reset(t, q: int, seq: list[int]):
    actual = t
    reset = t
    for x in seq:
        actual = base.splay(actual, x)
        reset = base.splay(base.splay(reset, x), q)
    return actual, reset


def check_seq(t, q: int, current: int, seq: list[int], slack: int):
    actual, reset = run_actual_reset(t, q, seq)
    lhs = base.path_len(actual, current)
    rhs0 = base.path_len(reset, current)
    gap = lhs - (rhs0 + slack)
    if gap > 0:
        return {
            "q": q,
            "current": current,
            "seq": seq,
            "lhs": lhs,
            "rhs_without_slack": rhs0,
            "slack": slack,
            "actual": actual,
            "reset": reset,
        }
    return None


def exhaustive(args, deadline):
    cases = 0
    best = (float("-inf"), None)
    for total_n in range(2, args.total_n + 1):
        for q in range(1, total_n):
            vals = list(range(q))
            for t in rooted_trees(total_n, q):
                for current in vals:
                    allowed = list(range(current + 1))
                    for length in range(args.max_len + 1):
                        for seq_tuple in product(allowed, repeat=length):
                            if time.time() > deadline:
                                return cases, best
                            seq = list(seq_tuple)
                            ce = check_seq(t, q, current, seq, args.slack)
                            actual, reset = run_actual_reset(t, q, seq)
                            lhs = base.path_len(actual, current)
                            rhs0 = base.path_len(reset, current)
                            gap = lhs - (rhs0 + args.slack)
                            if gap > best[0]:
                                best = (gap, {
                                    "total_n": total_n,
                                    "q": q,
                                    "current": current,
                                    "seq": seq,
                                    "lhs": lhs,
                                    "rhs_without_slack": rhs0,
                                    "slack": args.slack,
                                })
                            cases += 1
                            if ce:
                                print("COUNTER all-low", {"total_n": total_n, **ce}, flush=True)
                                raise SystemExit(2)
        print("total_n", total_n, "cases", cases, "best", best, flush=True)
    return cases, best


def structured(args, deadline):
    cases = 0
    best = (float("-inf"), None)
    shapes = ["balanced", "left", "right", "random"]
    while time.time() < deadline:
        total_n = random.choice([8, 13, 21, 34, 55, 89])
        q = random.randrange(1, total_n)
        current = random.randrange(q)
        shape = random.choice(shapes)
        t = base.rooted_tree(q, total_n - q - 1, shape)
        if shape == "random":
            t = base.N(
                base.random_tree(range(q)),
                q,
                base.random_tree(range(q + 1, total_n)),
            )
        length = random.randrange(args.max_random_len + 1)
        modes = [
            list(range(current + 1)),
            list(reversed(range(current + 1))),
            [current],
            [0, current] if current else [0],
        ]
        mode = random.choice(modes)
        seq = [random.choice(mode) for _ in range(length)]
        ce = check_seq(t, q, current, seq, args.slack)
        actual, reset = run_actual_reset(t, q, seq)
        lhs = base.path_len(actual, current)
        rhs0 = base.path_len(reset, current)
        gap = lhs - (rhs0 + args.slack)
        if gap > best[0]:
            best = (gap, {
                "total_n": total_n,
                "q": q,
                "current": current,
                "shape": shape,
                "seq_len": len(seq),
                "seq_prefix": seq[:40],
                "lhs": lhs,
                "rhs_without_slack": rhs0,
                "slack": args.slack,
            })
        cases += 1
        if ce:
            print("COUNTER all-low structured", {"total_n": total_n, **ce}, flush=True)
            raise SystemExit(2)
        if cases % args.progress_every == 0:
            print("structured", cases, "best", best, flush=True)
    return cases, best


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("all", "exhaustive", "structured"), default="all")
    parser.add_argument("--seconds", type=float, default=120.0)
    parser.add_argument("--seed", type=int, default=20260604)
    parser.add_argument("--total-n", type=int, default=7)
    parser.add_argument("--max-len", type=int, default=7)
    parser.add_argument("--max-random-len", type=int, default=400)
    parser.add_argument("--slack", type=int, default=4)
    parser.add_argument("--progress-every", type=int, default=10000)
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
