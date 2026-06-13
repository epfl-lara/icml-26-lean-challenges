from __future__ import annotations

import argparse
import importlib.util
import random
import time
from pathlib import Path

BASE_PATH = Path(__file__).with_name(".tmp_low_preservation_search.py")
SPEC = importlib.util.spec_from_file_location("low_base", BASE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"could not load {BASE_PATH}")
low = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(low)
base = low.base


def path_gap(actual, reset, q: int, lo: int, x: int, slack: int):
    actual2 = base.splay(actual, x)
    reset2 = base.splay(base.splay(reset, x), q)
    out = None
    for y in range(lo, q):
        if y not in base.keys(actual2):
            continue
        lhs = base.path_len(actual2, y)
        rhs0 = base.path_len(reset2, y)
        gap = lhs - (rhs0 + slack)
        item = {
            "q": q,
            "lo": lo,
            "x": x,
            "y": y,
            "lhs": lhs,
            "rhs_without_slack": rhs0,
            "slack": slack,
            "actual_root": None if not actual else actual[1],
            "reset_root": None if not reset else reset[1],
            "actual2_root": None if not actual2 else actual2[1],
            "reset2_root": None if not reset2 else reset2[1],
        }
        if out is None or gap > out[0]:
            out = (gap, item)
    return out or (0, {"empty_interval": True})


def check_case(total_n: int, q: int, actual, reset, lo: int, x: int, slack: int):
    if x not in base.keys(actual) or not (x < q and x <= lo):
        return None
    if not low.dom_above(actual, reset, q, lo, slack):
        return None
    gap, payload = path_gap(actual, reset, q, lo, x, slack)
    if gap > 0:
        return {
            "total_n": total_n,
            **payload,
            "actual": actual,
            "reset": reset,
            "actual2": base.splay(actual, x),
            "reset2": base.splay(base.splay(reset, x), q),
        }
    return None


def exhaustive(args, deadline):
    cases = 0
    doms = 0
    best = (float("-inf"), None)
    for total_n in range(2, args.total_n + 1):
        all_trees = base.trees(0, total_n)
        for q in range(1, total_n):
            resets = list(low.rooted_trees(total_n, q))
            for actual in all_trees:
                for reset in resets:
                    if time.time() > deadline:
                        return cases, doms, best
                    if base.keys(actual) != base.keys(reset):
                        continue
                    for lo in range(q):
                        if not low.dom_above(actual, reset, q, lo, args.dom_slack):
                            continue
                        doms += 1
                        for x in range(lo + 1):
                            ce = check_case(total_n, q, actual, reset, lo, x, args.path_slack)
                            cases += 1
                            gap, payload = path_gap(actual, reset, q, lo, x, args.path_slack)
                            if gap > best[0]:
                                best = (gap, {"total_n": total_n, **payload})
                            if ce:
                                print("COUNTER low-path", ce, flush=True)
                                raise SystemExit(2)
        print("total_n", total_n, "cases", cases, "doms", doms, "best", best, flush=True)
    return cases, doms, best


def structured(args, deadline):
    cases = 0
    doms = 0
    best = (float("-inf"), None)
    while time.time() < deadline:
        total_n = random.choice([5, 6, 7, 8, 10, 13, 21, 34])
        q = random.randrange(1, total_n)
        actual, reset = low.random_case(total_n, q)
        for lo in {0, q // 2, max(0, q - 2), q - 1, random.randrange(q)}:
            if not low.dom_above(actual, reset, q, lo, args.dom_slack):
                continue
            doms += 1
            for x in range(lo + 1):
                ce = check_case(total_n, q, actual, reset, lo, x, args.path_slack)
                cases += 1
                gap, payload = path_gap(actual, reset, q, lo, x, args.path_slack)
                if gap > best[0]:
                    best = (gap, {"total_n": total_n, **payload})
                if ce:
                    print("COUNTER low-path", ce, flush=True)
                    raise SystemExit(2)
        if cases and cases % args.progress_every == 0:
            print("structured", cases, "doms", doms, "best", best, flush=True)
    return cases, doms, best


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=120.0)
    parser.add_argument("--seed", type=int, default=20260605)
    parser.add_argument("--total-n", type=int, default=8)
    parser.add_argument("--dom-slack", type=int, default=8)
    parser.add_argument("--path-slack", type=int, default=8)
    parser.add_argument("--mode", choices=("all", "exhaustive", "structured"), default="all")
    parser.add_argument("--progress-every", type=int, default=50000)
    args = parser.parse_args()
    random.seed(args.seed)
    deadline = time.time() + args.seconds
    total_cases = total_doms = 0
    best = (float("-inf"), None)
    if args.mode in ("all", "exhaustive"):
        cases, doms, b = exhaustive(args, deadline)
        total_cases += cases
        total_doms += doms
        best = max(best, b, key=lambda z: z[0])
    if args.mode in ("all", "structured") and time.time() < deadline:
        cases, doms, b = structured(args, deadline)
        total_cases += cases
        total_doms += doms
        best = max(best, b, key=lambda z: z[0])
    print("DONE", "cases", total_cases, "doms", total_doms, "best", best, flush=True)


if __name__ == "__main__":
    main()
