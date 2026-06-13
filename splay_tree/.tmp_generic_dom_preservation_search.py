from __future__ import annotations

import argparse
import importlib.util
import time
from pathlib import Path


BASE_PATH = Path(__file__).with_name(".tmp_pair_certificate_search.py")
SPEC = importlib.util.spec_from_file_location("splay_search_base", BASE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"could not load {BASE_PATH}")
base = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(base)


def domination_holds(q: int, slack: int, actual, reset) -> bool:
    ks = base.keys(actual)
    if base.keys(reset) != ks:
        return False
    if not reset or reset[1] != q:
        return False
    for y in ks:
        if y < q:
            lhs = base.path_len(actual, y) + base.path_len(base.splay(actual, y), q)
            rhs = (
                base.path_len(actual, q)
                + base.path_len(reset, y)
                + base.path_len(base.splay(reset, y), q)
                + slack
            )
            if lhs > rhs:
                return False
    return True


def preservation_gap(q: int, slack: int, actual, reset, x: int):
    actual2 = base.splay(actual, x)
    reset2 = base.splay(base.splay(reset, x), q)
    worst = (float("-inf"), None)
    for y in base.keys(actual):
        if y < q:
            lhs = base.path_len(actual2, y) + base.path_len(base.splay(actual2, y), q)
            rhs0 = (
                base.path_len(actual2, q)
                + base.path_len(reset2, y)
                + base.path_len(base.splay(reset2, y), q)
            )
            gap = lhs - (rhs0 + slack)
            if gap > worst[0]:
                worst = (gap, (y, lhs, rhs0))
    return worst


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=8)
    parser.add_argument("--seconds", type=float, default=180)
    parser.add_argument("--slack", type=int, default=2)
    parser.add_argument("--progress", type=int, default=100000)
    args = parser.parse_args()
    deadline = time.time() + args.seconds
    checked_pairs = 0
    dom_pairs = 0
    steps = 0
    best = (float("-inf"), None)
    for n in range(2, args.n + 1):
        all_trees = base.trees(0, n)
        for q in range(1, n):
            rooted = [t for t in all_trees if t and t[1] == q]
            for actual in all_trees:
                for reset in rooted:
                    if time.time() > deadline:
                        print("TIMEOUT", dict(n=n, checked_pairs=checked_pairs, dom_pairs=dom_pairs, steps=steps, best=best), flush=True)
                        return
                    checked_pairs += 1
                    if not domination_holds(q, args.slack, actual, reset):
                        continue
                    dom_pairs += 1
                    for x in range(q):
                        gap = preservation_gap(q, args.slack, actual, reset, x)
                        steps += 1
                        if gap[0] > best[0]:
                            best = (gap[0], dict(n=n, q=q, x=x, y=gap[1][0], lhs=gap[1][1], rhs0=gap[1][2], actual=actual, reset=reset))
                            print("BEST", best, flush=True)
                        if gap[0] > 0:
                            print("COUNTER", dict(n=n, q=q, x=x, gap=gap, actual=actual, reset=reset), flush=True)
                            return
                    if steps and steps % args.progress == 0:
                        print("progress", dict(n=n, checked_pairs=checked_pairs, dom_pairs=dom_pairs, steps=steps, best=best), flush=True)
        print("finished n", n, dict(checked_pairs=checked_pairs, dom_pairs=dom_pairs, steps=steps, best=best), flush=True)
    print("DONE", dict(checked_pairs=checked_pairs, dom_pairs=dom_pairs, steps=steps, best=best), flush=True)


if __name__ == "__main__":
    main()
