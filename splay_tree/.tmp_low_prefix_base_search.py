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


def gap(init, q, prefix, lo, slack):
    actual = base.splay(splay_after(init, prefix), q)
    reset = suffix_reset_after(init, prefix, q)
    best = None
    for x in range(lo, q):
        lhs = base.path_len(actual, x) + base.path_len(base.splay(actual, x), q)
        rhs0 = (
            base.path_len(actual, q)
            + base.path_len(reset, x)
            + base.path_len(base.splay(reset, x), q)
        )
        g = lhs - (rhs0 + slack)
        payload = {
            "x": x,
            "lo": lo,
            "lhs": lhs,
            "rhs_without_slack": rhs0,
            "slack": slack,
            "actual_root": None if not actual else actual[1],
            "reset_root": None if not reset else reset[1],
        }
        if best is None or g > best[0]:
            best = (g, payload, actual, reset)
    if best is None:
        return (0, {"empty_interval": True}, actual, reset)
    return best


def prefix_ok(prefix, q, lo):
    return all((x == q or x <= lo) for x in prefix)


def record(best, label, total_n, q, shape, prefix, lo, init, args):
    g, payload, actual, reset = gap(init, q, prefix, lo, args.slack)
    if g > best["gap"][0]:
        best["gap"] = (
            g,
            {
                "label": label,
                "total_n": total_n,
                "q": q,
                "shape": shape,
                "prefix": base.seq_summary(prefix),
                **payload,
            },
        )
    if g > 0:
        print("COUNTER low-prefix-base", best["gap"][1], flush=True)
        print("init", init, flush=True)
        print("actual_after_q", actual, flush=True)
        print("reset_after", reset, flush=True)
        raise SystemExit(2)


def exhaustive(best, deadline, args):
    cases = 0
    for total_n in range(2, args.total_n + 1):
        for q in range(1, total_n):
            rooted = [
                base.N(l, q, r)
                for l in base.trees(0, q)
                for r in base.trees(q + 1, total_n - q - 1)
            ]
            for lo in range(q):
                for length in range(args.length + 1):
                    alphabet = list(range(lo + 1)) + [q]
                    for prefix in product(alphabet, repeat=length):
                        if not prefix_ok(prefix, q, lo):
                            continue
                        if args.avoid and not base.avoids231(prefix + (q, lo)):
                            continue
                        for idx, init in enumerate(rooted):
                            if time.time() > deadline:
                                print("TIMEOUT", cases, "best", best, flush=True)
                                return cases
                            record(
                                best,
                                "exhaustive",
                                total_n,
                                q,
                                f"rooted#{idx}",
                                list(prefix),
                                lo,
                                init,
                                args,
                            )
                            cases += 1
        print("total-n", total_n, "cases", cases, "best", best, flush=True)
    return cases


def structured(best, deadline, args):
    cases = 0
    shapes = ("balanced", "left", "right", "random")
    while time.time() < deadline:
        q = random.choice([2, 3, 4, 5, 8, 13, 21, 34, 55, 89])
        lo = random.randrange(q)
        total_n = q + 1 + random.choice([0, 1, q // 3, q, 2 * q])
        init = base.rooted_tree(q, total_n - q - 1, random.choice(shapes))
        length = random.choice([0, 1, 2, 3, 5, 8, 13, 25, 50, 100, 250])
        candidates = [
            [lo] * length,
            [q] * length,
            [q if i % 2 == 0 else lo for i in range(length)],
            [lo if i % 2 == 0 else q for i in range(length)],
            [random.choice(list(range(lo + 1)) + [q]) for _ in range(length)],
        ]
        for prefix in candidates:
            if args.avoid and not base.avoids231(tuple(prefix) + (q, lo)):
                continue
            record(best, "structured", total_n, q, "mixed", prefix, lo, init, args)
            cases += 1
        if cases and cases % args.progress_every == 0:
            print("structured-cases", cases, "best", best, flush=True)
    return cases


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=300.0)
    parser.add_argument("--seed", type=int, default=20260604)
    parser.add_argument("--slack", type=int, default=0)
    parser.add_argument("--avoid", action="store_true")
    parser.add_argument("--mode", choices=("all", "exhaustive", "structured"), default="all")
    parser.add_argument("--total-n", type=int, default=8)
    parser.add_argument("--length", type=int, default=9)
    parser.add_argument("--progress-every", type=int, default=10000)
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
