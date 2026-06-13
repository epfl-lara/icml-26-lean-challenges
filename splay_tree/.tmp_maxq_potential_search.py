from __future__ import annotations

import argparse
import importlib.util
import random
import time
from itertools import product
from pathlib import Path

BASE_PATH = Path(__file__).with_name(".tmp_pair_certificate_search.py")
SPEC = importlib.util.spec_from_file_location("splay_search_base", BASE_PATH)
base = importlib.util.module_from_spec(SPEC)
assert SPEC is not None and SPEC.loader is not None
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


def lower_keys(seq, q):
    return sorted({x for x in seq if x < q})


def gap_max(init, q, done, future):
    actual = splay_after(init, done)
    reset = suffix_reset_after(init, done, q)
    best = 0
    for x in lower_keys(future, q):
        best = max(best, base.path_len(actual, x) - base.path_len(reset, x))
    return max(0, best)


def boundary_budget(t, seq, q):
    hull = set(base.search_path_keys(t, q))
    for x in seq:
        hull.update(base.search_path_keys(t, x))
    return len(seq) + len(hull)


def psi(init, q, done, future, a, g, h):
    actual = splay_after(init, done)
    reset = suffix_reset_after(init, done, q)
    return (
        a * boundary_budget(reset, future, q)
        + g * gap_max(init, q, done, future)
        + h * base.path_len(actual, q)
    )


def valid_upper(seq, q):
    return all(x <= q for x in seq) and base.avoids231(seq)


def lower_need(init, q, done, x, future, a, g, h):
    return (
        gap_max(init, q, done, [x] + future)
        + psi(init, q, done + [x], future, a, g, h)
        - psi(init, q, done, [x] + future, a, g, h)
    )


def lower_details(init, q, done, x, future, a, g, h):
    actual = splay_after(init, done)
    reset = suffix_reset_after(init, done, q)
    actual_after = base.splay(actual, x)
    reset_after = base.splay(base.splay(reset, x), q)
    return {
        "gap_before": gap_max(init, q, done, [x] + future),
        "gap_after": gap_max(init, q, done + [x], future),
        "q_before": base.path_len(actual, q),
        "q_after": base.path_len(actual_after, q),
        "b_before": boundary_budget(reset, [x] + future, q),
        "b_after": boundary_budget(reset_after, future, q),
        "psi_before": psi(init, q, done, [x] + future, a, g, h),
        "psi_after": psi(init, q, done + [x], future, a, g, h),
    }


def eq_growth(init, q, done, future):
    return gap_max(init, q, done + [q], future) - gap_max(init, q, done, future)


def record(best, kind, value, payload):
    if value > best[kind][0]:
        best[kind] = (value, payload)


def exhaustive(args, deadline, best):
    cases = 0
    for total_n in range(2, args.total_n + 1):
        for q in range(1, total_n):
            rooted = [
                base.N(l, q, r)
                for l in base.trees(0, q)
                for r in base.trees(q + 1, total_n - q - 1)
            ]
            for length in range(1, args.length + 1):
                for seq0 in product(range(q + 1), repeat=length):
                    if time.time() > deadline:
                        return cases
                    seq = list(seq0)
                    if not valid_upper(seq, q):
                        continue
                    for ti, init in enumerate(rooted):
                        for pos, x in enumerate(seq):
                            done = seq[:pos]
                            future = seq[pos + 1 :]
                            payload = {
                                "mode": "exhaustive",
                                "total_n": total_n,
                                "q": q,
                                "tree": ti,
                                "seq": base.seq_summary(seq),
                                "pos": pos,
                                "x": x,
                                "done": base.seq_summary(done),
                                "future": base.seq_summary(future),
                            }
                            if x < q:
                                value = lower_need(init, q, done, x, future, args.a, args.g, args.h)
                                payload.update(lower_details(init, q, done, x, future, args.a, args.g, args.h))
                                record(best, "lower", value, payload)
                            else:
                                value = eq_growth(init, q, done, future)
                                record(best, "eq", value, payload)
                            cases += 1
        print("exhaustive total_n", total_n, "cases", cases, "best", best, flush=True)
    return cases


def structured(args, deadline, best):
    cases = 0
    shapes = ("balanced", "left", "right", "random")
    qs = [2, 3, 5, 8, 13, 21, 34, 55, 89]
    lengths = [1, 2, 3, 5, 8, 13, 21, 34, 89, 233]
    while time.time() < deadline:
        q = random.choice(qs)
        total_n = q + 1 + random.choice([0, 1, q // 2, q, 2 * q])
        init = base.rooted_tree(q, total_n - q - 1, random.choice(shapes))
        length = random.choice(lengths)
        candidates = [
            [0] * length,
            [q] * length,
            [0 if i % 2 == 0 else q for i in range(length)],
            [q if i % 2 == 0 else 0 for i in range(length)],
            sorted(random.randrange(q + 1) for _ in range(length)),
            base.random_avoiding_seq(0, q, length),
        ]
        for seq in candidates:
            if not valid_upper(seq, q):
                continue
            for pos, x in enumerate(seq):
                done = seq[:pos]
                future = seq[pos + 1 :]
                payload = {
                    "mode": "structured",
                    "total_n": total_n,
                    "q": q,
                    "seq": base.seq_summary(seq),
                    "pos": pos,
                    "x": x,
                    "done": base.seq_summary(done),
                    "future": base.seq_summary(future),
                }
                if x < q:
                    value = lower_need(init, q, done, x, future, args.a, args.g, args.h)
                    payload.update(lower_details(init, q, done, x, future, args.a, args.g, args.h))
                    record(best, "lower", value, payload)
                else:
                    value = eq_growth(init, q, done, future)
                    record(best, "eq", value, payload)
                cases += 1
        if cases and cases % args.progress_every == 0:
            print("structured", cases, "best", best, flush=True)
    return cases


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=180.0)
    parser.add_argument("--seed", type=int, default=20260605)
    parser.add_argument("--mode", choices=("all", "exhaustive", "structured"), default="all")
    parser.add_argument("--total-n", type=int, default=8)
    parser.add_argument("--length", type=int, default=7)
    parser.add_argument("--a", type=float, default=64.0)
    parser.add_argument("--g", type=float, default=2.0)
    parser.add_argument("--h", type=float, default=1.0)
    parser.add_argument("--progress-every", type=int, default=5000)
    args = parser.parse_args()
    random.seed(args.seed)
    deadline = time.time() + args.seconds
    best = {"lower": (float("-inf"), None), "eq": (float("-inf"), None)}
    cases = 0
    if args.mode in ("all", "exhaustive"):
        cases += exhaustive(args, deadline, best)
    if args.mode in ("all", "structured") and time.time() < deadline:
        cases += structured(args, deadline, best)
    print("DONE", "cases", cases, "best", best, flush=True)


if __name__ == "__main__":
    main()
