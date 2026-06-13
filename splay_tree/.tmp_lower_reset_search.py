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


def pivot_reset_lower(t, seq, q):
    total = 0
    for x in seq:
        total += base.path_len(t, x)
        t = base.splay(base.splay(t, x), q)
    return total


def budget_parts(t, seq, q):
    hull = set(base.search_path_keys(t, q))
    for x in seq:
        hull.update(base.search_path_keys(t, x))
    return len(seq), len(hull)


def seq_variants(q, length):
    if length == 0:
        return [[]]
    mid = q // 2
    near = max(0, q - 1)
    third = q // 3
    variants = [
        [near if i % 2 == 0 else 0 for i in range(length)],
        [0 if i % 2 == 0 else near for i in range(length)],
        [mid if i % 2 == 0 else 0 for i in range(length)],
        [0 if i % 2 == 0 else mid for i in range(length)],
        [mid if i % 3 == 0 else (third if i % 3 == 1 else 0) for i in range(length)],
        [0 for _ in range(length)],
        [near for _ in range(length)],
        base.random_avoiding_seq(0, near, length),
    ]
    return variants


def update_best(best, key, ratio, payload):
    if ratio > best[key][0]:
        best[key] = (ratio, payload)


def record(best, label, q, right_n, shape, seq, t, args):
    lower = pivot_reset_lower(t, seq, q)
    pair = base.pivot_reset_pair(t, seq, q)
    budget = base.boundary_budget(t, seq, q)
    length, hull = budget_parts(t, seq, q)
    sep = args.sep_a * length + args.sep_b * hull
    if budget == 0 or sep == 0:
        raise AssertionError("zero denominator")
    payload = {
        "lower": lower,
        "pair": pair,
        "budget": budget,
        "length": length,
        "hull": hull,
        "sep": sep,
        "label": label,
        "q": q,
        "right_n": right_n,
        "shape": shape,
        "seq": base.seq_summary(seq),
    }
    update_best(best, "lower_budget", lower / budget, payload)
    update_best(best, "lower_sep", lower / sep, payload)
    update_best(best, "pair_budget", pair / budget, payload)
    if lower > args.max_lower_budget * budget:
        print("COUNTER lower<=budget", args.max_lower_budget, payload, flush=True)
        raise SystemExit(2)
    if lower > sep:
        print("COUNTER lower<=sep", args.sep_a, args.sep_b, payload, flush=True)
        raise SystemExit(3)
    if pair > args.max_pair_budget * budget:
        print("COUNTER pair<=budget", args.max_pair_budget, payload, flush=True)
        raise SystemExit(4)


def exhaustive(best, deadline, args):
    cases = 0
    for total_n in range(2, args.exhaustive_total_n + 1):
        for q in range(1, total_n):
            rooted = []
            for l in base.trees(0, q):
                for r in base.trees(q + 1, total_n - q - 1):
                    rooted.append(base.N(l, q, r))
            max_len = min(args.exhaustive_len, q + args.exhaustive_extra)
            for length in range(max_len + 1):
                for seq in product(range(q), repeat=length):
                    if time.time() > deadline:
                        return cases
                    if not base.avoids231(seq):
                        continue
                    for idx, t in enumerate(rooted):
                        record(best, "exhaustive", q, total_n - q - 1, f"rooted#{idx}", seq, t, args)
                        cases += 1
        print("exhaustive-total-n", total_n, "cases", cases, "best", best, flush=True)
    return cases


def structured(best, deadline, args):
    cases = 0
    shapes = ("balanced", "left", "right", "random")
    qs = [2, 3, 4, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987]
    lengths = [0, 1, 2, 3, 5, 8, 13, 25, 50, 100, 250, 1000, 5000, 20000]
    while time.time() < deadline:
        q = random.choice(qs)
        right_n = random.choice([0, 1, q // 3, q, 2 * q])
        length = random.choice(lengths)
        shape = random.choice(shapes)
        t = base.rooted_tree(q, right_n, shape)
        for seq in seq_variants(q, length):
            if not base.avoids231(seq):
                continue
            record(best, "structured", q, right_n, shape, seq, t, args)
            cases += 1
        if cases % args.progress_every == 0:
            print("structured-cases", cases, "best", best, flush=True)
    return cases


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=300.0)
    parser.add_argument("--seed", type=int, default=20260603)
    parser.add_argument("--mode", choices=("all", "exhaustive", "structured"), default="all")
    parser.add_argument("--max-lower-budget", type=float, default=5.0)
    parser.add_argument("--max-pair-budget", type=float, default=10.0)
    parser.add_argument("--sep-a", type=float, default=5.0)
    parser.add_argument("--sep-b", type=float, default=4.0)
    parser.add_argument("--exhaustive-total-n", type=int, default=8)
    parser.add_argument("--exhaustive-len", type=int, default=7)
    parser.add_argument("--exhaustive-extra", type=int, default=3)
    parser.add_argument("--progress-every", type=int, default=2000)
    args = parser.parse_args()

    random.seed(args.seed)
    deadline = time.time() + args.seconds
    best = {
        "lower_budget": (0.0, None),
        "lower_sep": (0.0, None),
        "pair_budget": (0.0, None),
    }
    ex_cases = 0
    st_cases = 0
    if args.mode in ("all", "exhaustive"):
        ex_cases = exhaustive(best, deadline, args)
    if args.mode in ("all", "structured") and time.time() < deadline:
        st_cases = structured(best, deadline, args)
    print("DONE", "exhaustive", ex_cases, "structured", st_cases, "best", best, flush=True)


if __name__ == "__main__":
    main()
