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


def boundary_budget(t, seq, q):
    hull = set(base.search_path_keys(t, q))
    for x in seq:
        hull.update(base.search_path_keys(t, x))
    return len(seq) + len(hull)


def reset_gap_potential(init, q, done, future):
    actual = splay_after(init, done)
    reset = suffix_reset_after(init, done, q)
    total = 0
    for x in future:
        if x < q:
            total += max(0, base.path_len(actual, x) - base.path_len(reset, x))
    return total


def psi(init, q, done, future, a, g, budget_state):
    actual = splay_after(init, done)
    reset = suffix_reset_after(init, done, q)
    if budget_state == "actual":
        budget_tree = actual
    elif budget_state == "reset":
        budget_tree = reset
    else:
        raise ValueError(budget_state)
    return (
        a * boundary_budget(budget_tree, future, q)
        + g * reset_gap_potential(init, q, done, future)
    )


def lt_step_gap(init, q, done, x, future, a, g, d, budget_state):
    actual = splay_after(init, done)
    reset = suffix_reset_after(init, done, q)
    actual_after = base.splay(actual, x)
    lhs = (
        base.path_len(actual, x)
        + base.path_len(actual_after, q)
        + psi(init, q, done + [x], future, a, g, budget_state)
    )
    rhs = (
        base.path_len(actual, q)
        + base.path_len(reset, x)
        + base.path_len(base.splay(reset, x), q)
        + d
        + psi(init, q, done, [x] + future, a, g, budget_state)
    )
    return lhs - rhs, {
        "lhs": lhs,
        "rhs": rhs,
        "actual_root": None if not actual else actual[1],
        "reset_root": None if not reset else reset[1],
        "actual_path_x": base.path_len(actual, x),
        "actual_after_path_q": base.path_len(actual_after, q),
        "actual_path_q": base.path_len(actual, q),
        "reset_path_x": base.path_len(reset, x),
        "reset_after_path_q": base.path_len(base.splay(reset, x), q),
        "psi_before": psi(init, q, done, [x] + future, a, g, budget_state),
        "psi_after": psi(init, q, done + [x], future, a, g, budget_state),
    }


def eq_step_gap(init, q, done, future, a, g, d, budget_state):
    return (
        psi(init, q, done + [q], future, a, g, budget_state)
        - (d + psi(init, q, done, [q] + future, a, g, budget_state))
    )


def valid_upper(seq, q):
    return all(x <= q for x in seq) and base.avoids231(seq)


def summary(seq):
    return base.seq_summary(tuple(seq))


def exhaustive(args, deadline):
    best = (-10**9, None)
    cases = 0
    for total_n in range(2, args.total_n + 1):
        for q in range(1, total_n):
            rooted = [
                base.N(l, q, r)
                for l in base.trees(0, q)
                for r in base.trees(q + 1, total_n - q - 1)
            ]
            for length in range(1, args.length + 1):
                for seq in product(range(q + 1), repeat=length):
                    seq = list(seq)
                    if not valid_upper(seq, q):
                        continue
                    for pos, x in enumerate(seq):
                        done = seq[:pos]
                        future = seq[pos + 1 :]
                        for idx, init in enumerate(rooted):
                            if time.time() > deadline:
                                return cases, best
                            if x < q:
                                gap, info = lt_step_gap(
                                    init, q, done, x, future, args.a, args.g,
                                    args.d, args.budget_state,
                                )
                            else:
                                gap = eq_step_gap(
                                    init, q, done, future, args.a, args.g, args.d,
                                    args.budget_state,
                                )
                                info = {}
                            cases += 1
                            if gap > best[0]:
                                best = (gap, {
                                    "mode": "exhaustive",
                                    "total_n": total_n,
                                    "q": q,
                                    "rooted_index": idx,
                                    "seq": summary(seq),
                                    "pos": pos,
                                    "x": x,
                                    "done": summary(done),
                                    "future": summary(future),
                                    **info,
                                })
                            if gap > 0:
                                print("COUNTER", best, flush=True)
                                print("init", init, flush=True)
                                return cases, best
        print("total_n", total_n, "cases", cases, "best", best, flush=True)
    return cases, best


def random_upper(q, length):
    for _ in range(200):
        seq = base.random_avoiding_seq(0, q, length)
        if valid_upper(seq, q):
            return seq
    return sorted(random.randrange(q + 1) for _ in range(length))


def structured(args, deadline):
    best = (-10**9, None)
    cases = 0
    shapes = ("balanced", "left", "right", "random")
    while time.time() < deadline:
        q = random.choice([1, 2, 3, 5, 8, 13, 21, 34, 55])
        total_n = q + 1 + random.choice([0, 1, q // 2, q, 2 * q])
        init = base.rooted_tree(q, total_n - q - 1, random.choice(shapes))
        length = random.choice([1, 2, 3, 5, 8, 13, 21, 34, 89])
        candidates = [
            [0] * length,
            [q] * length,
            [0 if i % 2 == 0 else q for i in range(length)],
            [q if i % 2 == 0 else 0 for i in range(length)],
            sorted(random.randrange(q + 1) for _ in range(length)),
            random_upper(q, length),
        ]
        for seq in candidates:
            if not valid_upper(seq, q):
                continue
            for pos, x in enumerate(seq):
                done = seq[:pos]
                future = seq[pos + 1 :]
                if x < q:
                    gap, info = lt_step_gap(
                        init, q, done, x, future, args.a, args.g, args.d,
                        args.budget_state,
                    )
                else:
                    gap = eq_step_gap(
                        init, q, done, future, args.a, args.g, args.d,
                        args.budget_state,
                    )
                    info = {}
                cases += 1
                if gap > best[0]:
                    best = (gap, {
                        "mode": "structured",
                        "total_n": total_n,
                        "q": q,
                        "seq": summary(seq),
                        "pos": pos,
                        "x": x,
                        "done": summary(done),
                        "future": summary(future),
                        **info,
                    })
                if gap > 0:
                    print("COUNTER", best, flush=True)
                    print("init", init, flush=True)
                    return cases, best
        if cases and cases % args.progress_every == 0:
            print("structured", cases, "best", best, flush=True)
    return cases, best


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=120.0)
    parser.add_argument("--seed", type=int, default=20260605)
    parser.add_argument("--mode", choices=("all", "exhaustive", "structured"), default="all")
    parser.add_argument("--total-n", type=int, default=7)
    parser.add_argument("--length", type=int, default=7)
    parser.add_argument("--a", type=int, default=8)
    parser.add_argument("--g", type=int, default=1)
    parser.add_argument("--d", type=int, default=8)
    parser.add_argument("--budget-state", choices=("actual", "reset"), default="actual")
    parser.add_argument("--progress-every", type=int, default=5000)
    args = parser.parse_args()
    random.seed(args.seed)
    deadline = time.time() + args.seconds
    total_cases = 0
    best = (-10**9, None)
    if args.mode in ("all", "exhaustive"):
        cases, b = exhaustive(args, deadline)
        total_cases += cases
        best = max(best, b, key=lambda z: z[0])
    if args.mode in ("all", "structured") and time.time() < deadline and best[0] <= 0:
        cases, b = structured(args, deadline)
        total_cases += cases
        best = max(best, b, key=lambda z: z[0])
    print("DONE", "cases", total_cases, "best", best, flush=True)


if __name__ == "__main__":
    main()
