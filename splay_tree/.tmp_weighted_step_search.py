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


def one_step_values(t, seq, q):
    x = seq[0]
    xs = seq[1:]
    tx = base.splay(t, x)
    tr = base.splay(tx, q)
    lower_head = base.path_len(t, x)
    pair_head = lower_head + base.path_len(tx, q)
    b_before = base.boundary_budget(t, seq, q)
    b_after = base.boundary_budget(tr, xs, q)
    return x, xs, lower_head, pair_head, b_before, b_after


def seq_summary(seq):
    return base.seq_summary(seq)


def record(best, label, q, right_n, shape, seq, t, args):
    if not seq:
        return
    x, xs, lower_head, pair_head, b_before, b_after = one_step_values(t, seq, q)
    lower_need = lower_head + args.a * b_after - args.a * b_before
    pair_need = pair_head + args.a * b_after - args.a * b_before
    payload = {
        "lower_need": lower_need,
        "pair_need": pair_need,
        "lower_head": lower_head,
        "pair_head": pair_head,
        "b_before": b_before,
        "b_after": b_after,
        "drop": b_before - b_after,
        "x": x,
        "label": label,
        "q": q,
        "right_n": right_n,
        "shape": shape,
        "seq": seq_summary(seq),
    }
    if lower_need > best["lower"][0]:
        best["lower"] = (lower_need, payload)
    if pair_need > best["pair"][0]:
        best["pair"] = (pair_need, payload)
    if lower_need > args.c:
        print("COUNTER lower step", "A", args.a, "C", args.c, payload, flush=True)
        raise SystemExit(2)
    if pair_need > args.c:
        print("COUNTER pair step", "A", args.a, "C", args.c, payload, flush=True)
        raise SystemExit(3)


def exhaustive(best, deadline, args):
    cases = 0
    for total_n in range(2, args.exhaustive_total_n + 1):
        for q in range(1, total_n):
            rooted = []
            for l in base.trees(0, q):
                for r in base.trees(q + 1, total_n - q - 1):
                    rooted.append(base.N(l, q, r))
            max_len = min(args.exhaustive_len, q + args.exhaustive_extra)
            for length in range(1, max_len + 1):
                for seq in product(range(q), repeat=length):
                    if time.time() > deadline:
                        return cases
                    if args.avoid and not base.avoids231(seq):
                        continue
                    for idx, t in enumerate(rooted):
                        record(best, "exhaustive", q, total_n - q - 1, f"rooted#{idx}", list(seq), t, args)
                        cases += 1
        print("exhaustive-total-n", total_n, "cases", cases, "best", best, flush=True)
    return cases


def random_avoiding_seq(q, length):
    if length <= 0:
        return []
    return base.random_avoiding_seq(0, q - 1, length)


def variants(q, length):
    if length <= 0:
        return []
    mid = q // 2
    near = max(0, q - 1)
    third = q // 3
    return [
        [near if i % 2 == 0 else 0 for i in range(length)],
        [0 if i % 2 == 0 else near for i in range(length)],
        [mid if i % 2 == 0 else 0 for i in range(length)],
        [0 if i % 2 == 0 else mid for i in range(length)],
        [mid if i % 3 == 0 else (third if i % 3 == 1 else 0) for i in range(length)],
        [0 for _ in range(length)],
        [near for _ in range(length)],
        random_avoiding_seq(q, length),
    ]


def structured(best, deadline, args):
    cases = 0
    shapes = ("balanced", "left", "right", "random")
    qs = [2, 3, 4, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987]
    lengths = [1, 2, 3, 5, 8, 13, 25, 50, 100, 250, 1000, 5000, 20000]
    while time.time() < deadline:
        q = random.choice(qs)
        right_n = random.choice([0, 1, q // 3, q, 2 * q])
        length = random.choice(lengths)
        shape = random.choice(shapes)
        t = base.rooted_tree(q, right_n, shape)
        for seq in variants(q, length):
            if args.avoid and not base.avoids231(seq):
                continue
            record(best, "structured", q, right_n, shape, seq, t, args)
            cases += 1
        if cases % args.progress_every == 0:
            print("structured-cases", cases, "best", best, flush=True)
    return cases


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=180.0)
    parser.add_argument("--seed", type=int, default=20260603)
    parser.add_argument("--mode", choices=("all", "exhaustive", "structured"), default="all")
    parser.add_argument("--a", type=float, default=16.0)
    parser.add_argument("--c", type=float, default=64.0)
    parser.add_argument("--avoid", action="store_true")
    parser.add_argument("--exhaustive-total-n", type=int, default=8)
    parser.add_argument("--exhaustive-len", type=int, default=7)
    parser.add_argument("--exhaustive-extra", type=int, default=3)
    parser.add_argument("--progress-every", type=int, default=2000)
    args = parser.parse_args()
    random.seed(args.seed)
    deadline = time.time() + args.seconds
    best = {
        "lower": (float("-inf"), None),
        "pair": (float("-inf"), None),
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
