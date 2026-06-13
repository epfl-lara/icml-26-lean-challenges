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


def pivot_reset_tree_after(t, seq, q):
    for x in seq:
        t = base.splay(base.splay(t, x), q)
    return t


def hull_size(t, seq, q):
    hull = set(base.search_path_keys(t, q))
    for x in seq:
        hull.update(base.search_path_keys(t, x))
    return len(hull)


def first_max_index(seq):
    mx = max(seq)
    for i, x in enumerate(seq):
        if x == mx:
            return i
    raise AssertionError("empty")


def record(best, label, q, right_n, shape, seq, t, args):
    if not seq:
        return
    m = first_max_index(seq)
    pre = seq[:m]
    piv = seq[m]
    suf = seq[m + 1 :]
    tp = pivot_reset_tree_after(t, pre, q)
    ts = base.splay(base.splay(tp, piv), q)
    h_full = hull_size(t, seq, q)
    h_pre = hull_size(t, pre, q)
    h_suf = hull_size(ts, suf, q)
    access = base.path_len(tp, piv)
    lhs = access + args.b * h_pre + args.b * h_suf
    rhs = args.a + args.b * h_full
    need = lhs - args.b * h_full
    payload = {
        "need": need,
        "lhs": lhs,
        "rhs": rhs,
        "access": access,
        "h_full": h_full,
        "h_pre": h_pre,
        "h_suf": h_suf,
        "m": m,
        "pivot": piv,
        "label": label,
        "q": q,
        "right_n": right_n,
        "shape": shape,
        "seq": base.seq_summary(seq),
    }
    if need > best["need"][0]:
        best["need"] = (need, payload)
    if lhs > rhs:
        print("COUNTER split", "a", args.a, "b", args.b, payload, flush=True)
        raise SystemExit(2)


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
                    if not base.avoids231(seq):
                        continue
                    for idx, t in enumerate(rooted):
                        record(best, "exhaustive", q, total_n - q - 1, f"rooted#{idx}", list(seq), t, args)
                        cases += 1
        print("exhaustive-total-n", total_n, "cases", cases, "best", best, flush=True)
    return cases


def variants(q, length):
    if length <= 0:
        return []
    near = q - 1
    mid = q // 2
    third = q // 3
    return [
        [near if i % 2 == 0 else 0 for i in range(length)],
        [0 if i % 2 == 0 else near for i in range(length)],
        [mid if i % 2 == 0 else 0 for i in range(length)],
        [0 if i % 2 == 0 else mid for i in range(length)],
        [mid if i % 3 == 0 else (third if i % 3 == 1 else 0) for i in range(length)],
        [0 for _ in range(length)],
        [near for _ in range(length)],
        base.random_avoiding_seq(0, near, length),
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
            if not base.avoids231(seq):
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
    parser.add_argument("--a", type=float, default=5.0)
    parser.add_argument("--b", type=float, default=4.0)
    parser.add_argument("--exhaustive-total-n", type=int, default=8)
    parser.add_argument("--exhaustive-len", type=int, default=7)
    parser.add_argument("--exhaustive-extra", type=int, default=3)
    parser.add_argument("--progress-every", type=int, default=500)
    args = parser.parse_args()
    random.seed(args.seed)
    deadline = time.time() + args.seconds
    best = {"need": (float("-inf"), None)}
    ex_cases = 0
    st_cases = 0
    if args.mode in ("all", "exhaustive"):
        ex_cases = exhaustive(best, deadline, args)
    if args.mode in ("all", "structured") and time.time() < deadline:
        st_cases = structured(best, deadline, args)
    print("DONE", "exhaustive", ex_cases, "structured", st_cases, "best", best, flush=True)


if __name__ == "__main__":
    main()
