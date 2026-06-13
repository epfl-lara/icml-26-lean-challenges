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


def boundary_hull_keys(t, xs, q):
    out = set(base.search_path_keys(t, q))
    for x in xs:
        out.update(base.search_path_keys(t, x))
    return out


def record(best, label, q, right_n, shape, seq, t):
    if not seq:
        return
    x = seq[0]
    xs = list(seq[1:])
    if not x < q or any(not y < q for y in xs):
        raise AssertionError("non-lower sequence")
    if not base.avoids231(seq):
        raise AssertionError("sequence does not avoid 231")
    old_path = set(base.search_path_keys(t, x))
    tx = base.splay(t, x)
    hull_after = boundary_hull_keys(tx, xs, q)
    inter = old_path & hull_after
    path_len = base.path_len(t, x)
    lhs = 32 * len(inter)
    rhs = 31 * path_len + 304
    slack = lhs - rhs
    payload = {
        "slack": slack,
        "inter": len(inter),
        "path_len": path_len,
        "x": x,
        "q": q,
        "right_n": right_n,
        "shape": shape,
        "label": label,
        "seq": base.seq_summary(seq),
        "old_path_prefix": tuple(base.search_path_keys(t, x)[:20]),
        "inter_prefix": tuple(sorted(inter)[:20]),
    }
    if slack > best[0]:
        best[0] = slack
        best[1] = payload
    if slack > 0:
        print("COUNTER boundary intersection", payload, flush=True)
        raise SystemExit(2)


def exhaustive(deadline, args, best):
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
                        record(
                            best,
                            "exhaustive",
                            q,
                            total_n - q - 1,
                            f"rooted#{idx}",
                            list(seq),
                            t,
                        )
                        cases += 1
        print("exhaustive-total-n", total_n, "cases", cases, "best", best, flush=True)
    return cases


def random_avoiding_seq(q, length):
    return base.random_avoiding_seq(0, q - 1, length)


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
        [third if i % 3 == 0 else (mid if i % 3 == 1 else near) for i in range(length)],
        [0 for _ in range(length)],
        [near for _ in range(length)],
        list(range(q)),
        list(range(q - 1, -1, -1)),
        random_avoiding_seq(q, length),
    ]


def structured(deadline, args, best):
    cases = 0
    shapes = ("balanced", "left", "right", "random")
    qs = [2, 3, 4, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597]
    lengths = [1, 2, 3, 5, 8, 13, 25, 50, 100, 250, 1000, 5000, 20000]
    while time.time() < deadline:
        q = random.choice(qs)
        right_n = random.choice([0, 1, q // 3, q, 2 * q])
        shape = random.choice(shapes)
        t = base.rooted_tree(q, right_n, shape)
        for length in lengths:
            for seq in variants(q, length):
                if time.time() > deadline:
                    return cases
                if not seq or not base.avoids231(seq):
                    continue
                record(best, "structured", q, right_n, shape, seq, t)
                cases += 1
        if cases % args.progress_every == 0:
            print("structured-cases", cases, "best", best, flush=True)
    return cases


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=180.0)
    parser.add_argument("--seed", type=int, default=20260604)
    parser.add_argument("--mode", choices=("all", "exhaustive", "structured"), default="all")
    parser.add_argument("--exhaustive-total-n", type=int, default=9)
    parser.add_argument("--exhaustive-len", type=int, default=8)
    parser.add_argument("--exhaustive-extra", type=int, default=3)
    parser.add_argument("--progress-every", type=int, default=2000)
    args = parser.parse_args()
    random.seed(args.seed)
    deadline = time.time() + args.seconds
    best = [float("-inf"), None]
    ex_cases = 0
    st_cases = 0
    if args.mode in ("all", "exhaustive"):
        ex_cases = exhaustive(deadline, args, best)
    if args.mode in ("all", "structured") and time.time() < deadline:
        st_cases = structured(deadline, args, best)
    print("DONE", "exhaustive", ex_cases, "structured", st_cases, "best", best, flush=True)


if __name__ == "__main__":
    main()
