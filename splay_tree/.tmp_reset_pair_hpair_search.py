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


def hpair_gap(init, q, done, x, slack):
    a = splay_after(init, done)
    b = suffix_reset_after(init, done, q)
    lhs = base.path_len(a, x) + base.path_len(base.splay(a, x), q)
    rhs0 = (
        base.path_len(a, q)
        + base.path_len(b, x)
        + base.path_len(base.splay(b, x), q)
    )
    return lhs - (rhs0 + slack), lhs, rhs0, a, b


def seq_summary(seq):
    return base.seq_summary(seq)


def record(best, label, total_n, q, shape, done, x, init, args):
    gap, lhs, rhs0, a, b = hpair_gap(init, q, done, x, args.slack)
    if gap > best["gap"][0]:
        best["gap"] = (
            gap,
            {
                "label": label,
                "total_n": total_n,
                "q": q,
                "shape": shape,
                "x": x,
                "done": seq_summary(done),
                "lhs": lhs,
                "rhs_without_slack": rhs0,
                "slack": args.slack,
                "a_root": None if not a else a[1],
                "b_root": None if not b else b[1],
            },
        )
    if gap > 0:
        print("COUNTER hpair", best["gap"][1], flush=True)
        print("init", init, flush=True)
        print("actual_after", a, flush=True)
        print("reset_after", b, flush=True)
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
            for length in range(max_len + 1):
                for done in product(range(q + 1), repeat=length):
                    if args.avoid and not base.avoids231(done):
                        continue
                    for x in range(q):
                        if args.avoid and not base.avoids231(tuple(done) + (x,)):
                            continue
                        for idx, init in enumerate(rooted):
                            if time.time() > deadline:
                                return cases
                            record(
                                best,
                                "exhaustive",
                                total_n,
                                q,
                                f"rooted#{idx}",
                                list(done),
                                x,
                                init,
                                args,
                            )
                            cases += 1
        print("exhaustive-total-n", total_n, "cases", cases, "best", best, flush=True)
    return cases


def random_done(q, length, avoid):
    if not avoid:
        return [random.randrange(q + 1) for _ in range(length)]
    for _ in range(200):
        xs = base.random_avoiding_seq(0, q, length)
        if base.avoids231(xs):
            return xs
    return [q] * length


def structured(best, deadline, args):
    cases = 0
    shapes = ("balanced", "left", "right", "random")
    qs = [2, 3, 4, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377]
    lengths = [0, 1, 2, 3, 5, 8, 13, 25, 50, 100, 250, 1000, 5000]
    while time.time() < deadline:
        q = random.choice(qs)
        total_n = q + 1 + random.choice([0, 1, q // 3, q, 2 * q])
        shape = random.choice(shapes)
        if shape == "random":
            init = base.rooted_tree(q, total_n - q - 1, "random")
        else:
            init = base.rooted_tree(q, total_n - q - 1, shape)
        length = random.choice(lengths)
        candidates = []
        if length == 0:
            candidates.append([])
        else:
            candidates.extend(
                [
                    [q] * length,
                    [0] * length,
                    [q - 1] * length,
                    [q if i % 2 == 0 else 0 for i in range(length)],
                    [0 if i % 2 == 0 else q for i in range(length)],
                    [q if i % 2 == 0 else q - 1 for i in range(length)],
                    [q - 1 if i % 2 == 0 else q for i in range(length)],
                    random_done(q, length, args.avoid),
                ]
            )
        for done in candidates:
            if args.avoid and not base.avoids231(done):
                continue
            for x in {0, q // 2, q - 1, random.randrange(q)}:
                if args.avoid and not base.avoids231(tuple(done) + (x,)):
                    continue
                record(best, "structured", total_n, q, shape, done, x, init, args)
                cases += 1
        if cases % args.progress_every == 0:
            print("structured-cases", cases, "best", best, flush=True)
    return cases


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=300.0)
    parser.add_argument("--seed", type=int, default=20260603)
    parser.add_argument("--mode", choices=("all", "exhaustive", "structured"), default="all")
    parser.add_argument("--slack", type=int, default=2)
    parser.add_argument("--avoid", action="store_true")
    parser.add_argument("--exhaustive-total-n", type=int, default=8)
    parser.add_argument("--exhaustive-len", type=int, default=8)
    parser.add_argument("--exhaustive-extra", type=int, default=3)
    parser.add_argument("--progress-every", type=int, default=1000)
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
