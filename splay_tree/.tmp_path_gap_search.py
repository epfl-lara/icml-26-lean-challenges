from __future__ import annotations

import argparse
import importlib.util
import time
from itertools import product
from pathlib import Path


BASE_PATH = Path(__file__).with_name(".tmp_reset_pair_hpair_search.py")
SPEC = importlib.util.spec_from_file_location("hpair_base", BASE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"could not load {BASE_PATH}")
base = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(base)


def class_ok(done: tuple[int, ...], q: int, cls: str) -> bool:
    has_q = q in done
    if cls == "all":
        return True
    if cls == "noq":
        return not has_q
    if cls == "hasq":
        return has_q
    raise ValueError(cls)


def path_gap(init, q: int, done: tuple[int, ...], x: int, slack: int):
    actual = base.splay_after(init, done)
    reset = base.suffix_reset_after(init, done, q)
    lhs = base.base.path_len(actual, x)
    rhs0 = base.base.path_len(reset, x)
    return lhs - (rhs0 + slack), lhs, rhs0, actual, reset


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=120.0)
    parser.add_argument("--slack", type=int, default=2)
    parser.add_argument("--total-n", type=int, default=8)
    parser.add_argument("--length", type=int, default=11)
    parser.add_argument("--cls", choices=("all", "noq", "hasq"), default="noq")
    parser.add_argument("--avoid", action="store_true")
    args = parser.parse_args()

    deadline = time.time() + args.seconds
    best = (float("-inf"), None)
    cases = 0
    for total_n in range(2, args.total_n + 1):
        for q in range(1, total_n):
            rooted = [
                base.base.N(l, q, r)
                for l in base.base.trees(0, q)
                for r in base.base.trees(q + 1, total_n - q - 1)
            ]
            for length in range(args.length + 1):
                for done in product(range(q + 1), repeat=length):
                    if not class_ok(done, q, args.cls):
                        continue
                    if args.avoid and not base.base.avoids231(done):
                        continue
                    for x in range(q):
                        if args.avoid and not base.base.avoids231(done + (x,)):
                            continue
                        for idx, init in enumerate(rooted):
                            if time.time() > deadline:
                                print("TIMEOUT", cases, "best", best, flush=True)
                                return
                            gap, lhs, rhs0, actual, reset = path_gap(
                                init, q, done, x, args.slack
                            )
                            if gap > best[0]:
                                best = (
                                    gap,
                                    {
                                        "total_n": total_n,
                                        "q": q,
                                        "shape": f"rooted#{idx}",
                                        "done": base.seq_summary(done),
                                        "x": x,
                                        "lhs": lhs,
                                        "rhs_without_slack": rhs0,
                                        "slack": args.slack,
                                        "actual_root": None if not actual else actual[1],
                                        "reset_root": None if not reset else reset[1],
                                    },
                                )
                            if gap > 0:
                                print("COUNTER path", best[1], flush=True)
                                print("init", init, flush=True)
                                print("actual", actual, flush=True)
                                print("reset", reset, flush=True)
                                raise SystemExit(2)
                            cases += 1
        print("total-n", total_n, "cases", cases, "best", best, flush=True)
    print("DONE", cases, "best", best, flush=True)


if __name__ == "__main__":
    main()
