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
    if cls == "lastq":
        return has_q and all(y < q for y in done[done.index(q) + 1 :])
    raise ValueError(cls)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=120.0)
    parser.add_argument("--slack", type=int, default=2)
    parser.add_argument("--total-n", type=int, default=7)
    parser.add_argument("--length", type=int, default=9)
    parser.add_argument("--cls", choices=("all", "noq", "hasq", "lastq"), default="all")
    parser.add_argument("--avoid", action="store_true")
    args = parser.parse_args()

    deadline = time.time() + args.seconds
    best = {"gap": (float("-inf"), None)}
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
                            base.record(
                                best,
                                args.cls,
                                total_n,
                                q,
                                f"rooted#{idx}",
                                list(done),
                                x,
                                init,
                                args,
                            )
                            cases += 1
        print("total-n", total_n, "cases", cases, "best", best, flush=True)
    print("DONE", cases, "best", best, flush=True)


if __name__ == "__main__":
    main()
