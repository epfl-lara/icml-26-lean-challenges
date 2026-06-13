from __future__ import annotations

import argparse
import importlib.util
import itertools
import pathlib
import random
import time

base_path = pathlib.Path(__file__).with_name(".tmp_pair_certificate_search.py")
spec = importlib.util.spec_from_file_location("splay_base", base_path)
base = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(base)


def proper_ancestors(t, q):
    path = base.search_path_keys(t, q)
    return [x for x in path if x != q]


def static_subroot_by_touched(seq, t, done, key):
    if key not in base.keys(t):
        return False
    touched = {seq[i] for i in done}
    if key in touched:
        return False
    return all(a in touched for a in proper_ancestors(t, key))


def source_potential_keys(seq, t, done, future):
    touched = {seq[i] for i in done}
    future_paths = set()
    for j in future:
        future_paths.update(base.search_path_keys(t, seq[j]))
    return [k for k in base.keys(t) if k in touched and k in future_paths]


def active_budget(t, future_values):
    hull = set()
    for x in future_values:
        hull.update(base.search_path_keys(t, x))
    return len(future_values) + len(hull)


def active_hull(t, future_values):
    hull = set()
    for x in future_values:
        hull.update(base.search_path_keys(t, x))
    return hull


def splay_after(t, seq, done):
    for i in done:
        t = base.splay(t, seq[i])
    return t


def check_source_conditions(seq, init, *, verbose=False):
    n = len(seq)
    for pos in range(n):
        done = list(range(pos))
        i = pos
        future = list(range(pos + 1, n))
        cur = splay_after(init, seq, done)
        key = seq[i]
        if not static_subroot_by_touched(seq, cur, done, key):
            if verbose:
                return False, {
                    "kind": "static",
                    "pos": pos,
                    "key": key,
                    "done": [seq[j] for j in done],
                    "future": [seq[j] for j in future],
                    "cur": cur,
                    "path": base.search_path_keys(cur, key),
                    "ancestors": proper_ancestors(cur, key),
                }
            return False, None
        new_t = base.splay(cur, key)
        new_keys = set(source_potential_keys(seq, new_t, done + [i], future))
        old_path = set(base.search_path_keys(cur, key))
        bad = sorted((new_keys & old_path) - {key})
        if bad:
            if verbose:
                return False, {
                    "kind": "inter",
                    "pos": pos,
                    "key": key,
                    "done": [seq[j] for j in done],
                    "future": [seq[j] for j in future],
                    "cur": cur,
                    "new_t": new_t,
                    "path": base.search_path_keys(cur, key),
                    "new_keys": sorted(new_keys),
                    "bad": bad,
                }
            return False, None
    return True, None


def exhaustive(max_n, max_len, seconds):
    start = time.time()
    checked = 0
    avoid_checked = 0
    for tree_n in range(1, max_n + 1):
        all_trees = base.trees(0, tree_n)
        for length in range(1, min(max_len, tree_n) + 1):
            for seq in itertools.product(range(tree_n), repeat=length):
                if time.time() - start > seconds:
                    return {"timeout": True, "checked": checked, "avoid": avoid_checked}
                checked += len(all_trees)
                if not base.avoids231(seq):
                    continue
                avoid_checked += len(all_trees)
                for t in all_trees:
                    ok, info = check_source_conditions(list(seq), t, verbose=True)
                    if not ok:
                        return {
                            "counterexample": info,
                            "seq": seq,
                            "tree_n": tree_n,
                            "checked": checked,
                            "avoid": avoid_checked,
                        }
    return {"timeout": False, "checked": checked, "avoid": avoid_checked}


def random_search(max_n, max_len, seconds):
    start = time.time()
    checked = 0
    while time.time() - start < seconds:
        tree_n = random.randint(1, max_n)
        length = random.randint(1, max_len)
        seq = base.random_avoiding_seq(0, tree_n - 1, length)
        t = base.random_tree(range(tree_n))
        checked += 1
        ok, info = check_source_conditions(seq, t, verbose=True)
        if not ok:
            return {"counterexample": info, "seq": seq, "tree_n": tree_n, "checked": checked}
    return {"timeout": True, "checked": checked}


def exhaustive_active_step(max_n, max_len, seconds, delta, C, progress_every):
    start = time.time()
    checked = 0
    avoid_checked = 0
    best = (-10**9, None)
    for tree_n in range(1, max_n + 1):
        all_trees = base.trees(0, tree_n)
        for length in range(1, min(max_len, tree_n) + 1):
            for seq in itertools.product(range(tree_n), repeat=length):
                if time.time() - start > seconds:
                    return {
                        "timeout": True,
                        "checked": checked,
                        "avoid": avoid_checked,
                        "best": best,
                    }
                if not base.avoids231(seq):
                    continue
                avoid_checked += len(all_trees)
                for t0 in all_trees:
                    t = t0
                    for pos, x in enumerate(seq):
                        future = list(seq[pos + 1 :])
                        before_values = list(seq[pos:])
                        lhs = base.path_len(t, x) + delta * active_budget(base.splay(t, x), future)
                        rhs = C + delta * active_budget(t, before_values)
                        slack = lhs - rhs
                        checked += 1
                        if slack > best[0]:
                            best = (
                                slack,
                                {
                                    "tree_n": tree_n,
                                    "length": length,
                                    "seq": seq,
                                    "pos": pos,
                                    "x": x,
                                    "path": base.path_len(t, x),
                                    "before": active_budget(t, before_values),
                                    "after": active_budget(base.splay(t, x), future),
                                    "lhs": lhs,
                                    "rhs": rhs,
                                    "tree": t,
                                },
                            )
                        if progress_every and checked % progress_every == 0:
                            print(
                                "active-progress",
                                {
                                    "checked": checked,
                                    "avoid": avoid_checked,
                                    "best_slack": best[0],
                                    "tree_n": tree_n,
                                    "length": length,
                                    "elapsed": round(time.time() - start, 1),
                                },
                                flush=True,
                            )
                        if slack > 0:
                            return {
                                "counterexample": best,
                                "checked": checked,
                                "avoid": avoid_checked,
                            }
                        t = base.splay(t, x)
    return {"timeout": False, "checked": checked, "avoid": avoid_checked, "best": best}


def exhaustive_active_intersection(max_n, max_len, seconds, progress_every):
    start = time.time()
    checked = 0
    avoid_checked = 0
    best = (-10**9, None)
    for tree_n in range(1, max_n + 1):
        all_trees = base.trees(0, tree_n)
        for length in range(1, min(max_len, tree_n) + 1):
            for seq in itertools.product(range(tree_n), repeat=length):
                if time.time() - start > seconds:
                    return {
                        "timeout": True,
                        "checked": checked,
                        "avoid": avoid_checked,
                        "best": best,
                    }
                if not base.avoids231(seq):
                    continue
                avoid_checked += len(all_trees)
                for t0 in all_trees:
                    t = t0
                    for pos, x in enumerate(seq):
                        future = list(seq[pos + 1 :])
                        path = set(base.search_path_keys(t, x))
                        new = active_hull(base.splay(t, x), future)
                        inter_keys = sorted(new & path)
                        inter = len(inter_keys)
                        path_len = base.path_len(t, x)
                        slack = 4 * inter - (3 * path_len + 12)
                        checked += 1
                        if slack > best[0]:
                            best = (
                                slack,
                                {
                                    "tree_n": tree_n,
                                    "length": length,
                                    "seq": seq,
                                    "pos": pos,
                                    "x": x,
                                    "path_len": path_len,
                                    "inter": inter,
                                    "path": sorted(path),
                                    "inter_keys": inter_keys,
                                    "tree": t,
                                },
                            )
                        if progress_every and checked % progress_every == 0:
                            print(
                                "inter-progress",
                                {
                                    "checked": checked,
                                    "avoid": avoid_checked,
                                    "best_slack": best[0],
                                    "tree_n": tree_n,
                                    "length": length,
                                    "elapsed": round(time.time() - start, 1),
                                },
                                flush=True,
                            )
                        if slack > 0:
                            return {
                                "counterexample": best,
                                "checked": checked,
                                "avoid": avoid_checked,
                            }
                        t = base.splay(t, x)
    return {"timeout": False, "checked": checked, "avoid": avoid_checked, "best": best}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=60)
    parser.add_argument("--max-n", type=int, default=7)
    parser.add_argument("--max-len", type=int, default=7)
    parser.add_argument(
        "--mode",
        choices=["exhaustive", "random", "all", "active-step", "active-inter"],
        default="all",
    )
    parser.add_argument("--delta", type=int, default=4)
    parser.add_argument("--C", type=int, default=8)
    parser.add_argument("--progress-every", type=int, default=0)
    args = parser.parse_args()
    if args.mode in ("exhaustive", "all"):
        print("exhaustive", exhaustive(args.max_n, args.max_len, args.seconds))
    if args.mode in ("random", "all"):
        print("random", random_search(args.max_n * 8, args.max_len * 8, args.seconds))
    if args.mode == "active-step":
        print(
            "active-step",
            exhaustive_active_step(
                args.max_n,
                args.max_len,
                args.seconds,
                args.delta,
                args.C,
                args.progress_every,
            ),
        )
    if args.mode == "active-inter":
        print(
            "active-inter",
            exhaustive_active_intersection(
                args.max_n,
                args.max_len,
                args.seconds,
                args.progress_every,
            ),
        )


if __name__ == "__main__":
    main()
