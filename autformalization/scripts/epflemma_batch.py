#!/usr/bin/env python3
from __future__ import annotations

import argparse
import datetime as dt
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
INDEX_PATH = ROOT / "data/problem_index.json"
RUNS_DIR = ROOT / "runs"
STATE_PATH = RUNS_DIR / "state.json"
ONE_PROBLEM_SCRIPT = ROOT / "scripts/epflemma_formalize.sh"


def utc_now() -> str:
    return dt.datetime.now(dt.UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def safe_name(value: str) -> str:
    return "".join(ch if ch.isalnum() or ch in "._-" else "-" for ch in value).strip("-") or "problem"


def load_index() -> list[dict[str, Any]]:
    if not INDEX_PATH.is_file():
        raise SystemExit(f"Missing index: {INDEX_PATH}. Run scripts/prepare_shadowbench.py first.")
    payload = json.loads(INDEX_PATH.read_text(encoding="utf-8"))
    return list(payload.get("problems", []) or [])


def split_csv(values: Iterable[str]) -> set[str]:
    result: set[str] = set()
    for value in values:
        for item in str(value).split(","):
            item = item.strip()
            if item:
                result.add(item)
    return result


def filter_problems(problems: list[dict[str, Any]], args: argparse.Namespace) -> list[dict[str, Any]]:
    areas = split_csv(args.area or [])
    levels = split_csv(args.level or [])
    only = split_csv(args.only or [])
    skip_until = str(args.start_after or "").strip()
    selected: list[dict[str, Any]] = []
    skipping = bool(skip_until)

    for item in problems:
        idx = str(item.get("idx", ""))
        parts = idx.split("/")
        area = parts[0] if len(parts) > 0 else ""
        level = parts[1] if len(parts) > 1 else ""
        slug = parts[-1] if parts else idx
        if areas and area not in areas:
            continue
        if levels and level not in levels:
            continue
        if only and idx not in only and slug not in only:
            continue
        if skipping:
            if idx == skip_until or slug == skip_until:
                skipping = False
            continue
        selected.append(item)

    if args.limit:
        selected = selected[: args.limit]
    return selected


def load_state() -> dict[str, Any]:
    if not STATE_PATH.is_file():
        return {}
    return json.loads(STATE_PATH.read_text(encoding="utf-8"))


def write_state(state: dict[str, Any]) -> None:
    STATE_PATH.parent.mkdir(parents=True, exist_ok=True)
    STATE_PATH.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def state_key(idx: str, phase: str) -> str:
    return f"{phase}:{idx}"


def command_for(problem: dict[str, Any], args: argparse.Namespace) -> list[str]:
    problem_dir = ROOT / str(problem["path"])
    command = [
        str(ONE_PROBLEM_SCRIPT),
        "--problem-dir",
        str(problem_dir),
        "--phase",
        args.phase,
        "--provider",
        args.provider,
    ]
    if args.lake_update:
        command.append("--lake-update")
    if args.check_before:
        command.append("--check-before")
    if args.check_after:
        command.append("--check-after")
    if args.no_project_init:
        command.append("--no-project-init")
    return command


def append_jsonl(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(payload, sort_keys=True) + "\n")


def run_problem(
    problem: dict[str, Any],
    args: argparse.Namespace,
    *,
    run_dir: Path,
    state: dict[str, Any],
) -> dict[str, Any]:
    idx = str(problem["idx"])
    key = state_key(idx, args.phase)
    if args.skip_success and state.get(key, {}).get("status") == "success":
        return {
            "idx": idx,
            "phase": args.phase,
            "status": "skipped",
            "reason": "previous success",
            "started_at": utc_now(),
            "ended_at": utc_now(),
        }

    log_path = run_dir / "logs" / f"{safe_name(idx)}.log"
    result_path = run_dir / "results.jsonl"
    command = command_for(problem, args)
    started = time.monotonic()
    started_at = utc_now()
    print(f"[{idx}] phase={args.phase} log={log_path.relative_to(ROOT)}", flush=True)

    if args.dry_run:
        print("+ " + " ".join(command))
        result = {
            "idx": idx,
            "phase": args.phase,
            "status": "dry-run",
            "command": command,
            "started_at": started_at,
            "ended_at": utc_now(),
            "log": str(log_path.relative_to(ROOT)),
        }
        append_jsonl(result_path, result)
        return result

    log_path.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open("w", encoding="utf-8") as log:
        log.write(f"# idx: {idx}\n")
        log.write(f"# phase: {args.phase}\n")
        log.write(f"# started_at: {started_at}\n")
        log.write("+ " + " ".join(command) + "\n\n")
        log.flush()
        process = subprocess.run(
            command,
            cwd=str(ROOT),
            stdout=log,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
    elapsed = round(time.monotonic() - started, 3)
    status = "success" if process.returncode == 0 else "failed"
    result = {
        "idx": idx,
        "path": problem.get("path", ""),
        "phase": args.phase,
        "status": status,
        "returncode": process.returncode,
        "elapsed_s": elapsed,
        "started_at": started_at,
        "ended_at": utc_now(),
        "log": str(log_path.relative_to(ROOT)),
    }
    append_jsonl(result_path, result)
    state[key] = result
    write_state(state)
    print(f"[{idx}] {status} ({elapsed}s)", flush=True)
    return result


def cmd_list(args: argparse.Namespace) -> int:
    problems = filter_problems(load_index(), args)
    for item in problems:
        print(item["idx"])
    print(f"# count={len(problems)}", file=sys.stderr)
    return 0


def cmd_status(args: argparse.Namespace) -> int:
    state = load_state()
    problems = filter_problems(load_index(), args)
    counts: dict[str, int] = {}
    for item in problems:
        idx = str(item["idx"])
        found = False
        for phase in ("formalize", "prove", "both", "check"):
            entry = state.get(state_key(idx, phase))
            if not entry:
                continue
            found = True
            status = str(entry.get("status", "unknown"))
            counts[status] = counts.get(status, 0) + 1
            if args.verbose:
                print(f"{idx}\t{phase}\t{status}\t{entry.get('log', '')}")
        if not found:
            counts["not-run"] = counts.get("not-run", 0) + 1
            if args.verbose:
                print(f"{idx}\t-\tnot-run\t")
    for key in sorted(counts):
        print(f"{key}: {counts[key]}")
    return 0


def cmd_run(args: argparse.Namespace) -> int:
    problems = filter_problems(load_index(), args)
    if not problems:
        raise SystemExit("No problems selected.")
    run_id = args.run_id or f"{dt.datetime.now(dt.UTC).strftime('%Y%m%dT%H%M%SZ')}-{args.phase}"
    run_dir = RUNS_DIR / run_id
    run_dir.mkdir(parents=True, exist_ok=True)
    state = load_state()
    failures = 0
    for problem in problems:
        result = run_problem(problem, args, run_dir=run_dir, state=state)
        if result.get("status") == "failed":
            failures += 1
            if args.fail_fast:
                break
    print(f"Run directory: {run_dir}")
    print(f"Selected: {len(problems)}; failures: {failures}")
    return 1 if failures else 0


def add_selection_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--area", action="append", help="area filter; repeat or comma-separate")
    parser.add_argument("--level", action="append", help="level filter such as L2; repeat or comma-separate")
    parser.add_argument("--only", action="append", help="exact idx or final slug; repeat or comma-separate")
    parser.add_argument("--start-after", help="skip selected problems through this idx/slug")
    parser.add_argument("--limit", type=int, default=0, help="maximum number of selected problems")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Batch EPFLemma runner for ShadowBench problem projects.")
    subparsers = parser.add_subparsers(dest="command", required=True)

    list_parser = subparsers.add_parser("list", help="list selected problem ids")
    add_selection_args(list_parser)
    list_parser.set_defaults(func=cmd_list)

    status_parser = subparsers.add_parser("status", help="summarize batch run state")
    add_selection_args(status_parser)
    status_parser.add_argument("--verbose", action="store_true", help="print per-problem status lines")
    status_parser.set_defaults(func=cmd_status)

    run_parser = subparsers.add_parser("run", help="run EPFLemma on selected problems")
    add_selection_args(run_parser)
    run_parser.add_argument("--phase", choices=["formalize", "prove", "both", "check"], default="formalize")
    run_parser.add_argument("--provider", default="codex")
    run_parser.add_argument("--run-id", help="run directory name under autformalization/runs")
    run_parser.add_argument("--skip-success", action="store_true", help="skip problems previously successful for this phase")
    run_parser.add_argument("--fail-fast", action="store_true", help="stop after first failure")
    run_parser.add_argument("--dry-run", action="store_true", help="print commands without executing them")
    run_parser.add_argument("--lake-update", action="store_true", help="run lake update before each problem")
    run_parser.add_argument("--check-before", action="store_true", help="run Lean before EPFLemma")
    run_parser.add_argument("--check-after", action="store_true", help="run Lean after EPFLemma")
    run_parser.add_argument("--no-project-init", action="store_true", help="skip epflemma project init")
    run_parser.set_defaults(func=cmd_run)

    return parser.parse_args()


def main() -> int:
    args = parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
