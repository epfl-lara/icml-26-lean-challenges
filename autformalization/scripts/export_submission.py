#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DATASET_PATH = ROOT / "data/test.jsonl"
PROBLEMS_DIR = ROOT / "problems"
DEFAULT_OUTPUT = ROOT / "submission/shadowbench_submission.jsonl"
TARGET = Path("ShadowBench/Source/Main.lean")


def load_rows() -> list[dict[str, Any]]:
    if not DATASET_PATH.is_file():
        raise SystemExit(f"Dataset not found: {DATASET_PATH}. Run scripts/prepare_shadowbench.py first.")
    rows: list[dict[str, Any]] = []
    for line in DATASET_PATH.read_text(encoding="utf-8").splitlines():
        if line.strip():
            rows.append(json.loads(line))
    return rows


def problem_dir(idx: str) -> Path:
    path = PROBLEMS_DIR / idx
    if not path.is_dir():
        raise SystemExit(f"Missing problem directory: {path}")
    return path


def read_history(project: Path, idx: str, strict: bool) -> list[dict[str, str]]:
    history_path = project / "docs/llm_history.json"
    if history_path.is_file():
        payload = json.loads(history_path.read_text(encoding="utf-8"))
        if (
            isinstance(payload, list)
            and payload
            and all(isinstance(item, dict) and item.get("role") and item.get("content") for item in payload)
        ):
            return [{"role": str(item["role"]), "content": str(item["content"])} for item in payload]
        raise SystemExit(f"Invalid llm_history payload: {history_path}")
    if strict:
        raise SystemExit(f"Missing required history file: {history_path}")
    return [
        {
            "role": "assistant",
            "content": f"Lean proof collected from {TARGET.as_posix()} for ShadowBench problem {idx}.",
        }
    ]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Export ShadowBench Lean files to Codabench JSONL format.")
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT), help="output JSONL path")
    parser.add_argument("--strict-history", action="store_true", help="require docs/llm_history.json for every row")
    parser.add_argument("--only", action="append", default=[], help="export only this idx; repeatable")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    rows = load_rows()
    only = set(args.only)
    output = Path(args.output).expanduser().resolve()
    output.parent.mkdir(parents=True, exist_ok=True)

    count = 0
    with output.open("w", encoding="utf-8") as handle:
        for row in rows:
            idx = str(row["idx"])
            if only and idx not in only:
                continue
            project = problem_dir(idx)
            lean_path = project / TARGET
            if not lean_path.is_file():
                raise SystemExit(f"Missing Lean target: {lean_path}")
            payload = {
                "idx": idx,
                "formal_proof": lean_path.read_text(encoding="utf-8"),
                "llm_history": read_history(project, idx, strict=args.strict_history),
            }
            handle.write(json.dumps(payload, ensure_ascii=False) + "\n")
            count += 1
    print(f"Wrote {count} rows to {output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
