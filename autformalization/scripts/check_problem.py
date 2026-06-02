#!/usr/bin/env python3
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PROBLEMS_DIR = ROOT / "problems"
TARGET = Path("ShadowBench/Source/Main.lean")


def find_problem(value: str) -> Path:
    raw = Path(value)
    candidates = [
        raw,
        PROBLEMS_DIR / value,
        ROOT / value,
    ]
    for candidate in candidates:
        path = candidate.expanduser()
        if path.is_dir() and (path / TARGET).is_file():
            return path.resolve()
    matches = sorted(PROBLEMS_DIR.rglob(raw.name))
    for match in matches:
        if match.is_dir() and (match / TARGET).is_file():
            return match.resolve()
    raise SystemExit(f"Could not find problem project for {value!r}")


def run(command: list[str], cwd: Path) -> int:
    print(f"+ {' '.join(command)}", flush=True)
    return subprocess.run(command, cwd=str(cwd), check=False).returncode


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run Lean on one ShadowBench problem project.")
    parser.add_argument("problem", help="problem idx or project directory")
    parser.add_argument("--update", action="store_true", help="run lake update before checking")
    parser.add_argument("--target", default=str(TARGET), help="Lean file to check inside the project")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    project = find_problem(args.problem)
    target = Path(args.target)
    if args.update:
        code = run(["lake", "update"], project)
        if code != 0:
            return code
    return run(["lake", "env", "lean", str(target)], project)


if __name__ == "__main__":
    sys.exit(main())
