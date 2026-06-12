#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DATASET_PATH = ROOT / "data/test.jsonl"
PROBLEMS_DIR = ROOT / "problems"
DEFAULT_OUTPUT = ROOT / "submission/shadowbench_submission.jsonl"
TARGET = Path("ShadowBench/Source/Main.lean")
LOCAL_SCAFFOLD_NAMESPACE = "ShadowBench.Source"


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


def lean_ident(part: str, *, style: str) -> str:
    if style == "sanitized":
        ident = re.sub(r"[^A-Za-z0-9_']", "_", part)
        if not ident or ident[0].isdigit():
            ident = "_" + ident
        return ident
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", part):
        return part
    if "»" in part:
        raise SystemExit(f"Cannot quote namespace component containing closing guillemet: {part!r}")
    return f"«{part}»"


def submission_namespace(idx: str, *, style: str) -> str:
    parts = idx.split("/")
    if len(parts) != 3:
        raise SystemExit(f"Expected idx with three path components, got: {idx!r}")
    return ".".join(["ABM", *(lean_ident(part, style=style) for part in parts)])


def strip_local_imports(text: str) -> str:
    return "\n".join(
        line for line in text.splitlines() if not line.lstrip().startswith("import ")
    ).strip()


def unwrap_local_scaffold_namespace(text: str) -> str:
    kept: list[str] = []
    for line in text.splitlines():
        if line.strip() in {
            f"namespace {LOCAL_SCAFFOLD_NAMESPACE}",
            f"end {LOCAL_SCAFFOLD_NAMESPACE}",
        }:
            continue
        kept.append(line)
    return "\n".join(kept).strip()


def expected_names(row: dict[str, Any]) -> list[str]:
    rules = str(row.get("formalization_rules", ""))
    names: list[str] = []
    patterns = [
        r"The theorem must be named `([^`]+)`",
        r"The lemma must be named `([^`]+)`",
        r"The definition must be named `([^`]+)`",
        r"The Lean declaration must be named exactly:\s*(?:\n-\s*)?`([^`]+)`",
        r"must be named exactly:\s*(?:\n-\s*)?`([^`]+)`",
        r"must be named `([^`]+)`",
    ]
    for pattern in patterns:
        names.extend(re.findall(pattern, rules))
    seen: set[str] = set()
    result: list[str] = []
    for name in names:
        if name not in seen:
            result.append(name)
            seen.add(name)
    return result


def has_local_decl(text: str, expected: str) -> bool:
    boundary = r"(?![A-Za-z0-9_'.])"
    decl_kinds = r"(?:theorem|lemma|def|abbrev|structure|class|instance)"
    exact = re.escape(expected)
    if re.search(rf"(?m)^\s*(?:noncomputable\s+)?{decl_kinds}\s+{exact}{boundary}", text):
        return True
    if re.search(rf"(?m)^\s*alias\s+{exact}{boundary}", text):
        return True
    if "." not in expected:
        return False
    namespace, short = expected.rsplit(".", 1)
    short_re = re.escape(short)
    namespace_re = re.escape(namespace)
    has_namespace = re.search(rf"(?m)^\s*namespace\s+{namespace_re}\s*$", text) is not None
    if not has_namespace:
        return False
    if re.search(rf"(?m)^\s*(?:noncomputable\s+)?{decl_kinds}\s+{short_re}{boundary}", text):
        return True
    return re.search(rf"(?m)^\s*alias\s+{short_re}{boundary}", text) is not None


def bridge_imported_decls(body: str, row: dict[str, Any]) -> str:
    bridges: list[str] = []
    for name in expected_names(row):
        if has_local_decl(body, name):
            continue
        bridges.append(
            "/-- Submission bridge for an imported declaration with the required name. -/\n"
            f"abbrev {name} := _root_.{name}"
        )
    if not bridges:
        return body
    return body.rstrip() + "\n\n" + "\n\n".join(bridges)


def formal_proof_for_row(
    *,
    idx: str,
    row: dict[str, Any],
    lean_text: str,
    raw: bool,
    namespace_style: str,
    bridge_imported: bool,
) -> str:
    if raw:
        return lean_text
    body = strip_local_imports(lean_text)
    body = unwrap_local_scaffold_namespace(body)
    if bridge_imported:
        body = bridge_imported_decls(body, row)
    namespace = submission_namespace(idx, style=namespace_style)
    return f"namespace {namespace}\n\n{body.rstrip()}\n\nend {namespace}\n"


def imports_from_instructions(project: Path) -> list[str]:
    instructions = project / "docs/instructions.md"
    if not instructions.is_file():
        return []
    text = instructions.read_text(encoding="utf-8")
    match = re.search(r"## Allowed Imports.*?```lean\n(.*?)\n```", text, flags=re.S)
    if not match:
        return []
    imports: list[str] = []
    for raw in match.group(1).splitlines():
        line = raw.strip()
        if line and line.startswith("import ") and line not in imports:
            imports.append(line)
    return imports


def problem_import_block(row: dict[str, Any], project: Path) -> str:
    imports = row.get("imports", [])
    if isinstance(imports, str):
        lines = [line.strip() for line in imports.splitlines()]
    elif isinstance(imports, list):
        lines = [str(line).strip() for line in imports]
    else:
        lines = []
    lines = [line for line in lines if line]
    if not lines:
        lines = imports_from_instructions(project)
    return "\n".join(lines)


def check_formal_proof(project: Path, row: dict[str, Any], formal_proof: str, timeout: int) -> str:
    source = problem_import_block(row, project).rstrip() + "\n\n" + formal_proof
    completed = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=str(project),
        input=source,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )
    if completed.returncode != 0:
        return completed.stdout
    return ""


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Export ShadowBench Lean files to Codabench JSONL format.")
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT), help="output JSONL path")
    parser.add_argument("--strict-history", action="store_true", help="require docs/llm_history.json for every row")
    parser.add_argument("--only", action="append", default=[], help="export only this idx; repeatable")
    parser.add_argument("--raw", action="store_true", help="export raw Main.lean files without stripping/wrapping")
    parser.add_argument(
        "--namespace-style",
        choices=("quoted", "sanitized"),
        default="quoted",
        help="encoding for idx components that are not Lean identifiers",
    )
    parser.add_argument(
        "--no-bridge-imported",
        action="store_true",
        help="do not synthesize local abbreviations for expected names already provided by imports",
    )
    parser.add_argument("--check", action="store_true", help="compile each generated proof with the row imports")
    parser.add_argument("--check-timeout", type=int, default=120, help="per-row Lean check timeout in seconds")
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
            formal_proof = formal_proof_for_row(
                idx=idx,
                row=row,
                lean_text=lean_path.read_text(encoding="utf-8"),
                raw=args.raw,
                namespace_style=args.namespace_style,
                bridge_imported=not args.no_bridge_imported,
            )
            if args.check:
                check_output = check_formal_proof(project, row, formal_proof, timeout=args.check_timeout)
                if check_output:
                    raise SystemExit(f"Generated submission snippet failed for {idx}:\n{check_output}")
            payload = {
                "idx": idx,
                "formal_proof": formal_proof,
                "llm_history": read_history(project, idx, strict=args.strict_history),
            }
            handle.write(json.dumps(payload, ensure_ascii=False) + "\n")
            count += 1
    print(f"Wrote {count} rows to {output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
