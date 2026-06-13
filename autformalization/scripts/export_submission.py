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
OFFICIAL_IMPORTS_PATH = ROOT / "data/dicotiar_test_imports.json"
PROBLEMS_DIR = ROOT / "problems"
DEFAULT_OUTPUT = ROOT / "submission/shadowbench_submission.jsonl"
TARGET = Path("ShadowBench/Source/Main.lean")
LOCAL_SCAFFOLD_NAMESPACE = "ShadowBench.Source"
ROOT_NAMESPACE_BRIDGES = {
    "AlgebraicGeometry": "_root_.AlgebraicGeometry",
}
FORBIDDEN_SNIPPET_PATTERNS = [
    ("placeholder proof", re.compile(r"\b(?:sorry|admit)\b")),
    ("vacuous True proposition", re.compile(r"\bProp\s*:=\s*True\b|^\s*(?:theorem|lemma)\s+\S+[^:\n]*:\s*True\s*:=", re.M)),
    ("axiom declaration", re.compile(r"(?m)^\s*(?:noncomputable\s+)?axiom\s+")),
    ("constant declaration", re.compile(r"(?m)^\s*(?:noncomputable\s+)?constant(?:s)?\s+")),
    ("opaque declaration", re.compile(r"(?m)^\s*(?:noncomputable\s+)?opaque\s+")),
    ("unsafe code", re.compile(r"\bunsafe\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
]
STRICT_CHECK_PREAMBLE = "set_option autoImplicit false\n"


def load_rows() -> list[dict[str, Any]]:
    if not DATASET_PATH.is_file():
        raise SystemExit(f"Dataset not found: {DATASET_PATH}. Run scripts/prepare_shadowbench.py first.")
    rows: list[dict[str, Any]] = []
    for line in DATASET_PATH.read_text(encoding="utf-8").splitlines():
        if line.strip():
            rows.append(json.loads(line))
    return rows


def load_official_imports() -> dict[str, list[str]]:
    if not OFFICIAL_IMPORTS_PATH.is_file():
        return {}
    payload = json.loads(OFFICIAL_IMPORTS_PATH.read_text(encoding="utf-8"))
    imports_by_idx = payload.get("imports_by_idx", {})
    if not isinstance(imports_by_idx, dict):
        raise SystemExit(f"Invalid imports manifest: {OFFICIAL_IMPORTS_PATH}")
    result: dict[str, list[str]] = {}
    for idx, raw_imports in imports_by_idx.items():
        if not isinstance(raw_imports, list):
            raise SystemExit(f"Invalid imports list for {idx!r} in {OFFICIAL_IMPORTS_PATH}")
        result[str(idx)] = [str(item).strip() for item in raw_imports if str(item).strip()]
    return result


def canonical_idx(idx: str, official_imports: dict[str, list[str]]) -> str:
    """Return the official ShadowBench idx spelling when the local mirror differs only by case."""
    if idx in official_imports:
        return idx
    lower_idx = idx.lower()
    matches = [official_idx for official_idx in official_imports if official_idx.lower() == lower_idx]
    if len(matches) == 1:
        return matches[0]
    return idx


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


def rewrite_local_scaffold_references(text: str) -> str:
    return text.replace(f"{LOCAL_SCAFFOLD_NAMESPACE}.", "")


def add_root_namespace_bridges(text: str) -> str:
    lines: list[str] = []
    for line in text.splitlines():
        lines.append(line)
        stripped = line.strip()
        if not stripped.startswith("namespace "):
            continue
        namespace = stripped.removeprefix("namespace ").strip()
        root_namespace = ROOT_NAMESPACE_BRIDGES.get(namespace)
        if root_namespace is not None:
            lines.append(f"open {root_namespace}")
    return "\n".join(lines).strip()


def strip_lean_comments(text: str) -> str:
    result: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth == 0 and text.startswith("--", i):
            end = text.find("\n", i)
            if end == -1:
                break
            result.append("\n")
            i = end + 1
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth > 0:
            result.append("\n" if text[i] == "\n" else " ")
            i += 1
        else:
            result.append(text[i])
            i += 1
    return "".join(result)


def unclosed_sections(text: str) -> int:
    count = 0
    for line in strip_lean_comments(text).splitlines():
        stripped = line.strip()
        if re.match(r"^(?:noncomputable\s+)?section(?:\s|$)", stripped):
            count += 1
        elif re.match(r"^end(?:\s|$)", stripped) and count > 0:
            count -= 1
    return count


def lint_formal_proof(idx: str, formal_proof: str) -> list[str]:
    """Check competition-local rules that Lean compilation alone may not reject."""
    uncommented = strip_lean_comments(formal_proof)
    errors: list[str] = []
    for label, pattern in FORBIDDEN_SNIPPET_PATTERNS:
        match = pattern.search(uncommented)
        if match is None:
            continue
        line = uncommented.count("\n", 0, match.start()) + 1
        errors.append(f"{idx}: forbidden {label} near line {line}")
    return errors


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
    body = rewrite_local_scaffold_references(body)
    body = add_root_namespace_bridges(body)
    if bridge_imported:
        body = bridge_imported_decls(body, row)
    namespace = submission_namespace(idx, style=namespace_style)
    section_closers = "end\n" * unclosed_sections(body)
    return f"namespace {namespace}\n\n{body.rstrip()}\n\n{section_closers}end {namespace}\n"


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


def problem_import_block(
    row: dict[str, Any],
    project: Path,
    official_imports: dict[str, list[str]],
    *,
    require_official: bool = False,
) -> str:
    idx = canonical_idx(str(row["idx"]), official_imports)
    if idx in official_imports:
        return "\n".join(official_imports[idx])
    if require_official and official_imports:
        raise SystemExit(
            f"Missing official imports for {idx!r}; local data/test.jsonl is out of sync "
            f"with {OFFICIAL_IMPORTS_PATH}"
        )
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
    official_imports = load_official_imports()
    source = (
        problem_import_block(row, project, official_imports, require_official=True).rstrip()
        + "\n\n"
        + STRICT_CHECK_PREAMBLE
        + "\n"
        + formal_proof
    )
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
        help=argparse.SUPPRESS,
    )
    parser.add_argument(
        "--bridge-imported",
        action="store_true",
        help=(
            "debug only: synthesize local abbreviations for missing expected names from `_root_`; "
            "final submissions should declare every required name in Main.lean"
        ),
    )
    parser.add_argument(
        "--allow-official-mismatch",
        action="store_true",
        help="allow exporting rows whose idx set does not match the official DicoTiar import manifest",
    )
    parser.add_argument(
        "--allow-import-fallback",
        action="store_true",
        help="allow --check to fall back to local/instruction imports when official imports are missing",
    )
    parser.add_argument("--check", action="store_true", help="compile each generated proof with the row imports")
    parser.add_argument("--check-timeout", type=int, default=120, help="per-row Lean check timeout in seconds")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    rows = load_rows()
    official_imports = load_official_imports()
    only = set(args.only)
    selected_rows: list[dict[str, Any]] = []
    for row in rows:
        local_idx = str(row["idx"])
        idx = canonical_idx(local_idx, official_imports)
        if only and local_idx not in only and idx not in only:
            continue
        selected_rows.append(row)
    if official_imports and not args.allow_official_mismatch:
        selected_official = {canonical_idx(str(row["idx"]), official_imports) for row in selected_rows}
        missing_imports = sorted(idx for idx in selected_official if idx not in official_imports)
        missing_local = sorted(set(official_imports) - selected_official) if not only else []
        if missing_imports or missing_local:
            details: list[str] = [
                "Official idx/import mismatch. Refusing to export a final submission from out-of-sync data."
            ]
            if missing_imports:
                details.append("Rows without official imports:")
                details.extend(f"- {idx}" for idx in missing_imports)
            if missing_local:
                details.append("Official rows missing locally:")
                details.extend(f"- {idx}" for idx in missing_local)
            details.append("Use --allow-official-mismatch only for debugging non-final skeleton exports.")
            raise SystemExit("\n".join(details))
    output = Path(args.output).expanduser().resolve()
    output.parent.mkdir(parents=True, exist_ok=True)

    count = 0
    with output.open("w", encoding="utf-8") as handle:
        for row in selected_rows:
            local_idx = str(row["idx"])
            idx = canonical_idx(local_idx, official_imports)
            project = problem_dir(local_idx)
            lean_path = project / TARGET
            if not lean_path.is_file():
                raise SystemExit(f"Missing Lean target: {lean_path}")
            lean_text = lean_path.read_text(encoding="utf-8")
            unbridged_formal_proof = formal_proof_for_row(
                idx=idx,
                row=row,
                lean_text=lean_text,
                raw=args.raw,
                namespace_style=args.namespace_style,
                bridge_imported=False,
            )
            missing_expected = [
                name for name in expected_names(row) if not has_local_decl(unbridged_formal_proof, name)
            ]
            if missing_expected and not args.bridge_imported:
                raise SystemExit(
                    f"{idx}: required declaration(s) missing from {TARGET.as_posix()}: "
                    + ", ".join(missing_expected)
                    + "\nDo not rely on exporter-generated `_root_` bridges for final submissions."
                )
            formal_proof = formal_proof_for_row(
                idx=idx,
                row=row,
                lean_text=lean_text,
                raw=args.raw,
                namespace_style=args.namespace_style,
                bridge_imported=args.bridge_imported and not args.no_bridge_imported,
            )
            if args.check:
                lint_errors = lint_formal_proof(idx, formal_proof)
                if lint_errors:
                    raise SystemExit("\n".join(lint_errors))
                check_source = (
                    problem_import_block(
                        row,
                        project,
                        official_imports,
                        require_official=not args.allow_import_fallback,
                    ).rstrip()
                    + "\n\n"
                    + STRICT_CHECK_PREAMBLE
                    + "\n"
                    + formal_proof
                )
                completed = subprocess.run(
                    ["lake", "env", "lean", "--stdin"],
                    cwd=str(project),
                    input=check_source,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    timeout=args.check_timeout,
                    check=False,
                )
                check_output = completed.stdout if completed.returncode != 0 else ""
                if check_output:
                    raise SystemExit(f"Generated submission snippet failed for {idx}:\n{check_output}")
            payload = {
                "idx": idx,
                "formal_proof": formal_proof,
                "llm_history": read_history(project, local_idx, strict=args.strict_history),
            }
            handle.write(json.dumps(payload, ensure_ascii=False) + "\n")
            count += 1
    print(f"Wrote {count} rows to {output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
