#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib.util
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = Path(__file__).resolve().parent
EXPORTER_PATH = SCRIPT_DIR / "export_submission.py"
DEFAULT_OUTPUT_DIR = ROOT / "runs" / "rules-audit-latest"
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def load_exporter() -> Any:
    spec = importlib.util.spec_from_file_location("export_submission", EXPORTER_PATH)
    if spec is None or spec.loader is None:
        raise SystemExit(f"Could not import {EXPORTER_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


export = load_exporter()


def add_issue(
    issues: list[dict[str, Any]],
    *,
    idx: str,
    severity: str,
    kind: str,
    detail: str,
    path: str | None = None,
    **extra: Any,
) -> None:
    payload: dict[str, Any] = {
        "idx": idx,
        "severity": severity,
        "kind": kind,
        "detail": detail,
    }
    if path is not None:
        payload["path"] = path
    payload.update(extra)
    issues.append(payload)


def uncommented_import_lines(formal_proof: str) -> list[int]:
    lines: list[int] = []
    for line_no, line in enumerate(export.strip_lean_comments(formal_proof).splitlines(), start=1):
        if line.lstrip().startswith("import "):
            lines.append(line_no)
    return lines


def namespace_errors(idx: str, formal_proof: str, namespace: str) -> list[str]:
    stripped = [line.strip() for line in formal_proof.splitlines() if line.strip()]
    errors: list[str] = []
    if not stripped or stripped[0] != f"namespace {namespace}":
        errors.append(f"first nonempty line is not `namespace {namespace}`")
    if not stripped or stripped[-1] != f"end {namespace}":
        errors.append(f"last nonempty line is not `end {namespace}`")
    if "ShadowBench.Source" in export.strip_lean_comments(formal_proof):
        errors.append("formal_proof still references local scaffold namespace `ShadowBench.Source`")
    return errors


def declaration_header(formal_proof: str, name: str) -> str | None:
    decl_kinds = r"(?:theorem|lemma|def|abbrev|structure|class|instance)"
    boundary = r"(?![A-Za-z0-9_'.])"
    candidates = [name]
    if "." in name:
        candidates.append(name.rsplit(".", 1)[1])
    for candidate in candidates:
        pattern = re.compile(
            rf"(?ms)^\s*(?:noncomputable\s+)?{decl_kinds}\s+{re.escape(candidate)}{boundary}.*?(?:(?::=)|(?:\n\s*where\b)|(?:\n\n))"
        )
        match = pattern.search(formal_proof)
        if match is not None:
            return " ".join(match.group(0).split())
    return None


def run_lean(project: Path, source: str, timeout: int) -> tuple[int, str]:
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
    return completed.returncode, completed.stdout


def first_error(output: str) -> str:
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    for line in lines:
        if "error" in line.lower():
            return line
    return lines[0] if lines else "Lean failed without diagnostic output"


def axiom_commands(namespace: str, names: list[str]) -> str:
    return "\n".join(f"#print axioms {namespace}.{name}" for name in names)


def parse_axioms(output: str) -> set[str]:
    axioms: set[str] = set()
    for match in re.finditer(r"depends on axioms:\s*\[([^\]]*)\]", output):
        raw = match.group(1).strip()
        if not raw:
            continue
        axioms.update(item.strip() for item in raw.split(",") if item.strip())
    return axioms


def row_path(local_idx: str) -> Path:
    return export.problem_dir(local_idx) / export.TARGET


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Audit generated ShadowBench submissions against RULES.md.")
    parser.add_argument("--output-dir", default=str(DEFAULT_OUTPUT_DIR), help="directory for summary and issue files")
    parser.add_argument("--only", action="append", default=[], help="audit only this local or official idx")
    parser.add_argument("--compile", action="store_true", help="compile generated snippets under official imports")
    parser.add_argument("--axioms", action="store_true", help="after successful compile, run #print axioms for expected names")
    parser.add_argument("--timeout", type=int, default=120, help="per-row Lean timeout")
    parser.add_argument(
        "--allow-official-mismatch",
        action="store_true",
        help="do not flag local/official idx set mismatches",
    )
    parser.add_argument(
        "--allow-import-fallback",
        action="store_true",
        help="allow local/instruction imports when official imports are missing",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    output_dir = Path(args.output_dir).expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    rows = export.load_rows()
    official_imports = export.load_official_imports()
    only = set(args.only)
    selected_rows: list[dict[str, Any]] = []
    for row in rows:
        local_idx = str(row["idx"])
        idx = export.canonical_idx(local_idx, official_imports)
        if only and local_idx not in only and idx not in only:
            continue
        selected_rows.append(row)

    issues: list[dict[str, Any]] = []
    canonical_counts = Counter(export.canonical_idx(str(row["idx"]), official_imports) for row in selected_rows)
    for idx, count in canonical_counts.items():
        if count > 1:
            add_issue(
                issues,
                idx=idx,
                severity="fatal",
                kind="duplicate_canonical_idx",
                detail=f"{count} local rows map to the same canonical idx",
            )

    selected_official = set(canonical_counts)
    if official_imports and not args.allow_official_mismatch:
        for idx in sorted(selected_official - set(official_imports)):
            add_issue(
                issues,
                idx=idx,
                severity="fatal",
                kind="missing_official_imports",
                detail="Local row is not present in the official DicoTiar import manifest.",
            )
        if not only:
            local_dirs = {
                path.relative_to(export.PROBLEMS_DIR).as_posix()
                for path in export.PROBLEMS_DIR.glob("*/*/*")
                if path.is_dir()
            }
            canonical_dirs = {export.canonical_idx(idx, official_imports) for idx in local_dirs}
            for idx in sorted(set(official_imports) - canonical_dirs):
                add_issue(
                    issues,
                    idx=idx,
                    severity="fatal",
                    kind="missing_local_problem_for_official_idx",
                    detail="Official DicoTiar row has no local problem directory.",
                )

    compile_pass = 0
    compile_fail = 0
    compile_skip = 0
    axiom_checked = 0

    for row in selected_rows:
        local_idx = str(row["idx"])
        idx = export.canonical_idx(local_idx, official_imports)
        project = export.problem_dir(local_idx)
        lean_path = project / export.TARGET
        path = lean_path.relative_to(ROOT).as_posix()
        namespace = export.submission_namespace(idx, style="quoted")
        expected = export.expected_names(row)
        lean_text = lean_path.read_text(encoding="utf-8")
        unbridged_formal_proof = export.formal_proof_for_row(
            idx=idx,
            row=row,
            lean_text=lean_text,
            raw=False,
            namespace_style="quoted",
            bridge_imported=False,
        )
        formal_proof = unbridged_formal_proof

        for line in uncommented_import_lines(formal_proof):
            add_issue(
                issues,
                idx=idx,
                severity="fatal",
                kind="formal_proof_contains_import",
                path=path,
                detail="formal_proof contains an import line; evaluator supplies imports separately.",
                line=line,
            )
        for detail in namespace_errors(idx, formal_proof, namespace):
            add_issue(
                issues,
                idx=idx,
                severity="fatal",
                kind="namespace_wrapper",
                path=path,
                detail=detail,
            )
        for detail in export.lint_formal_proof(idx, formal_proof):
            add_issue(
                issues,
                idx=idx,
                severity="fatal",
                kind="forbidden_construct",
                path=path,
                detail=detail,
            )
        for name in expected:
            if not export.has_local_decl(unbridged_formal_proof, name):
                add_issue(
                    issues,
                    idx=idx,
                    severity="fatal",
                    kind="missing_local_expected_declaration",
                    path=path,
                    detail=(
                        f"`{name}` is not declared in {export.TARGET.as_posix()}; "
                        "do not rely on exporter-generated `_root_` bridges for required declarations."
                    ),
                )
                continue
            header = declaration_header(formal_proof, name)
            if header is not None and "Mechanism" in header:
                add_issue(
                    issues,
                    idx=idx,
                    severity="fatal",
                    kind="mechanism_assumption_in_statement",
                    path=path,
                    detail=f"Required declaration `{name}` has a `*Mechanism` hypothesis in its public statement.",
                    header=header,
                )

        imports_available = idx in official_imports
        if not imports_available and not args.allow_import_fallback:
            if args.compile:
                compile_skip += 1
            continue

        if args.compile:
            import_block = export.problem_import_block(
                row,
                project,
                official_imports,
                require_official=not args.allow_import_fallback,
            )
            source = import_block.rstrip() + "\n\n" + export.STRICT_CHECK_PREAMBLE + "\n" + formal_proof
            try:
                returncode, output = run_lean(project, source, timeout=args.timeout)
            except subprocess.TimeoutExpired:
                compile_fail += 1
                add_issue(
                    issues,
                    idx=idx,
                    severity="fatal",
                    kind="compile_timeout",
                    path=path,
                    detail=f"Lean timed out after {args.timeout}s under official imports.",
                )
                continue
            if returncode != 0:
                compile_fail += 1
                add_issue(
                    issues,
                    idx=idx,
                    severity="fatal",
                    kind="compile_failed",
                    path=path,
                    detail=first_error(output),
                    output_tail=output[-4000:],
                )
                continue
            compile_pass += 1

            if args.axioms and expected:
                axiom_source = source + "\n\n" + axiom_commands(namespace, expected) + "\n"
                try:
                    ax_returncode, ax_output = run_lean(project, axiom_source, timeout=args.timeout)
                except subprocess.TimeoutExpired:
                    add_issue(
                        issues,
                        idx=idx,
                        severity="fatal",
                        kind="axiom_check_timeout",
                        path=path,
                        detail=f"`#print axioms` timed out after {args.timeout}s.",
                    )
                    continue
                if ax_returncode != 0:
                    add_issue(
                        issues,
                        idx=idx,
                        severity="fatal",
                        kind="axiom_check_failed",
                        path=path,
                        detail=first_error(ax_output),
                        output_tail=ax_output[-4000:],
                    )
                    continue
                axiom_checked += 1
                used_axioms = parse_axioms(ax_output)
                extra_axioms = sorted(used_axioms - ALLOWED_AXIOMS)
                if extra_axioms:
                    add_issue(
                        issues,
                        idx=idx,
                        severity="fatal",
                        kind="forbidden_axiom_dependency",
                        path=path,
                        detail="Declaration depends on axioms outside the competition whitelist.",
                        axioms=extra_axioms,
                    )

    summary: dict[str, Any] = {
        "generated_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "local_dataset": "data/test.jsonl",
        "official_import_manifest": export.OFFICIAL_IMPORTS_PATH.relative_to(ROOT).as_posix(),
        "selected_rows": len(selected_rows),
        "official_import_rows": len(official_imports),
        "issue_count": len(issues),
        "fatal_issue_count": sum(1 for issue in issues if issue["severity"] == "fatal"),
        "warning_issue_count": sum(1 for issue in issues if issue["severity"] == "warning"),
        "issues_by_kind": dict(Counter(issue["kind"] for issue in issues)),
        "compile_enabled": args.compile,
        "compile_pass": compile_pass,
        "compile_fail": compile_fail,
        "compile_skip": compile_skip,
        "axiom_check_enabled": args.axioms,
        "axiom_checked": axiom_checked,
    }

    (output_dir / "issues.jsonl").write_text(
        "".join(json.dumps(issue, ensure_ascii=False) + "\n" for issue in issues),
        encoding="utf-8",
    )
    (output_dir / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    by_kind: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for issue in issues:
        by_kind[issue["kind"]].append(issue)
    lines = [
        "# ShadowBench Submission Rules Audit",
        "",
        f"- Generated: `{summary['generated_at_utc']}`",
        f"- Selected rows: `{summary['selected_rows']}`",
        f"- Official import rows: `{summary['official_import_rows']}`",
        f"- Fatal issues: `{summary['fatal_issue_count']}`",
        f"- Warnings: `{summary['warning_issue_count']}`",
        f"- Compile: `{compile_pass}` pass, `{compile_fail}` fail, `{compile_skip}` skipped",
        f"- Axiom checked rows: `{axiom_checked}`",
        "",
        "## Issues By Kind",
    ]
    for kind, count in sorted(summary["issues_by_kind"].items()):
        lines.append(f"- `{kind}`: {count}")
    for kind, kind_issues in sorted(by_kind.items()):
        lines.extend(["", f"## {kind}", ""])
        for issue in kind_issues[:80]:
            item = f"- `{issue['idx']}`: {issue['detail']}"
            if "path" in issue:
                item += f" ({issue['path']})"
            lines.append(item)
        if len(kind_issues) > 80:
            lines.append(f"- ... {len(kind_issues) - 80} more")
    (output_dir / "summary.md").write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"Wrote audit to {output_dir}")
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 1 if summary["fatal_issue_count"] else 0


if __name__ == "__main__":
    sys.exit(main())
