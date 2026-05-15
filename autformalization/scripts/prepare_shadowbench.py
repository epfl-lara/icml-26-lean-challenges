#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.request
from pathlib import Path
from typing import Any


DATASET_URL = "https://huggingface.co/datasets/DicoTiar/ShadowBench/resolve/main/test.jsonl"
DATASET_README_URL = "https://huggingface.co/datasets/DicoTiar/ShadowBench/raw/main/README.md"
DEFAULT_LEAN_TOOLCHAIN = "leanprover/lean4:v4.28.0"
DEFAULT_MATHLIB_REV = "v4.28.0"

ROOT = Path(__file__).resolve().parents[1]
DATA_DIR = ROOT / "data"
PROBLEMS_DIR = ROOT / "problems"


def write_text(path: Path, content: str) -> bool:
    path.parent.mkdir(parents=True, exist_ok=True)
    old = path.read_text(encoding="utf-8") if path.exists() else None
    if old == content:
        return False
    path.write_text(content, encoding="utf-8")
    return True


def fetch(url: str) -> str:
    with urllib.request.urlopen(url, timeout=60) as response:
        return response.read().decode("utf-8")


def load_rows(refresh: bool) -> list[dict[str, Any]]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    dataset_path = DATA_DIR / "test.jsonl"
    readme_path = DATA_DIR / "README.md"
    if refresh or not dataset_path.exists():
        write_text(dataset_path, fetch(DATASET_URL))
    if refresh or not readme_path.exists():
        write_text(readme_path, fetch(DATASET_README_URL))

    rows: list[dict[str, Any]] = []
    for line_no, line in enumerate(dataset_path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as exc:
            raise SystemExit(f"{dataset_path}:{line_no}: invalid JSON: {exc}") from exc
        for field in ("idx", "informal_proof", "formalization_rules", "imports"):
            if field not in row:
                raise SystemExit(f"{dataset_path}:{line_no}: missing field {field!r}")
        rows.append(row)
    return rows


def safe_package_name(idx: str) -> str:
    parts = re.findall(r"[A-Za-z0-9]+", idx.lower())
    suffix = "_".join(parts)[:70].strip("_") or "problem"
    return f"shadowbench_{suffix}"


def tex_escape(value: str) -> str:
    replacements = {
        "\\": r"\textbackslash{}",
        "{": r"\{",
        "}": r"\}",
        "#": r"\#",
        "$": r"\$",
        "%": r"\%",
        "&": r"\&",
        "_": r"\_",
        "^": r"\^{}",
        "~": r"\~{}",
    }
    return "".join(replacements.get(ch, ch) for ch in value)


def normalize_imports(raw_imports: list[str]) -> list[str]:
    imports: list[str] = []
    seen: set[str] = set()
    for raw in raw_imports:
        line = str(raw or "").strip()
        if not line:
            continue
        if not line.startswith("import "):
            line = f"import {line}"
        if line not in seen:
            seen.add(line)
            imports.append(line)
    if not imports:
        imports.append("import Mathlib")
    return imports


def leading_rule_code(rules: str) -> str:
    before_comment = str(rules or "").split("/-", 1)[0]
    lines: list[str] = []
    for raw in before_comment.splitlines():
        line = raw.strip()
        if not line or line.startswith("--") or line.startswith("import "):
            continue
        lines.append(line)
    return "\n".join(lines)


def expected_names(rules: str) -> list[str]:
    names: list[str] = []
    for name in re.findall(r"`([A-Za-z_][A-Za-z0-9_'.]*)`", str(rules or "")):
        if name not in names:
            names.append(name)
    return names


def render_source_tex(row: dict[str, Any]) -> str:
    idx = str(row["idx"])
    body = str(row["informal_proof"]).rstrip()
    return (
        "\\documentclass{article}\n"
        "\\usepackage{amsmath,amssymb,amsthm,mathtools}\n"
        "\\newtheorem{theorem}{Theorem}\n"
        "\\newtheorem{lemma}{Lemma}\n"
        "\\newtheorem{proposition}{Proposition}\n"
        "\\newtheorem{corollary}{Corollary}\n"
        "\\newtheorem{definition}{Definition}\n"
        "\\newtheorem{example}{Example}\n"
        f"\\title{{ShadowBench {tex_escape(idx)}}}\n"
        "\\begin{document}\n"
        "\\maketitle\n"
        f"% Problem id: {idx}\n"
        "% Companion instructions: docs/instructions.md\n"
        "% Lean target: ShadowBench/Source/Main.lean\n\n"
        f"{body}\n"
        "\\end{document}\n"
    )


def render_instructions(row: dict[str, Any]) -> str:
    idx = str(row["idx"])
    imports = normalize_imports(list(row["imports"]))
    names = expected_names(str(row["formalization_rules"]))
    names_section = "\n".join(f"- `{name}`" for name in names) if names else "- [none detected]"
    return (
        f"# ShadowBench Instructions: `{idx}`\n\n"
        "## Source\n\n"
        "- Formalize `docs/source.tex`.\n"
        "- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.\n"
        "- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.\n\n"
        "## Allowed Imports\n\n"
        "Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.\n\n"
        "```lean\n"
        + "\n".join(imports)
        + "\n```\n\n"
        "## Expected Declaration Names\n\n"
        f"{names_section}\n\n"
        "## Formalization Rules\n\n"
        "```text\n"
        + str(row["formalization_rules"]).rstrip()
        + "\n```\n\n"
        "## Workflow Rules\n\n"
        "- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.\n"
        "- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.\n"
        "- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.\n"
        "- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.\n"
        "- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.\n"
    )


def render_lakefile(package_name: str, *, mathlib_rev: str) -> str:
    return (
        f'name = "{package_name}"\n'
        'version = "0.1.0"\n'
        'keywords = ["math", "autoformalization", "shadowbench"]\n'
        'defaultTargets = ["ShadowBench"]\n\n'
        "[leanOptions]\n"
        "pp.unicode.fun = true\n"
        "relaxedAutoImplicit = false\n"
        "weak.linter.mathlibStandardSet = true\n"
        "maxSynthPendingDepth = 3\n"
        "linter.style.whitespace = false\n"
        "linter.style.cdot = false\n\n"
        "[[require]]\n"
        'name = "mathlib"\n'
        'scope = "leanprover-community"\n'
        f'rev = "{mathlib_rev}"\n\n'
        "[[lean_lib]]\n"
        'name = "ShadowBench"\n'
    )


def render_project_yaml() -> str:
    return (
        "schema_version: 1\n"
        "name: ShadowBench\n"
        "kind: lean4\n"
        "lean_root: .\n"
        "created_at: '2026-05-15T00:00:00+00:00'\n"
        "paths:\n"
        "  runtime: .epflemma/runtime\n"
        "  cache: .epflemma/cache\n"
        "  workflows: .epflemma/workflows\n"
        "source:\n"
        "  mode: shadowbench\n"
        "  template_source: DicoTiar/ShadowBench\n"
        "blueprint:\n"
        "  markers:\n"
        "  - lean-toolchain\n"
        "  - lakefile.toml\n"
    )


def render_main_lean(row: dict[str, Any]) -> str:
    idx = str(row["idx"])
    imports = normalize_imports(list(row["imports"]))
    rule_code = leading_rule_code(str(row["formalization_rules"]))
    chunks = ["\n".join(imports)]
    if rule_code:
        chunks.append(rule_code)
    chunks.append(
        "/-\n"
        f"ShadowBench problem: {idx}\n"
        "Source: docs/source.tex\n"
        "Instructions: docs/instructions.md\n"
        "Blueprint: ShadowBench/Source/Blueprint.md\n\n"
        "Replace this scaffold with the required declarations and proofs.\n"
        "-/\n"
    )
    return "\n\n".join(chunks).rstrip() + "\n"


def render_blueprint(row: dict[str, Any]) -> str:
    idx = str(row["idx"])
    imports = normalize_imports(list(row["imports"]))
    names = expected_names(str(row["formalization_rules"]))
    names_text = "\n".join(f"- `{name}`" for name in names) if names else "- [pending manual extraction]"
    return (
        f"# Formalization Blueprint: `{idx}`\n\n"
        "- Source: `docs/source.tex`\n"
        "- Instructions: `docs/instructions.md`\n"
        "- Target Lean entry file: `ShadowBench/Source/Main.lean`\n"
        "- Status: scaffold created; replace pending entries during formalization.\n\n"
        "## Import Plan\n\n"
        "```lean\n"
        + "\n".join(imports)
        + "\n```\n\n"
        "## Required Names\n\n"
        f"{names_text}\n\n"
        "## Statement Inventory\n\n"
        "For each source theorem, lemma, definition, or named item:\n\n"
        "- Planned Lean declaration: _pending_\n"
        "- Source locator: `docs/source.tex`\n"
        "- Dependencies: _pending_\n"
        "- Formal statement review: _pending_\n"
        "- Source qualifiers: _pending_\n"
        "- Lean coverage: _pending_\n"
        "- Scope changes: _pending_\n"
        "- Statement verification status: _pending_\n"
        "- Source proof / prover notes: _pending_\n\n"
        "## Formalization Rules\n\n"
        "```text\n"
        + str(row["formalization_rules"]).rstrip()
        + "\n```\n"
    )


def render_metadata(row: dict[str, Any]) -> str:
    return json.dumps(row, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def render_history_template(row: dict[str, Any]) -> str:
    idx = str(row["idx"])
    payload = [
        {
            "role": "system",
            "content": f"Replace this template with the actual model conversation used for ShadowBench problem {idx}.",
        }
    ]
    return json.dumps(payload, indent=2, ensure_ascii=False) + "\n"


def materialize_problem(
    row: dict[str, Any],
    *,
    lean_toolchain: str,
    mathlib_rev: str,
    overwrite_lean: bool,
    overwrite_blueprint: bool,
) -> dict[str, Any]:
    idx = str(row["idx"])
    problem_dir = PROBLEMS_DIR / idx
    package_name = safe_package_name(idx)
    changed = 0

    files = {
        "docs/source.tex": render_source_tex(row),
        "docs/instructions.md": render_instructions(row),
        "docs/metadata.json": render_metadata(row),
        "docs/llm_history.template.json": render_history_template(row),
        "lakefile.toml": render_lakefile(package_name, mathlib_rev=mathlib_rev),
        "lean-toolchain": f"{lean_toolchain}\n",
        ".epflemma/project.yaml": render_project_yaml(),
        "ShadowBench.lean": "import ShadowBench.Source.Main\n",
    }
    for relative, content in files.items():
        if write_text(problem_dir / relative, content):
            changed += 1

    main_path = problem_dir / "ShadowBench/Source/Main.lean"
    if overwrite_lean or not main_path.exists():
        if write_text(main_path, render_main_lean(row)):
            changed += 1

    blueprint_path = problem_dir / "ShadowBench/Source/Blueprint.md"
    if overwrite_blueprint or not blueprint_path.exists():
        if write_text(blueprint_path, render_blueprint(row)):
            changed += 1

    return {"idx": idx, "path": str(problem_dir.relative_to(ROOT)), "changed_files": changed}


def write_index(
    rows: list[dict[str, Any]],
    generated: list[dict[str, Any]],
    *,
    lean_toolchain: str,
    mathlib_rev: str,
) -> None:
    by_area: dict[str, int] = {}
    by_level: dict[str, int] = {}
    for row in rows:
        idx = str(row["idx"])
        parts = idx.split("/")
        if parts:
            by_area[parts[0]] = by_area.get(parts[0], 0) + 1
        if len(parts) > 1:
            by_level[parts[1]] = by_level.get(parts[1], 0) + 1
    payload = {
        "dataset": "DicoTiar/ShadowBench",
        "dataset_url": DATASET_URL,
        "lean_toolchain": lean_toolchain,
        "mathlib_rev": mathlib_rev,
        "problem_count": len(rows),
        "by_area": dict(sorted(by_area.items())),
        "by_level": dict(sorted(by_level.items())),
        "problems": generated,
    }
    write_text(DATA_DIR / "problem_index.json", json.dumps(payload, indent=2, sort_keys=True) + "\n")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Prepare one Lean project per ShadowBench row.")
    parser.add_argument("--refresh", action="store_true", help="redownload the dataset files")
    parser.add_argument(
        "--lean-toolchain",
        default=DEFAULT_LEAN_TOOLCHAIN,
        help=f"Lean toolchain to write into each project (default: {DEFAULT_LEAN_TOOLCHAIN})",
    )
    parser.add_argument(
        "--mathlib-rev",
        default=DEFAULT_MATHLIB_REV,
        help=f"mathlib revision to write into each lakefile.toml (default: {DEFAULT_MATHLIB_REV})",
    )
    parser.add_argument("--overwrite-lean", action="store_true", help="overwrite existing Main.lean scaffolds")
    parser.add_argument("--overwrite-blueprint", action="store_true", help="overwrite existing Blueprint.md scaffolds")
    parser.add_argument("--limit", type=int, default=0, help="materialize only the first N rows")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    rows = load_rows(refresh=args.refresh)
    if args.limit:
        rows = rows[: args.limit]
    generated = [
        materialize_problem(
            row,
            lean_toolchain=args.lean_toolchain,
            mathlib_rev=args.mathlib_rev,
            overwrite_lean=args.overwrite_lean,
            overwrite_blueprint=args.overwrite_blueprint,
        )
        for row in rows
    ]
    write_index(rows, generated, lean_toolchain=args.lean_toolchain, mathlib_rev=args.mathlib_rev)
    changed = sum(item["changed_files"] for item in generated)
    print(f"Prepared {len(generated)} ShadowBench problem projects; changed files: {changed}")
    print(f"Index: {DATA_DIR / 'problem_index.json'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
