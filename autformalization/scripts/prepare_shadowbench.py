#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import sys
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any


DEFAULT_DATASET_ID = "Lemmy00/ShadowBench-skeletons-prod"
DEFAULT_LEAN_TOOLCHAIN = "leanprover/lean4:v4.29.0"
DEFAULT_MATHLIB_REV = "v4.29.0"

HF_BASE = "https://huggingface.co"
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


def hf_headers(token: str = "") -> dict[str, str]:
    token = token or os.environ.get("HF_TOKEN", "")
    return {"Authorization": f"Bearer {token}"} if token else {}


def fetch_bytes(url: str, *, token: str = "") -> bytes:
    request = urllib.request.Request(url, headers=hf_headers(token))
    try:
        with urllib.request.urlopen(request, timeout=90) as response:
            return response.read()
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")[:500]
        raise SystemExit(f"Failed to fetch {url}: HTTP {exc.code}: {detail}") from exc


def fetch_text(url: str, *, token: str = "") -> str:
    return fetch_bytes(url, token=token).decode("utf-8")


def dataset_api_url(dataset_id: str) -> str:
    return f"{HF_BASE}/api/datasets/{dataset_id}"


def dataset_file_url(dataset_id: str, path: str) -> str:
    quoted = urllib.parse.quote(path, safe="/")
    return f"{HF_BASE}/datasets/{dataset_id}/resolve/main/{quoted}"


def dataset_raw_url(dataset_id: str, path: str) -> str:
    quoted = urllib.parse.quote(path, safe="/")
    return f"{HF_BASE}/datasets/{dataset_id}/raw/main/{quoted}"


def load_dataset_metadata(dataset_id: str, *, token: str = "") -> dict[str, Any]:
    return json.loads(fetch_text(dataset_api_url(dataset_id), token=token))


def sibling_names(metadata: dict[str, Any]) -> list[str]:
    return [str(item.get("rfilename", "")) for item in metadata.get("siblings", []) if item.get("rfilename")]


def candidate_data_files(metadata: dict[str, Any]) -> list[str]:
    names = sibling_names(metadata)
    preferred = [name for name in names if name.endswith(".jsonl")]
    preferred.extend(name for name in names if name.endswith(".json"))
    preferred.extend(name for name in names if name.endswith(".parquet"))
    if preferred:
        return preferred

    values: list[str] = []
    card = metadata.get("cardData", {}) or {}
    for config in card.get("configs", []) or []:
        for item in config.get("data_files", []) or []:
            path = str(item.get("path", "") or "")
            if path and "*" not in path:
                values.append(path)
    return values


def parquet_rows(data: bytes) -> list[dict[str, Any]]:
    try:
        import pyarrow as pa
        import pyarrow.parquet as pq
    except ModuleNotFoundError as exc:
        raise SystemExit(
            "Reading the skeleton dataset requires pyarrow in the Python environment you use. "
            "For this workspace, `/localhome/milikic/miniconda3/bin/python -m pip install pyarrow` "
            "works with the documented local-Parquet refresh path."
        ) from exc
    table = pq.read_table(pa.BufferReader(data))
    return table.to_pylist()


def rows_from_dataset_file(dataset_id: str, path: str, *, token: str = "") -> list[dict[str, Any]]:
    data = fetch_bytes(dataset_file_url(dataset_id, path), token=token)
    if path.endswith(".jsonl"):
        return [json.loads(line) for line in data.decode("utf-8").splitlines() if line.strip()]
    if path.endswith(".json"):
        payload = json.loads(data.decode("utf-8"))
        if isinstance(payload, list):
            return payload
        if isinstance(payload, dict):
            for key in ("rows", "data", "test"):
                value = payload.get(key)
                if isinstance(value, list):
                    return value
        raise SystemExit(f"Unsupported JSON dataset shape in {path}")
    if path.endswith(".parquet"):
        return parquet_rows(data)
    raise SystemExit(f"Unsupported dataset file type: {path}")


def load_rows(
    refresh: bool,
    *,
    dataset_id: str,
    token: str = "",
    local_parquet: str = "",
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    dataset_path = DATA_DIR / "test.jsonl"
    metadata_path = DATA_DIR / "dataset_metadata.json"
    readme_path = DATA_DIR / "README.md"

    metadata: dict[str, Any] = {}
    if refresh or local_parquet or not dataset_path.exists():
        if local_parquet:
            metadata = {"id": dataset_id, "private": True, "source": str(Path(local_parquet).expanduser())}
            write_text(metadata_path, json.dumps(metadata, indent=2, sort_keys=True) + "\n")
            write_text(
                readme_path,
                f"# {dataset_id}\n\nLoaded from local Parquet file `{local_parquet}`.\n",
            )
            rows = parquet_rows(Path(local_parquet).expanduser().read_bytes())
        else:
            metadata = load_dataset_metadata(dataset_id, token=token)
            write_text(metadata_path, json.dumps(metadata, indent=2, sort_keys=True) + "\n")
            try:
                write_text(readme_path, fetch_text(dataset_raw_url(dataset_id, "README.md"), token=token))
            except SystemExit:
                write_text(readme_path, f"# {dataset_id}\n\nREADME.md was not available through the HF API.\n")

            files = candidate_data_files(metadata)
            if not files:
                raise SystemExit(f"No JSON/JSONL/Parquet data file found in {dataset_id}")
            rows = rows_from_dataset_file(dataset_id, files[0], token=token)
        write_text(dataset_path, "\n".join(json.dumps(row, ensure_ascii=False) for row in rows) + "\n")
    else:
        if metadata_path.exists():
            metadata = json.loads(metadata_path.read_text(encoding="utf-8"))

    rows: list[dict[str, Any]] = []
    for line_no, line in enumerate(dataset_path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip():
            continue
        row = json.loads(line)
        for field in ("idx", "informal_proof", "formalization_rules"):
            if field not in row:
                raise SystemExit(f"{dataset_path}:{line_no}: missing field {field!r}")
        rows.append(row)
    return rows, metadata


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


def skeleton_entries(row: dict[str, Any]) -> list[tuple[str, str]]:
    entries: list[tuple[str, str]] = []
    for key in ("skeleton1", "skeleton2", "skeleton3", "skeleton4"):
        value = str(row.get(key, "") or "").strip()
        if value:
            entries.append((f"{key.capitalize()}.lean", value.rstrip() + "\n"))
    return entries


def extract_imports_from_lean(text: str) -> list[str]:
    imports: list[str] = []
    for raw in str(text or "").splitlines():
        line = raw.strip()
        if not line.startswith("import "):
            continue
        if line not in imports:
            imports.append(line)
    return imports


def normalize_imports(raw_imports: Any) -> list[str]:
    imports: list[str] = []
    if isinstance(raw_imports, str):
        raw_values = raw_imports.splitlines()
    elif isinstance(raw_imports, list):
        raw_values = raw_imports
    else:
        raw_values = []
    for raw in raw_values:
        line = str(raw or "").strip()
        if not line:
            continue
        if not line.startswith("import "):
            line = f"import {line}"
        if line not in imports:
            imports.append(line)
    return imports


def row_imports(row: dict[str, Any]) -> list[str]:
    imports = normalize_imports(row.get("imports", []))
    if imports:
        return imports
    for _name, skeleton in skeleton_entries(row):
        for line in extract_imports_from_lean(skeleton):
            if line not in imports:
                imports.append(line)
    return imports or ["import Mathlib"]


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
        "% Candidate skeletons: docs/skeletons/\n"
        "% Lean target: ShadowBench/Source/Main.lean\n\n"
        f"{body}\n"
        "\\end{document}\n"
    )


def skeleton_list_markdown(entries: list[tuple[str, str]]) -> str:
    if not entries:
        return "- No candidate skeletons were provided for this problem."
    return "\n".join(f"- `docs/skeletons/{name}`" for name, _content in entries)


def render_skeleton_readme(row: dict[str, Any]) -> str:
    idx = str(row["idx"])
    entries = skeleton_entries(row)
    return (
        f"# Candidate Lean Skeletons: `{idx}`\n\n"
        "These files come from `Lemmy00/ShadowBench-skeletons-prod` and are suggestions for initial Lean declarations.\n"
        "Do not copy them blindly: compare each candidate against `../source.tex`, `../instructions.md`, and the blueprint.\n\n"
        "Available skeletons:\n\n"
        f"{skeleton_list_markdown(entries)}\n"
    )


def render_instructions(row: dict[str, Any], *, dataset_id: str) -> str:
    idx = str(row["idx"])
    imports = row_imports(row)
    names = expected_names(str(row["formalization_rules"]))
    entries = skeleton_entries(row)
    names_section = "\n".join(f"- `{name}`" for name in names) if names else "- [none detected]"
    return (
        f"# ShadowBench Instructions: `{idx}`\n\n"
        "## Source\n\n"
        "- Formalize `docs/source.tex`.\n"
        "- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.\n"
        "- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.\n\n"
        "## Candidate Skeletons\n\n"
        f"Dataset: `{dataset_id}`\n\n"
        f"{skeleton_list_markdown(entries)}\n\n"
        "Treat these as candidate statement/definition shapes, not authoritative answers. Prefer the source theorem and formalization rules when candidates disagree.\n\n"
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
        "- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.\n"
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


def render_project_yaml(dataset_id: str) -> str:
    return (
        "schema_version: 1\n"
        "name: ShadowBench\n"
        "kind: lean4\n"
        "lean_root: .\n"
        "created_at: '2026-06-02T00:00:00+00:00'\n"
        "paths:\n"
        "  runtime: .epflemma/runtime\n"
        "  cache: .epflemma/cache\n"
        "  workflows: .epflemma/workflows\n"
        "source:\n"
        "  mode: shadowbench-skeletons\n"
        f"  template_source: {dataset_id}\n"
        "blueprint:\n"
        "  markers:\n"
        "  - lean-toolchain\n"
        "  - lakefile.toml\n"
    )


def render_main_lean(row: dict[str, Any]) -> str:
    idx = str(row["idx"])
    imports = row_imports(row)
    rule_code = leading_rule_code(str(row["formalization_rules"]))
    chunks = ["\n".join(imports)]
    if rule_code:
        chunks.append(rule_code)
    chunks.append(
        "/-\n"
        f"ShadowBench problem: {idx}\n"
        "Source: docs/source.tex\n"
        "Instructions: docs/instructions.md\n"
        "Candidate skeletons: docs/skeletons/\n"
        "Blueprint: ShadowBench/Source/Blueprint.md\n\n"
        "Replace this scaffold with the required declarations and proofs.\n"
        "-/\n"
    )
    return "\n\n".join(chunks).rstrip() + "\n"


def render_blueprint(row: dict[str, Any], *, dataset_id: str) -> str:
    idx = str(row["idx"])
    imports = row_imports(row)
    names = expected_names(str(row["formalization_rules"]))
    entries = skeleton_entries(row)
    names_text = "\n".join(f"- `{name}`" for name in names) if names else "- [pending manual extraction]"
    return (
        f"# Formalization Blueprint: `{idx}`\n\n"
        "- Source: `docs/source.tex`\n"
        "- Instructions: `docs/instructions.md`\n"
        "- Candidate skeletons: `docs/skeletons/`\n"
        "- Target Lean entry file: `ShadowBench/Source/Main.lean`\n"
        "- Status: scaffold created; replace pending entries during formalization.\n\n"
        "## Candidate Skeletons\n\n"
        f"- Dataset: `{dataset_id}`\n"
        f"{skeleton_list_markdown(entries)}\n\n"
        "Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.\n\n"
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
        "- Skeleton candidate used: _pending_\n"
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


def render_metadata(row: dict[str, Any], *, dataset_id: str) -> str:
    payload = dict(row)
    payload["_dataset"] = dataset_id
    return json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


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
    dataset_id: str,
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
        "docs/instructions.md": render_instructions(row, dataset_id=dataset_id),
        "docs/metadata.json": render_metadata(row, dataset_id=dataset_id),
        "docs/llm_history.template.json": render_history_template(row),
        "docs/skeletons/README.md": render_skeleton_readme(row),
        "lakefile.toml": render_lakefile(package_name, mathlib_rev=mathlib_rev),
        "lean-toolchain": f"{lean_toolchain}\n",
        ".epflemma/project.yaml": render_project_yaml(dataset_id),
        "ShadowBench.lean": "import ShadowBench.Source\n",
        "ShadowBench/Source.lean": "import ShadowBench.Source.Main\n",
    }
    for name, content in skeleton_entries(row):
        files[f"docs/skeletons/{name}"] = content

    for relative, content in files.items():
        if write_text(problem_dir / relative, content):
            changed += 1

    main_path = problem_dir / "ShadowBench/Source/Main.lean"
    if overwrite_lean or not main_path.exists():
        if write_text(main_path, render_main_lean(row)):
            changed += 1

    blueprint_path = problem_dir / "ShadowBench/Source/Blueprint.md"
    if overwrite_blueprint or not blueprint_path.exists():
        if write_text(blueprint_path, render_blueprint(row, dataset_id=dataset_id)):
            changed += 1

    return {
        "idx": idx,
        "path": str(problem_dir.relative_to(ROOT)),
        "changed_files": changed,
        "skeleton_count": len(skeleton_entries(row)),
    }


def reset_problem_dirs() -> None:
    if PROBLEMS_DIR.exists():
        shutil.rmtree(PROBLEMS_DIR)
    PROBLEMS_DIR.mkdir(parents=True, exist_ok=True)


def prune_problem_dirs(rows: list[dict[str, Any]]) -> int:
    wanted = {str(row["idx"]) for row in rows}
    removed = 0
    if not PROBLEMS_DIR.exists():
        return removed
    for path in sorted(PROBLEMS_DIR.glob("*/*/*")):
        if not path.is_dir():
            continue
        try:
            rel = path.relative_to(PROBLEMS_DIR).as_posix()
        except ValueError:
            continue
        if rel not in wanted:
            shutil.rmtree(path)
            removed += 1
    return removed


def write_index(
    rows: list[dict[str, Any]],
    generated: list[dict[str, Any]],
    *,
    dataset_id: str,
    metadata: dict[str, Any],
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
        "dataset": dataset_id,
        "dataset_url": dataset_file_url(dataset_id, "data/test-00000-of-00001.parquet"),
        "dataset_sha": metadata.get("sha", ""),
        "dataset_private": bool(metadata.get("private", False)),
        "lean_toolchain": lean_toolchain,
        "mathlib_rev": mathlib_rev,
        "problem_count": len(rows),
        "skeleton_problem_count": sum(1 for item in generated if item.get("skeleton_count", 0) > 0),
        "skeleton_fields": ["skeleton1", "skeleton2", "skeleton3", "skeleton4"],
        "by_area": dict(sorted(by_area.items())),
        "by_level": dict(sorted(by_level.items())),
        "problems": generated,
    }
    write_text(DATA_DIR / "problem_index.json", json.dumps(payload, indent=2, sort_keys=True) + "\n")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Prepare one Lean project per ShadowBench skeleton row.")
    parser.add_argument("--refresh", action="store_true", help="redownload dataset files")
    parser.add_argument("--dataset", default=DEFAULT_DATASET_ID, help=f"HF dataset id (default: {DEFAULT_DATASET_ID})")
    parser.add_argument("--hf-token", default="", help="HF token; defaults to HF_TOKEN from the environment")
    parser.add_argument("--local-parquet", default="", help="read rows from an already-downloaded Parquet file")
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
    parser.add_argument("--reset-problems", action="store_true", help="delete all generated problem folders before writing")
    parser.add_argument("--prune", action="store_true", help="delete problem folders not present in the current dataset")
    parser.add_argument("--limit", type=int, default=0, help="materialize only the first N rows")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    rows, metadata = load_rows(
        refresh=args.refresh,
        dataset_id=args.dataset,
        token=args.hf_token,
        local_parquet=args.local_parquet,
    )
    if args.limit:
        rows = rows[: args.limit]
    if args.reset_problems:
        reset_problem_dirs()
    elif args.prune:
        removed = prune_problem_dirs(rows)
        if removed:
            print(f"Pruned {removed} stale problem project(s)")
    generated = [
        materialize_problem(
            row,
            dataset_id=args.dataset,
            lean_toolchain=args.lean_toolchain,
            mathlib_rev=args.mathlib_rev,
            overwrite_lean=args.overwrite_lean,
            overwrite_blueprint=args.overwrite_blueprint,
        )
        for row in rows
    ]
    write_index(
        rows,
        generated,
        dataset_id=args.dataset,
        metadata=metadata,
        lean_toolchain=args.lean_toolchain,
        mathlib_rev=args.mathlib_rev,
    )
    changed = sum(item["changed_files"] for item in generated)
    skeletons = sum(item["skeleton_count"] for item in generated)
    print(f"Prepared {len(generated)} ShadowBench problem projects; changed files: {changed}")
    print(f"Skeleton candidates written: {skeletons}")
    print(f"Index: {DATA_DIR / 'problem_index.json'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
