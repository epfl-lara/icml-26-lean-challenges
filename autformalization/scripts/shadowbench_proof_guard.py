#!/usr/bin/env python3
from __future__ import annotations

import argparse
import difflib
import json
import re
import sys
from pathlib import Path
from typing import Any


TARGET = Path("ShadowBench/Source/Main.lean")
INSTRUCTIONS = Path("docs/instructions.md")
DECL_KINDS = ("theorem", "lemma", "def", "abbrev", "structure", "class", "instance")
DECL_RE = re.compile(
    rf"(?m)^[ \t]*(?:@[^\n]*\n[ \t]*)*(?:noncomputable\s+)?({'|'.join(DECL_KINDS)})\s+"
)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def normalize_ws(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def imports_from_main(text: str) -> list[str]:
    return [line.strip() for line in text.splitlines() if line.lstrip().startswith("import ")]


def allowed_imports(project: Path) -> list[str]:
    path = project / INSTRUCTIONS
    if not path.is_file():
        return []
    text = read_text(path)
    match = re.search(r"## Allowed Imports.*?```lean\n(.*?)\n```", text, flags=re.S)
    if not match:
        return []
    imports: list[str] = []
    for raw in match.group(1).splitlines():
        line = raw.strip()
        if line.startswith("import ") and line not in imports:
            imports.append(line)
    return imports


def expected_names(project: Path) -> list[str]:
    path = project / INSTRUCTIONS
    if not path.is_file():
        return []
    text = read_text(path)
    names: list[str] = []
    section = re.search(r"## Expected Declaration Names\n(.*?)(?:\n## |\Z)", text, flags=re.S)
    if section:
        names.extend(re.findall(r"`([^`]+)`", section.group(1)))
    if not names:
        patterns = [
            r"The theorem must be named `([^`]+)`",
            r"The lemma must be named `([^`]+)`",
            r"The definition must be named `([^`]+)`",
            r"The Lean declaration must be named exactly:\s*(?:\n-\s*)?`([^`]+)`",
            r"must be named exactly:\s*(?:\n-\s*)?`([^`]+)`",
            r"must be named `([^`]+)`",
        ]
        for pattern in patterns:
            names.extend(re.findall(pattern, text))
    seen: set[str] = set()
    result: list[str] = []
    for name in names:
        name = name.strip()
        if name and name not in seen:
            result.append(name)
            seen.add(name)
    return result


def lean_name_regex(name: str) -> str:
    return re.escape(name) + r"(?![A-Za-z0-9_'.])"


def declaration_matches(text: str, name: str) -> list[re.Match[str]]:
    prefixes = [
        rf"(?m)^[ \t]*(?:@[^\n]*\n[ \t]*)*(?:noncomputable\s+)?({'|'.join(DECL_KINDS)})\s+{lean_name_regex(name)}",
    ]
    if "." in name:
        short = name.rsplit(".", 1)[1]
        prefixes.append(
            rf"(?m)^[ \t]*(?:@[^\n]*\n[ \t]*)*(?:noncomputable\s+)?({'|'.join(DECL_KINDS)})\s+{lean_name_regex(short)}"
        )
    matches: list[re.Match[str]] = []
    for pattern in prefixes:
        matches.extend(re.finditer(pattern, text))
        if matches:
            break
    return matches


def next_decl_start(text: str, start: int) -> int:
    match = DECL_RE.search(text, start)
    return match.start() if match else len(text)


def signature_for_block(kind: str, block: str) -> str:
    if kind in {"theorem", "lemma"}:
        marker = block.find(":=")
        if marker >= 0:
            return normalize_ws(block[:marker])
    return normalize_ws(block)


def protected_body_for(kind: str, block: str) -> str | None:
    if kind in {"theorem", "lemma"}:
        return None
    return normalize_ws(block)


def declaration_snapshot(text: str, name: str) -> dict[str, Any] | None:
    matches = declaration_matches(text, name)
    if not matches:
        return None
    match = matches[0]
    kind = match.group(1)
    end = next_decl_start(text, match.end())
    block = text[match.start() : end].strip()
    result: dict[str, Any] = {
        "kind": kind,
        "signature": signature_for_block(kind, block),
    }
    protected_body = protected_body_for(kind, block)
    if protected_body is not None:
        result["protected_body"] = protected_body
    return result


def make_snapshot(project: Path, *, require_allowed_imports: bool, allow_missing_decls: bool) -> dict[str, Any]:
    main_path = project / TARGET
    if not main_path.is_file():
        raise SystemExit(f"Missing Lean target: {main_path}")
    text = read_text(main_path)
    imports = imports_from_main(text)
    allowed = allowed_imports(project)
    if require_allowed_imports and allowed and imports != allowed:
        print("PROOF_GUARD_FAILED: current imports do not match docs/instructions.md allowed imports", file=sys.stderr)
        print(diff_lists("current imports", imports, "allowed imports", allowed), file=sys.stderr)
        raise SystemExit(1)

    names = expected_names(project)
    declarations: dict[str, Any] = {}
    missing: list[str] = []
    for name in names:
        decl = declaration_snapshot(text, name)
        if decl is None:
            missing.append(name)
        else:
            declarations[name] = decl

    if missing and not allow_missing_decls:
        print("PROOF_GUARD_FAILED: required declarations are missing before prove-only run", file=sys.stderr)
        for name in missing:
            print(f"- {name}", file=sys.stderr)
        raise SystemExit(1)

    return {
        "version": 1,
        "target": TARGET.as_posix(),
        "imports": imports,
        "allowed_imports": allowed,
        "expected_names": names,
        "declarations": declarations,
        "missing_declarations": missing,
    }


def diff_lists(left_label: str, left: list[str], right_label: str, right: list[str]) -> str:
    return "\n".join(
        difflib.unified_diff(
            [line + "\n" for line in left],
            [line + "\n" for line in right],
            fromfile=left_label,
            tofile=right_label,
            lineterm="",
        )
    )


def diff_text(left_label: str, left: str, right_label: str, right: str) -> str:
    return "\n".join(
        difflib.unified_diff(
            [left + "\n"],
            [right + "\n"],
            fromfile=left_label,
            tofile=right_label,
            lineterm="",
        )
    )


def compare_snapshots(before: dict[str, Any], after: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    before_imports = list(before.get("imports", []))
    after_imports = list(after.get("imports", []))
    if before_imports != after_imports:
        errors.append(
            "Import block changed during prove-only run:\n"
            + diff_lists("before imports", before_imports, "after imports", after_imports)
        )

    before_decls: dict[str, Any] = dict(before.get("declarations", {}))
    after_decls: dict[str, Any] = dict(after.get("declarations", {}))
    for name, old in before_decls.items():
        new = after_decls.get(name)
        if new is None:
            errors.append(f"Required declaration disappeared: {name}")
            continue
        if old.get("kind") != new.get("kind"):
            errors.append(f"Declaration kind changed for {name}: {old.get('kind')} -> {new.get('kind')}")
        if old.get("signature") != new.get("signature"):
            errors.append(
                f"Protected declaration signature changed for {name}:\n"
                + diff_text("before signature", str(old.get("signature", "")), "after signature", str(new.get("signature", "")))
            )
        if "protected_body" in old and old.get("protected_body") != new.get("protected_body"):
            errors.append(
                f"Protected definition/class body changed for {name}:\n"
                + diff_text("before body", str(old.get("protected_body", "")), "after body", str(new.get("protected_body", "")))
            )
    return errors


def cmd_snapshot(args: argparse.Namespace) -> int:
    project = Path(args.problem_dir).expanduser().resolve()
    snapshot = make_snapshot(
        project,
        require_allowed_imports=args.require_allowed_imports,
        allow_missing_decls=args.allow_missing_decls,
    )
    output = Path(args.output).expanduser()
    if not output.is_absolute():
        output = project / output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(snapshot, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"PROOF_GUARD_SNAPSHOT {output}")
    return 0


def cmd_check(args: argparse.Namespace) -> int:
    project = Path(args.problem_dir).expanduser().resolve()
    input_path = Path(args.input).expanduser()
    if not input_path.is_absolute():
        input_path = project / input_path
    before = json.loads(input_path.read_text(encoding="utf-8"))
    after = make_snapshot(
        project,
        require_allowed_imports=args.require_allowed_imports,
        allow_missing_decls=True,
    )
    errors = compare_snapshots(before, after)
    if errors:
        print("PROOF_GUARD_FAILED: prove-only run changed protected imports or declarations", file=sys.stderr)
        for error in errors:
            print("\n" + error, file=sys.stderr)
        return 1
    print("PROOF_GUARD_OK")
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Guard ShadowBench prove-only runs against import/statement drift.")
    subparsers = parser.add_subparsers(dest="command", required=True)

    snapshot = subparsers.add_parser("snapshot", help="write a pre-prove guard snapshot")
    snapshot.add_argument("--problem-dir", default=".")
    snapshot.add_argument("--output", default=".epflemma/proof-guard-before.json")
    snapshot.add_argument("--require-allowed-imports", action="store_true")
    snapshot.add_argument("--allow-missing-decls", action="store_true")
    snapshot.set_defaults(func=cmd_snapshot)

    check = subparsers.add_parser("check", help="compare current file with a pre-prove guard snapshot")
    check.add_argument("--problem-dir", default=".")
    check.add_argument("--input", default=".epflemma/proof-guard-before.json")
    check.add_argument("--require-allowed-imports", action="store_true")
    check.set_defaults(func=cmd_check)

    return parser.parse_args()


def main() -> int:
    args = parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
