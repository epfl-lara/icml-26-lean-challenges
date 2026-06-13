#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = ROOT / "data" / "dicotiar_test_imports.json"
DEFAULT_ROWS_OUTPUT = ROOT / "data" / "dicotiar_test.jsonl"
WORKSPACE_ROWS = ROOT / "data" / "test.jsonl"
WORKSPACE_METADATA = ROOT / "data" / "dataset_metadata.json"
WORKSPACE_README = ROOT / "data" / "README.md"
DATASET = "DicoTiar/ShadowBench"
CONFIG = "default"
SPLIT = "test"


def fetch_json(path: str, params: dict[str, str | int]) -> dict[str, Any]:
    query = urllib.parse.urlencode(params)
    url = f"https://datasets-server.huggingface.co/{path}?{query}"
    with urllib.request.urlopen(url, timeout=60) as response:
        payload = response.read().decode("utf-8")
    data = json.loads(payload)
    if not isinstance(data, dict):
        raise SystemExit(f"Unexpected response from {url}")
    return data


def fetch_rows(*, dataset: str, config: str, split: str, page_size: int) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    offset = 0
    while True:
        data = fetch_json(
            "rows",
            {
                "dataset": dataset,
                "config": config,
                "split": split,
                "offset": offset,
                "length": page_size,
            },
        )
        batch = data.get("rows", [])
        if not isinstance(batch, list):
            raise SystemExit("Dataset Viewer response did not contain a row list")
        for item in batch:
            if not isinstance(item, dict) or not isinstance(item.get("row"), dict):
                raise SystemExit("Dataset Viewer response contained a malformed row")
            rows.append(item["row"])
        if len(batch) < page_size:
            break
        offset += page_size
    return rows


def normalized_imports(raw: Any) -> list[str]:
    if isinstance(raw, str):
        values = raw.splitlines()
    elif isinstance(raw, list):
        values = raw
    else:
        values = []
    imports: list[str] = []
    for value in values:
        line = str(value).strip()
        if not line:
            continue
        if not line.startswith("import "):
            line = "import " + line
        if line not in imports:
            imports.append(line)
    return imports


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Refresh official DicoTiar/ShadowBench test imports.")
    parser.add_argument("--dataset", default=DATASET)
    parser.add_argument("--config", default=CONFIG)
    parser.add_argument("--split", default=SPLIT)
    parser.add_argument("--page-size", type=int, default=100)
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--rows-output", default=str(DEFAULT_ROWS_OUTPUT))
    parser.add_argument(
        "--update-workspace",
        action="store_true",
        help="also replace data/test.jsonl and dataset metadata with the official DicoTiar rows",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    rows = fetch_rows(dataset=args.dataset, config=args.config, split=args.split, page_size=args.page_size)
    imports_by_idx: dict[str, list[str]] = {}
    for row in rows:
        idx = str(row.get("idx", "")).strip()
        if not idx:
            raise SystemExit("Official row without idx")
        if idx in imports_by_idx:
            raise SystemExit(f"Duplicate official idx: {idx}")
        imports_by_idx[idx] = normalized_imports(row.get("imports", []))
    output = Path(args.output).expanduser().resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    rows_output = Path(args.rows_output).expanduser().resolve()
    rows_output.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "config": args.config,
        "dataset": args.dataset,
        "imports_by_idx": imports_by_idx,
        "num_rows": len(rows),
        "split": args.split,
    }
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    rows_payload = "\n".join(json.dumps(row, ensure_ascii=False) for row in rows) + "\n"
    rows_output.write_text(rows_payload, encoding="utf-8")
    if args.update_workspace:
        WORKSPACE_ROWS.write_text(rows_payload, encoding="utf-8")
        WORKSPACE_METADATA.write_text(
            json.dumps(
                {
                    "config": args.config,
                    "id": args.dataset,
                    "private": False,
                    "source": "Hugging Face Dataset Viewer API",
                    "split": args.split,
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        WORKSPACE_README.write_text(
            f"# {args.dataset}\n\n"
            f"Loaded from the Hugging Face Dataset Viewer API, config `{args.config}`, split `{args.split}`.\n",
            encoding="utf-8",
        )
    print(f"Wrote {len(rows)} official import rows to {output}")
    print(f"Wrote {len(rows)} official rows to {rows_output}")
    if args.update_workspace:
        print(f"Updated workspace rows at {WORKSPACE_ROWS}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
