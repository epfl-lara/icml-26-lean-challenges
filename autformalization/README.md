# ShadowBench Autoformalization Workspace

This directory prepares Track 4 work for the ICML 2026 AI4Math challenge. The public workshop page describes Track 4 as end-to-end autoformalization and proof generation in Lean 4, and the ShadowBench dataset asks for one Lean snippet per problem with a non-empty `llm_history`.

The generated layout is one standalone Lean project per dataset row:

```text
problems/<area>/<level>/<problem>/
  docs/source.tex              # LaTeX source to formalize
  docs/instructions.md         # imports, canonical names, rules
  lakefile.toml
  lean-toolchain
  .epflemma/project.yaml
  ShadowBench.lean             # project root module
  ShadowBench/Source/Main.lean # Lean entry file for the answer
  ShadowBench/Source/Blueprint.md
```

## Regenerate

```bash
python3 scripts/prepare_shadowbench.py
```

Use `--refresh` to redownload `test.jsonl`. Existing `ShadowBench/Source/Main.lean` files and `Blueprint.md` files are not overwritten unless you pass `--overwrite-lean` or `--overwrite-blueprint`.

The default generated Lean stack is `leanprover/lean4:v4.28.0` with mathlib `v4.28.0`, matching the nearby Track 2 projects. If the Track 4 grader announces a different pin, regenerate with `--lean-toolchain ... --mathlib-rev ...`.

## Work One Problem

```bash
cd problems/analysis/L2/ana_comp_L2_002
lake update
lake env lean ShadowBench/Source/Main.lean
epflemma workflow formalize docs/source.tex
epflemma workflow prove ShadowBench/Source/Main.lean
```

Before formalizing, read `docs/instructions.md` and keep the Lean imports aligned with the allowed imports listed there. The Lean file must start with imports before comments or declarations.

## Check

```bash
python3 scripts/check_problem.py analysis/L2/ana_comp_L2_002 --update
```

This runs `lake env lean ShadowBench/Source/Main.lean` inside the selected problem project. `--update` runs `lake update` first.

## Export

```bash
python3 scripts/export_submission.py --strict-history
```

The submission writer emits `submission/shadowbench_submission.jsonl` with one row per problem:

```json
{"idx": "...", "formal_proof": "<full Lean snippet>", "llm_history": [{"role": "...", "content": "..."}]}
```

For serious submissions, put the actual model conversation in `docs/llm_history.json` for each solved problem and use `--strict-history`.
