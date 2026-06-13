# ShadowBench Autoformalization Workspace

This directory prepares Track 4 work for the ICML 2026 AI4Math challenge. The public workshop page describes Track 4 as end-to-end autoformalization and proof generation in Lean 4, and ShadowBench asks for one Lean snippet per problem with a non-empty `llm_history`.

Current primary dataset: `Lemmy00/ShadowBench-skeletons-prod`.

This private dataset includes four candidate Lean skeletons per problem. They are written under `docs/skeletons/` and should be treated as suggestions for initial theorem statements and definitions, not as source-of-truth replacements for the LaTeX statement and formalization rules.

The generated layout is one standalone Lean project per dataset row:

```text
problems/<area>/<level>/<problem>/
  docs/source.tex              # LaTeX source to formalize
  docs/instructions.md         # imports, canonical names, rules
  docs/skeletons/              # four candidate Lean skeletons
  lakefile.toml
  lean-toolchain
  .epflemma/project.yaml
  ShadowBench.lean             # project root module
  ShadowBench/Source.lean      # parent module
  ShadowBench/Source/Main.lean # Lean entry file for the answer
  ShadowBench/Source/Blueprint.md
```

## Regenerate

```bash
python3 scripts/prepare_shadowbench.py
```

Use `--refresh` to redownload the private dataset and rebuild `data/test.jsonl`. Set `HF_TOKEN` first if the dataset is not already cached:

```bash
export HF_TOKEN=...
python3 scripts/prepare_shadowbench.py --refresh --reset-problems --overwrite-lean --overwrite-blueprint
```

If the private Parquet file was already downloaded, or if your local `python3` does not have `pyarrow`, use a Python environment that does:

```bash
/localhome/milikic/miniconda3/bin/python scripts/prepare_shadowbench.py \
  --local-parquet /tmp/shadowbench_skeletons/test.parquet \
  --reset-problems --overwrite-lean --overwrite-blueprint
```

Existing `ShadowBench/Source/Main.lean` files and `Blueprint.md` files are not overwritten unless you pass `--overwrite-lean` or `--overwrite-blueprint`. Use `--reset-problems` only when you intentionally want to discard dummy workflow state and regenerate clean problem folders.

The default generated Lean stack is `leanprover/lean4:v4.29.0` with mathlib `v4.29.0`. If the Track 4 grader announces a different pin, regenerate with `--lean-toolchain ... --mathlib-rev ...`.

## Work One Problem

```bash
scripts/epflemma_formalize_only.sh --problem analysis/L2/ana_comp_L2_002 --lake-update --check-after
scripts/epflemma_prove_only.sh --problem analysis/L2/ana_comp_L2_002 --check-after
```

Before formalizing, read `docs/instructions.md`, `docs/skeletons/README.md`, all four `docs/skeletons/Skeleton*.lean` files, and `ShadowBench/Source/Blueprint.md`. Keep the Lean imports aligned with the imports listed there. The Lean file must start with imports before comments or declarations.

The helper scripts automatically pass `skills/shadowbench-formalization-context/SKILL.md` as an EPFLemma `--additional-skill`, so formalize and prove runs are reminded to read the instructions and skeletons before choosing statements. The skeletons are prompt-side suggestions, not authority over the source.

The helper script can run from either a problem directory or the workspace root:

```bash
scripts/epflemma_formalize_only.sh --problem algebra/L2/alg_comp_L2_001 --check-after
scripts/epflemma_prove_only.sh --problem algebra/L2/alg_comp_L2_001 --check-after
scripts/epflemma_formalize_and_prove.sh --problem algebra/L2/alg_comp_L2_001 --lake-update --check-after
```

The lower-level `scripts/epflemma_formalize.sh` is still available when you want to set `--phase init`, `--phase formalize`, `--phase prove`, `--phase both`, or `--phase check` explicitly.

EPFLemma workflow commands are fed a final `/exit` line, like `printf '/exit\n' | epflemma workflow ...`, so finished agent-mode sessions leave the prompt cleanly instead of hitting EOF cleanup paths. Project init still runs with stdin closed.

Prove-only runs are guarded by default. Before EPFLemma starts, `scripts/shadowbench_proof_guard.py` snapshots the import lines and every required declaration from `docs/instructions.md`; after EPFLemma exits, the wrapper rejects the run if imports, theorem/lemma signatures, or required definition/class bodies changed. This keeps prove runs focused on proof bodies and same-file helper lemmas. Use `--no-proof-guard` only when intentionally doing a formalization/setup repair, not proof completion. Use `--proof-guard-require-allowed-imports` when you also want to fail immediately unless local imports exactly match the allowed imports in `docs/instructions.md`.

By default, `scripts/epflemma_formalize.sh` runs `epflemma project init` only when `.epflemma/project.yaml` is missing. Use `--force-project-init` to rebuild EPFLemma project metadata, or `--no-project-init` when you already ran the batch init phase.

Phases:

- `init`: run `epflemma project init` for the selected problem project.
- `formalize`: source-backed declaration drafting from `docs/source.tex`.
- `prove`: proof completion for `ShadowBench/Source/Main.lean`.
- `both`: formalize then prove.
- `check`: only run `lake env lean ShadowBench/Source/Main.lean`.

## Batch Runs

Use `epflemma_batch.py` to process problems systematically. It writes logs and status under ignored `runs/`.

Preview selected problems:

```bash
python3 scripts/epflemma_batch.py list --level L2 --limit 10
scripts/epflemma_batch_init.sh --level L2 --limit 3 --dry-run
python3 scripts/epflemma_batch.py run --level L2 --limit 3 --phase formalize --dry-run
scripts/epflemma_batch_formalize.sh --level L2 --limit 3 --dry-run
```

Initialize EPFLemma metadata for selected projects once:

```bash
scripts/epflemma_batch_init.sh --level L2 --skip-success
```

Formalize all L2 problems, one at a time:

```bash
scripts/epflemma_batch_formalize.sh --level L2 --check-after --skip-success
```

Continue after an interrupted run:

```bash
scripts/epflemma_batch_formalize.sh --level L2 --check-after --skip-success
```

Prove already formalized files:

```bash
scripts/epflemma_batch_prove.sh --level L2 --check-after --skip-success
scripts/epflemma_batch_prove.sh --only analysis/L3/ana_gen_L3_004 --proof-guard-require-allowed-imports --check-after
```

Inspect status:

```bash
python3 scripts/epflemma_batch.py status --level L2
python3 scripts/epflemma_batch.py status --level L2 --verbose
```

Batch statuses:

- `success`: the process exited cleanly, or a nonzero EPFLemma cleanup exit was accepted because the final log contains a source-review `PASS` or `Formalizer ended: document source/statement review passed`.
- `needs-review`: Lean/project verification passed, but the final log does not contain the source-review PASS signal. These are good candidates for manual source-fidelity review before proving.
- `failed`: no accepted final verification signal was found, or the log records a hard failure such as disk exhaustion.
- `not-run`: no status entry exists for that phase.

After an interrupted or disk-full run, reclassify logs before resuming:

```bash
python3 scripts/epflemma_batch.py reconcile --run-id formalize-all-20260602T233915Z --write
```

The batch wrappers are aliases for `epflemma_batch.py run`:

- `scripts/epflemma_batch_init.sh`
- `scripts/epflemma_batch_formalize.sh`
- `scripts/epflemma_batch_prove.sh`
- `scripts/epflemma_batch_formalize_and_prove.sh`

Useful filters:

```bash
python3 scripts/epflemma_batch.py run --area algebra --level L2 --phase formalize
python3 scripts/epflemma_batch.py run --only algebra/L2/alg_comp_L2_001 --phase both --check-after
python3 scripts/epflemma_batch.py run --level L2 --start-after alg_comp_L2_001 --phase formalize
```

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

By default, the exporter fails closed when `data/dicotiar_test_imports.json` is present and the local rows do not match the official `DicoTiar/ShadowBench` test `idx`/import manifest. Use `--allow-official-mismatch` or `--allow-import-fallback` only for local debugging, not for final submissions.

## Rules Audit

Run the generated-submission audit before treating a proof batch as submission-ready:

```bash
python3 scripts/audit_submission_rules.py --output-dir runs/rules-audit-latest --compile --axioms
```

This checks the exported `formal_proof` snippets, not the raw project files:

- every snippet is wrapped in the required `ABM.<area>.<level>.<problem>` namespace
- no `import` lines remain in `formal_proof`
- official `DicoTiar/ShadowBench` imports are used for compilation
- no `sorry`, `admit`, new `axiom`, `constant`, `opaque`, `unsafe`, or `native_decide` shortcuts appear
- required declarations are present and not weakened by `*Mechanism` hypotheses
- compile-passing rows are checked with `#print axioms` against the competition whitelist

See also [SKELETONS.md](SKELETONS.md) for the intended skeleton usage policy.
