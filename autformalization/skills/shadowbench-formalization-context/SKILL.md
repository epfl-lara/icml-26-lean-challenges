---
name: shadowbench-formalization-context
description: Persistent context for ShadowBench autoformalization projects generated from Lemmy00/ShadowBench-skeletons-prod.
---

# ShadowBench Formalization Context

Use this supplement for every ShadowBench formalization or proof run.

## Required Reads

Before choosing declarations or attempting proofs, read these project-local files:

- `docs/instructions.md`
- `docs/source.tex`
- `docs/skeletons/README.md`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`
- `ShadowBench/Source/Blueprint.md`

The skeleton Lean files are suggestions for initial theorem statements, definitions, imports, and naming only. They are not a replacement for the LaTeX source or the formalization rules.

## Proof Runs

- The proof target is always `ShadowBench/Source/Main.lean` in the current problem project.
- Before editing a proof, identify the active declaration in `Main.lean`, then read the matching section of `ShadowBench/Source/Blueprint.md`.
- Use `docs/source.tex` as the primary natural-language statement/proof source. If the source includes a proof, proof sketch, construction, or named reduction, follow it before inventing a new proof strategy.
- Use `docs/instructions.md` to confirm required declaration names and formalization rules. Do not rename required declarations during proving.
- Use skeletons only as hints for alternate formulations, missing helper names, or likely imports. Do not change a reviewed statement just because a skeleton is easier to prove.
- Preserve source-backed theorem statements by default. If a statement appears false or impossible, stop and report the statement/source mismatch instead of weakening it.
- Prefer local definitions and lemmas in `Main.lean`, then project-local imports, then Mathlib search. Add helper lemmas only when they directly reduce the active proof.
- After each proof edit, verify with `lake env lean ShadowBench/Source/Main.lean`; a proof is not complete while any submitted declaration still contains `sorry`, `admit`, or open goals.

## Formalization Rules

- Put the final answer in `ShadowBench/Source/Main.lean`.
- Keep imports as the first lines of the Lean file, before comments or declarations.
- Preserve theorem and definition names required by `docs/instructions.md`.
- Compare any adopted skeleton against `docs/source.tex` and the formalization rules before using it.
- Do not weaken or strengthen a source claim to fit a convenient skeleton.
- Record in `ShadowBench/Source/Blueprint.md` which skeleton, if any, shaped the final statement and why it matches the source.
- Keep proof notes close enough that a later proof run can recover the source argument after context compaction.

## Verification Target

For a finished proof/submission, `lake env lean ShadowBench/Source/Main.lean` must pass and the submitted declarations must have no `sorry`, `admit`, or open goals.
