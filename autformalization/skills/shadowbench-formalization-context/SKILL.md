---
name: shadowbench-formalization-context
description: Persistent context for ShadowBench autoformalization projects generated from Lemmy00/ShadowBench-skeletons-prod.
---

# ShadowBench Formalization Context

Use this supplement for every ShadowBench formalization or proof run.

## Required Reads

Before choosing declarations, read these project-local files:

- `docs/instructions.md`
- `docs/skeletons/README.md`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`
- `ShadowBench/Source/Blueprint.md`

The skeleton Lean files are suggestions for initial theorem statements, definitions, imports, and naming only. They are not a replacement for the LaTeX source or the formalization rules.

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
