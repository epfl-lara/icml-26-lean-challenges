# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.

## Import Plan

```lean
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.Etale.QuasiFinite
```

## Required Names

- `Scheme.Hom.exists_isIso_morphismRestrict_toNormalization`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Skeleton candidate used: _pending_
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

## Formalization Rules

```text
open CategoryTheory Limits

/-
Formalize in Lean the following items from Text.

Theorem (Scheme.Hom.exists_isIso_morphismRestrict_toNormalization)
   The theorem must be named `Scheme.Hom.exists_isIso_morphismRestrict_toNormalization`.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
