# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_003`

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
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
```

## Required Names

- `locallyOfFinitePresentation_isStableUnderBaseChange`

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
open CategoryTheory Topology

/-
Formalize in Lean the Theorem (locallyOfFinitePresentation_isStableUnderBaseChange) from Text.

The theorem must be named `locallyOfFinitePresentation_isStableUnderBaseChange`.
   Matched text (candidate 0, theorem, label=locallyOfFinitePresentation_isStableUnderBaseChange): \begin{theorem}[locallyOfFinitePresentation_isStableUnderBaseChange] Let $f: X \to Y$ be a
                                                                                                   morphism of schemes. Assume $f$ is of finite presentation. Then the image of a locally
                                                                                                   constructible subset is locally constructible. \end{theorem}
-/
```
