---
name: formalization-blueprint-ShadowBench-Source-Main
description: Blueprint and source map for `ShadowBench/Source/Main.lean`.
---

# Blueprint: ShadowBench/Source/Main.lean

Canonical blueprint path: `ShadowBench/Source/Blueprint.md`.
Source document: `docs/source.tex`.
Target Lean file: `ShadowBench/Source/Main.lean`.

Use the canonical `Blueprint.md` for full source text, statement-fidelity notes, scope-change notes, and prover notes before proving.

## Source Inventory

### Source inventory entry: `line-17`

- Source inventory entry: `line-17`.
- Source label: `line-17`.
- Source locator: `line-17`.
- Source file: `docs/source.tex`.
- Kind: theorem.
- Source name: `functionField_isFractionRing_of_affine`.
- Source statement: Let $R$ be an integral domain. Then the function field of the affine scheme $\operatorname{Spec} R$ is isomorphic to the field of fractions of $R$.
- Complete source proof: By definition, the function field is the stalk of the structure sheaf at the generic point. But the generic point of $\operatorname{Spec} R$ corresponds to the zero ideal, and the stalk at the generic point is the localization of $R$ at the zero prime ideal, which is precisely the field of fractions of $R$.
- Lean declaration: `functionField_isFractionRing_of_affine` in `ShadowBench/Source/Main.lean`.
- Statement verification status: pending independent statement/source review.

## Generated Declarations

- `functionField_isFractionRing_of_affine` maps source entry `line-17` to:
  ```lean
  theorem functionField_isFractionRing_of_affine (R : CommRingCat) [IsDomain R] :
      IsFractionRing R (Spec R).functionField
  ```
