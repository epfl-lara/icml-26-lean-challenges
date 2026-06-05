# ShadowBench Source Blueprint

## Source Document

- Source: `docs/source.tex`.
- Title: ShadowBench algebraic-geometry/L2/alg_sche_L2_001.
- Target Lean entry file: `ShadowBench/Source/Main.lean`.
- Draft status: manual Codex audit completed on 2026-06-04 after the old batch log missed a final literal `PASS`. `ShadowBench/Source/Main.lean` verifies and the theorem is closed by Mathlib's affine function-field theorem.

## Generated File Layout

- `ShadowBench.lean` imports `ShadowBench.Source`.
- `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- `ShadowBench/Source/Main.lean` contains the source-backed declaration `functionField_isFractionRing_of_affine`.

## Import Plan

```lean
import Mathlib.AlgebraicGeometry.FunctionField
```

## Suggested Search Modules

- `Mathlib.RingTheory.Localization.FractionRing` for the `IsFractionRing` representation of fraction fields.
- `Mathlib.AlgebraicGeometry.Scheme` and `Mathlib.AlgebraicGeometry.FunctionField` for `Spec`, `Scheme.functionField`, and the affine-domain function-field instance.

## Source Inventory

- `line-17` (theorem, lines 17-20) - `functionField_isFractionRing_of_affine`.
- Source inventory entry `line-17`.
- Source inventory entry: `line-17`.
- Source inventory label: `line-17`.
- Planned Lean declaration: `functionField_isFractionRing_of_affine`.
- Source inventory entry `line-17`.
- Source inventory entry: `line-17`.
- Source label: `line-17`.
- Source locator: `line-17`.
- Source file: `docs/source.tex`.
- Source environment: theorem.
- Source name: `functionField_isFractionRing_of_affine`.
- Source theorem line: 17.
- Source proof lines: 17-20.
- Source statement: Let $R$ be an integral domain. Then the function field of the affine scheme $\operatorname{Spec} R$ is isomorphic to the field of fractions of $R$.
- Source qualifiers: quantifies over an arbitrary integral domain `R`; object class is the affine scheme `Spec R`; output object is the function field of that scheme; comparison object is the field of fractions of `R`; conclusion is an isomorphism/fraction-field identification; no extra side conditions are stated.
- Complete source proof: By definition, the function field is the stalk of the structure sheaf at the generic point. But the generic point of $\operatorname{Spec} R$ corresponds to the zero ideal, and the stalk at the generic point is the localization of $R$ at the zero prime ideal, which is precisely the field of fractions of $R$.
- Lean declaration: `functionField_isFractionRing_of_affine` in `ShadowBench/Source/Main.lean`.
- Lean coverage: `(R : CommRingCat) [IsDomain R]` covers the integral-domain parameter, `(Spec R).functionField` covers the source function field, and `IsFractionRing R (Spec R).functionField` covers the field-of-fractions identification.
- Scope changes: no mathematical scope change; representation bridge only from an explicit isomorphism phrase to Mathlib's `IsFractionRing` predicate.
- Dependencies: `Mathlib.AlgebraicGeometry.FunctionField`; uses `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Scheme.functionField`, `CommRingCat`, and `IsFractionRing`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

## Statement Inventory

### `line-17` — theorem `functionField_isFractionRing_of_affine`

- Planned Lean declaration: `functionField_isFractionRing_of_affine`.
- Source inventory entry: `line-17`.
- Source label: `line-17`.
- Source locator: `line-17` (`docs/source.tex`, theorem line 17; proof lines 17-20).
- Lean statement:
  ```lean
  theorem functionField_isFractionRing_of_affine (R : CommRingCat) [IsDomain R] :
      IsFractionRing R (Spec R).functionField
  ```
- Source statement: Let $R$ be an integral domain. Then the function field of the affine scheme $\operatorname{Spec} R$ is isomorphic to the field of fractions of $R$.
- Complete source proof: By definition, the function field is the stalk of the structure sheaf at the generic point. But the generic point of $\operatorname{Spec} R$ corresponds to the zero ideal, and the stalk at the generic point is the localization of $R$ at the zero prime ideal, which is precisely the field of fractions of $R$.
- Formal-statement comparison: the source quantifies over an integral domain `R`; Mathlib's algebraic-geometry API packages this as `(R : CommRingCat) [IsDomain R]`. The source's function field of `Spec R` is `(Spec R).functionField`. The source phrase “is isomorphic to the field of fractions of R” is encoded by the standard Mathlib predicate `IsFractionRing R (Spec R).functionField`, which is the canonical API for a field being a fraction ring of `R`.
- Lean coverage: exact up to the standard Mathlib representation bridge from an explicit isomorphism with `FractionRing R` to the proposition `IsFractionRing R (Spec R).functionField`; no theorem content is weakened.
- Scope changes: no mathematical scope change. Representation change only: the source's raw phrase “isomorphic to the field of fractions” is encoded as `IsFractionRing R (Spec R).functionField` rather than as a raw equivalence term.
- Proof sketch: identify the generic point of `Spec R` with the zero prime ideal, then identify the stalk of the structure sheaf at that prime with the localization of `R` away from zero.
- Prover notes: after importing `Mathlib.AlgebraicGeometry.FunctionField`, Mathlib already provides `AlgebraicGeometry.functionField_isFractionRing_of_affine R`, so a later proof pass should be able to close the theorem by applying that instance/theorem.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` propose the required declaration name with parameters `(R : CommRingCat) [IsDomain R]` and target `IsFractionRing R (Spec R).functionField`.
- `docs/skeletons/Skeleton4.lean` uses a weaker placeholder target and was not selected.
- The selected target aligns with the Mathlib theorem in `Mathlib.AlgebraicGeometry.FunctionField` and with the source theorem after the representation bridge above.

## Proof-Handoff Checklist

- [x] Source document and preflight manifest inspected.
- [x] Candidate skeletons compared against the source theorem and Mathlib APIs.
- [x] Source inventory contains `line-17` with statement, complete proof text, dependencies, statement comparison, and prover notes.
- [x] Root project module imports `ShadowBench.Source`, and `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- [x] Project-level Lean verification run; build succeeds with no theorem `sorry` placeholder.
- [x] Manual statement/source review completed for the blueprint and Lean statement on 2026-06-04.
- [x] Proof closed by `AlgebraicGeometry.functionField_isFractionRing_of_affine`.
