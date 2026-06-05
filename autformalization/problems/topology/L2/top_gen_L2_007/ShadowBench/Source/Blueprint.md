# Formalization Blueprint: `topology/L2/top_gen_L2_007`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes only. The final theorem statement was compared against `docs/source.tex` and the source proof.

## Import Plan

```lean
import Mathlib.Topology.Compactness.Bases
import Mathlib.Topology.NoetherianSpace
```

These are the direct imports in `ShadowBench/Source/Main.lean`, following `docs/instructions.md`. They provide the topological compactness/embedding vocabulary needed for the local definition and theorem skeleton.

## Suggested Search Modules

- `Mathlib.Topology.QuasiSeparated`: contains Mathlib's canonical `IsQuasiSeparated` predicate and an existing theorem `IsQuasiSeparated.image_of_isEmbedding`; useful as proof guidance, but not imported directly in this draft because it would collide with the required declaration name.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the local `IsQuasiSeparated` predicate and source theorem skeleton `IsQuasiSeparated.image_of_isEmbedding` with a `sorry` proof for the later prover workflow.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so project-level builds cover the generated target module.

## Required Names

- `IsQuasiSeparated.image_of_isEmbedding`

## Source Statement Inventory

### line-17

- Planned Lean declarations: `IsQuasiSeparated.image_of_isEmbedding`
- Source locator: `line-17`; `docs/source.tex`, theorem lines 17-19 and proof lines 21-22.
- Source statement: Let $S \subseteq X$ be a quasiseparated set and $h:X \to Y$ is a topological embedding. Then, $f(S)$ is quasiseparated.
- Supporting Lean declarations: `IsQuasiSeparated`
- Skeleton candidate used: `docs/skeletons/Skeleton4.lean` shaped the final theorem statement because it uses the required dotted name, `IsQuasiSeparated`, `IsEmbedding`, and image notation `f '' s`. `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` were rejected because they use the typo `IsQuasiSeparable` and/or add a `True` exact-name stub.
- Dependencies: `Set`, `TopologicalSpace`, `IsOpen`, `IsCompact`, `IsEmbedding`, image/preimage operations, and compactness preservation under embeddings/continuous maps for the later proof.
- Source qualifiers:
  - Mathematical object class: subsets of topological spaces, not a global space-level class.
  - Quantifier order: topological spaces `X`, `Y`; subset `s : Set X`; map `f : X → Y`; hypothesis `hs : IsQuasiSeparated s`; embedding hypothesis `hf : IsEmbedding f`; conclusion about `f '' s`.
  - Parameter domain/codomain: `s ⊆ X` and `f : X → Y` with topologies on both spaces.
  - Equality/image condition: image subset is formalized as `f '' s`.
  - Side conditions: no Hausdorff, openness of the embedding, or Noetherian assumption is added.
  - Follow-on claim: the conclusion is exactly quasi-separatedness of the image subset.
- Lean coverage: exact set-level coverage after resolving the source's notation inconsistency between `h` and `f` to one embedding map `f`. The local definition
  `IsQuasiSeparated s := ∀ U V, U ⊆ s → IsOpen U → IsCompact U → V ⊆ s → IsOpen V → IsCompact V → IsCompact (U ∩ V)`
  records the intended compact-open-intersection meaning used in the source proof. This is the same predicate shape as Mathlib's `Mathlib.Topology.QuasiSeparated` definition; that module also contains an already-proved theorem with the same name, so the draft keeps the local definition/proof obligation rather than importing the theorem and causing a name collision with the required declaration.
- Scope changes: the only source ambiguity is the statement's use of `h` for the embedding and `f(S)` for the image; Lean uses a single map `f`. No mathematical weakening or strengthening is intended.
- Formal statement review: the Lean theorem states that if `s` is quasi-separated and `f` is an embedding, then `f '' s` is quasi-separated, matching the source theorem's set-level reading and proof.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: "Let $U,V$ be compact open subsets of $f(S)$. Since $f$ is an embedding, $f^{-1}(U), f^{-1}(V)$ are compact open subsets of $S$. Then $f^{-1}(U) \cap f^{-1}(V)$ is compact since $S$ is quasiseparated. Hence, $U \cap V = f(f^{-1}(U) \cap f^{-1}(V))$ is compact and thus $f(S)$ is quasiseparated."
- Source proof / prover notes: unfold `IsQuasiSeparated`; for compact open `U V ⊆ f '' s`, apply `hs` to `f ⁻¹' U` and `f ⁻¹' V`; use `hf.continuous` for openness/preimage facts, `hf.isCompact_iff` to transport compactness between a subset of the range and its preimage, and `hf.injective` plus `Set.image_preimage_eq_inter_range`/`Set.preimage_inter` to identify the image of the compact preimage intersection with `U ∩ V`.

## Formalization Rules

```text
open Set TopologicalSpace Topology

/-
Formalize in Lean the Theorem (IsQuasiSeparated.image_of_isEmbedding) from Text.

The theorem must be named `IsQuasiSeparated.image_of_isEmbedding`.
   Matched text (candidate 0, theorem, label=IsQuasiSeparated.image_of_isEmbedding): \begin{theorem}[IsQuasiSeparated.image_of_isEmbedding] Let $S \subseteq X$ be a
                                                                                     quasiseparated set and $h:X \to Y$ is a topological embedding. Then, $f(S)$ is
                                                                                     quasiseparated. \end{theorem}
-/
```

## Handoff Notes

- Source theorem inventory entry `line-17` is recorded with a source pointer and the complete source proof text.
- The blueprint import plan matches the direct imports in `ShadowBench/Source/Main.lean`.
- The root project module imports the generated target module path.
- Independent statement/source verification is still required before the proof queue should start.
