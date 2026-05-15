# ShadowBench Instructions: `topology/L2/top_gen_L2_013`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Sites.LocallySurjective
```

## Expected Declaration Names

- `IsLocallySurjective`
- `locally_surjective_iff_surjective_on_stalks`

## Formalization Rules

```text
open CategoryTheory
open TopologicalSpace
open Opposite
open scoped AlgebraicGeometry

/-
Formalize in Lean the following named items from Text.

1. Definition (IsLocallySurjective)
   The definition must be named `IsLocallySurjective`.
   Matched text (candidate 0, theorem): \begin{theorem} A map of presheaves \( T : \mathcal{F} \to \mathcal{G} \) is \emph{locally
                                        surjective} if for every open set \( U \), every section \( t \in \mathcal{G}(U) \), and
                                        every point \( x \in U \), there exists an open set \( V \) such that \( x \in V \subseteq U
                                        \) and a section \( s \in \mathcal{F}(V) \) such that \( T(s) = t|_V \). \end{theorem}
2. Theorem (locally_surjective_iff_surjective_on_stalks)
   The theorem must be named `locally_surjective_iff_surjective_on_stalks`.
   Matched text (candidate 1, theorem, label=locally_surjective_iff_surjective_on_stalks): \begin{theorem}[locally_surjective_iff_surjective_on_stalks] A morphism \( T : \mathcal{F}
                                                                                           \to \mathcal{G} \) of presheaves is locally surjective if and only if for every point \( x
                                                                                           \in X \), the induced map on stalks \( \mathcal{F}_x \to \mathcal{G}_x \) is surjective.
                                                                                           \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
