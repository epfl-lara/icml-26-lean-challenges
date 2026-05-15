# ShadowBench Instructions: `topology/L2/top_gen_L2_012`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Topology.Sheaves.PUnit
import Mathlib.Topology.Sheaves.Functors
```

## Expected Declaration Names

- `skyscraperPresheaf_eq_pushforward`
- `skyscraperPresheaf_isSheaf`

## Formalization Rules

```text
open TopologicalSpace TopCat CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

/-
Formalize in Lean the following named items from Text.

1. Theorem (skyscraperPresheaf_eq_pushforward)
   The theorem must be named `skyscraperPresheaf_eq_pushforward`.
   Matched text (candidate 0, theorem): \begin{theorem} Let $X$ be a topological space. $p_0 \in X$. Let $\mathcal{C}$ be a category
                                        with a terminal object and $A \in \text{Ob}(\mathcal{C})$ be an object of $\mathcal{C}$. A
                                        skyscraper sheaf $\mathcal{F}$ with value $A$ is a presheaf on $X$ with values in
                                        $\mathcal{C}$ such that $\mathcal{F}(U) = A$ if $p_0 \in U$ and $\mathcal{F}(U) =
                                        1_\mathcal{C}$ if $p_0 \notin U$ where $1_\mathcal{C}$ is some terminal…
2. Theorem (skyscraperPresheaf_isSheaf)
   The theorem must be named `skyscraperPresheaf_isSheaf`.
   Matched text (candidate 1, theorem, label=skyscraperPresheaf_isSheaf): \begin{theorem}[skyscraperPresheaf_isSheaf] A skyscraper presheaf with value $A$ is a sheaf.
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
