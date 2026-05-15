# ShadowBench Instructions: `topology/L2/top_gen_L2_018`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.LocallySurjective
```

## Expected Declaration Names

- `epi_of_shortExact`
- `of_shortExact_of_isFlasque`

## Formalization Rules

```text
open TopCat TopologicalSpace Opposite CategoryTheory Presheaf Limits
open scoped AlgebraicGeometry

/-
Formalize in Lean the following named items from Text.

1. Theorem (epi_of_shortExact)
   The theorem must be named `epi_of_shortExact`.
   Matched text (candidate 0, theorem): \begin{theorem}Let \(X\) be a topological space. A presheaf \(F\) on \(X\) is called
                                        \emph{flasque} if for every inclusion of open sets \[ V \subseteq U, \] the restriction map
                                        \[ F(U)\to F(V) \] is an epimorphism. A sheaf is called \emph{flasque} if its underlying
                                        presheaf is flasque. \end{theorem}
2. Theorem (of_shortExact_of_isFlasque)
   The theorem must be named `of_shortExact_of_isFlasque`.
   Matched text (candidate 1, theorem, label=of_shortExact_of_isFlasque): \begin{theorem}[of_shortExact_of_isFlasque]\label{thm:quotient-flasque} Suppose \[ 0 \to
                                                                          \mathcal F \to \mathcal G \to \mathcal H \to 0 \] is a short exact sequence of sheaves of
                                                                          abelian groups on \(X\). If \(\mathcal F\) and \(\mathcal G\) are flasque, then \(\mathcal
                                                                          H\) is flasque. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
