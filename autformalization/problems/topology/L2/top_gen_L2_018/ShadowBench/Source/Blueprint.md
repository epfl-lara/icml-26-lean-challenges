# Formalization Blueprint: `topology/L2/top_gen_L2_018`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.LocallySurjective
```

## Required Names

- `epi_of_shortExact`
- `of_shortExact_of_isFlasque`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

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
