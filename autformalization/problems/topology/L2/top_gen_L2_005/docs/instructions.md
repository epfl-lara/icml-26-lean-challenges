# ShadowBench Instructions: `topology/L2/top_gen_L2_005`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.EckmannHilton
```

## Expected Declaration Names

- `setoid`

## Formalization Rules

```text
open scoped unitInterval Topology
open Homeomorph

/-
Formalize in Lean the Definition (setoid) from Text.

The definition must be named `setoid`.
   Matched text (candidate 0, definition, label=setoid): \begin{definition}[setoid] Let $X$ be a topological space, $x \in X$ and $\Omega^{N}(X,x)$
                                                         denote the space of \emph{generalized $N$-loops in $X$ based at $x$} i.e. \[ \Omega^{N}(X,x)
                                                         := \Bigl\{\, f : I^{N} \to X \ \text{continuous} \ \Bigm|\ f(y)=x \text{ for all } y \in
                                                         \partial I^{N} \Bigr\} \] With respect to the usual topology on $ \Omega^{N}(X,x)$ inherited
                                                         from the compact-open topology on continuous maps, th…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
