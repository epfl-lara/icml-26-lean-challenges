# ShadowBench Instructions: `topology/L3/top_homo_L3_001`

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

- `isUnital_auxGroup`
- `auxGroup_indep`

## Formalization Rules

```text
open scoped unitInterval Topology
open Homeomorph

/-
Formalize in Lean the following named items from Text.

1. Theorem (isUnital_auxGroup)
   The theorem must be named `isUnital_auxGroup`.
   Matched text (candidate 0, theorem): \begin{theorem} Let $X$ be a topological space and $N$ be a finite index set. Let
                                        $\pi_N(X,x)\ :=\ \Omega^{N}(X,x)\big/\simeq_{\partial I^N}$ be the set of homotopy classes
                                        relative to the boundary. Fix $i\in N$. There is an induced identification of $N$-loops as
                                        ``loops of $(N\setminus\{i\})$-loops'', \[ \mathrm{toLoop}_i : \Omega^{N}(X,x)\
                                        \longrightarrow\ \Omega\!\bigl(\Omega^{N\setminus\{i\}}(X,x),\,\mathrm{cons…
2. Theorem (auxGroup_indep)
   The theorem must be named `auxGroup_indep`.
   Matched text (candidate 1, theorem, label=auxGroup_indep): \begin{theorem}[auxGroup_indep] Let $i,j\in N$. Then the groups $\mathrm{auxGroup}(i)$ and
                                                              $\mathrm{auxGroup}(j)$ are isomorphic. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
