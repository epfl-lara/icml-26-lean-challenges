# Formalization Blueprint: `topology/L3/top_gen_L3_002`

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
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.EckmannHilton
```

## Required Names

- `isUnital_auxGroup`
- `auxGroup_indep`

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
open scoped unitInterval Topology
open Homeomorph

/-
Formalize in Lean the following named items from Text.

1. Definition (isUnital_auxGroup)
   The definition must be named `isUnital_auxGroup`.
   Matched text (candidate 0, definition, label=isUnital_auxGroup): \begin{definition}[isUnital_auxGroup] Let $X$ be a topological space and $N$ be a finite
                                                                    index set. Let $\pi_N(X,x)\ :=\ \Omega^{N}(X,x)\big/\simeq_{\partial I^N}$ be the set of
                                                                    homotopy classes relative to the boundary. Fix $i\in N$. There is an induced identification
                                                                    of $N$-loops as ``loops of $(N\setminus\{i\})$-loops'', \[ \mathrm{toLoop}_i :
                                                                    \Omega^{N}(X,x)\ \longrightarrow\ \Omega\!\bigl(\Omega^{N\setminus\{i\…
2. Theorem (auxGroup_indep)
   The theorem must be named `auxGroup_indep`.
   Matched text (candidate 1, theorem, label=auxGroup_indep): \begin{theorem}[auxGroup_indep] Let $i,j\in N$. Then the groups $\mathrm{auxGroup}(i)$ and
                                                              $\mathrm{auxGroup}(j)$ are isomorphic. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
