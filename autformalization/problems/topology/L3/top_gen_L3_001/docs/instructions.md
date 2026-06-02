# ShadowBench Instructions: `topology/L3/top_gen_L3_001`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Candidate Skeletons

Dataset: `Lemmy00/ShadowBench-skeletons-prod`

- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Treat these as candidate statement/definition shapes, not authoritative answers. Prefer the source theorem and formalization rules when candidates disagree.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.EckmannHilton
```

## Expected Declaration Names

- `homotopyTo`
- `homotopyTo_apply`
- `homotopicTo`

## Formalization Rules

```text
open scoped unitInterval Topology
open Homeomorph

/-
Formalize in Lean the following named items from Text.

1. Definition (homotopyTo)
   The definition must be named `homotopyTo`.
   Matched text (candidate 0, theorem): \begin{theorem} Let $X$ be a topological space, let $x \in X$, and let $N$ be a finite index
                                        set. Fix an index $i \in N$, and write $N \setminus i := N \setminus \{i\}$. Let \[ \Psi_i :
                                        I \times I^{N\setminus i} \xrightarrow{\cong} I^N \] denote the canonical homeomorphism that
                                        inserts the coordinate $t \in I$ in the $i$-th position. For a generalized $N$-loop \[ p \in
                                        \Omega^{N}(X,x), \qquad p : I^N \to X, \] defin…
2. Theorem (homotopyTo_apply)
   The theorem must be named `homotopyTo_apply`.
   Matched text (candidate 1, lemma): \begin{lemma} We have a well-defined map \[ \mathrm{toLoop}_i : \Omega^{N}(X,x)
                                      \longrightarrow \Omega\bigl(\Omega^{N\setminus i}(X,x),\,\mathrm{const}\bigr), \] sending an
                                      $N$-dimensional generalized loop to a loop of generalized $(N\setminus i)$-loops based at
                                      the constant loop. \end{lemma}
3. Theorem (homotopicTo)
   The theorem must be named `homotopicTo`.
   Matched text (candidate 2, theorem, label=homotopicTo): \begin{theorem}[homotopicTo] Let $X$ be a topological space, $x\in X$, and $N$ an index set.
                                                           Fix $i\in N$. Let \[ p,q \in \Omega^{N}(X,x). \] Assume that the associated paths \[
                                                           \mathrm{toLoop}_i(p),\ \mathrm{toLoop}_i(q) : I \longrightarrow
                                                           \Omega^{N\setminus\{i\}}(X,x) \] are homotopic relative to endpoints. Then $p$ and $q$ are
                                                           homotopic relative to the boundary $\partial I^{N}$. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
