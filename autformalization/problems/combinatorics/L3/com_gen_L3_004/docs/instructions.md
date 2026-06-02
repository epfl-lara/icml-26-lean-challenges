# ShadowBench Instructions: `combinatorics/L3/com_gen_L3_004`

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
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Copy
```

## Expected Declaration Names

- `IsExtremal.prop`
- `exists_isExtremal_iff_exists`

## Formalization Rules

```text
open Finset Fintype

/-
Formalize in Lean the following named items from Text.

1. Lemma (IsExtremal.prop)
   The lemma must be named `IsExtremal.prop`.
   Matched text (candidate 0, theorem, label=Extremal graph): \begin{theorem}[Extremal graph] Let \(V\) be a finite vertex set, and let \(p\) be a
                                                              property of simple graphs on \(V\). A simple graph \(G\) on \(V\) is called \emph{extremal
                                                              with respect to \(p\)} if \[ p(G) \quad\text{and}\quad \text{for every simple graph } G'
                                                              \text{ on } V \text{ with } p(G'), \; |E(G')| \le |E(G)|. \] \end{theorem}
2. Theorem (exists_isExtremal_iff_exists)
   The theorem must be named `exists_isExtremal_iff_exists`.
   Matched text (candidate 1, theorem, label=exists_isExtremal_iff_exists): \begin{theorem}[exists_isExtremal_iff_exists] Let \(V\) be a finite vertex set, and let
                                                                            \(p\) be a property of simple graphs on \(V\). Then the following are equivalent: \[
                                                                            \exists\, G \text{ on } V \text{ such that } p(G) \quad\Longleftrightarrow\quad \exists\, G
                                                                            \text{ on } V \text{ that is extremal with respect to } p. \] \end{theorem}

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
