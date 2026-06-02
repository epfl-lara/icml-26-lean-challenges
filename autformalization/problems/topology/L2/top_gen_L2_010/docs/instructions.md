# ShadowBench Instructions: `topology/L2/top_gen_L2_010`

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
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Operator.Prod
```

## Expected Declaration Names

- `Trivialization.pullback_linear`
- `VectorBundle.pullback`

## Formalization Rules

```text
open Bundle Set FiberBundle

/-
Formalize in Lean the following named items from Text.

1. Definition (Trivialization.pullback_linear)
   The definition must be named `Trivialization.pullback_linear`.
   Matched text (candidate 0, definition, label=Trivialization.pullback_linear): \begin{definition}[Trivialization.pullback_linear] Let $E$ be a vector bundle over a base
                                                                                 space $B$ with fiber $F$, where $F$ is a normed space over a normed field $k$. Given a
                                                                                 continuous map $f: B' \to B$, the pullback bundle $f^*E$ is defined to be a vector bundle
                                                                                 over $B'$ whose fiber $(f^*E)_x$ is defined as $E_{f(x)}$ for each $x \in B'$. It is a
                                                                                 disjoint union $\bigsqcup_{x \in B'} (f^*E)_x$ of all these fiber…
2. Theorem (VectorBundle.pullback)
   The theorem must be named `VectorBundle.pullback`.
   Matched text (candidate 1, theorem, label=VectorBundle.pullback): \begin{theorem}[VectorBundle.pullback] Given a vector bundle $E$ over a base space $B$ with
                                                                     fiber $F$ and a continuous map $f:B' \to B$, the pullback bundle $f^*E$ over $B'$ inherits
                                                                     the structure of a vector bundle. \end{theorem}

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
