# ShadowBench Instructions: `algebra/L3/alg_grob_L3_001`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal
```

## Expected Declaration Names

- `IsFinite`
- `IsProjective`
- `finite_implies_projective`

## Formalization Rules

```text
open CategoryTheory

/-
Formalize in Lean the following named items from Text.

1. Definition (IsFinite)
   The definition must be named `IsFinite`.
   Matched text (candidate 0, theorem, label=Finite morphism): \begin{theorem}[Finite morphism] A morphism of schemes $f : X \to Y$ is called \emph{finite}
                                                               if it is affine and for every affine open subset $U = \operatorname{Spec}(A) \subset Y$, the
                                                               preimage $f^{-1}(U)$ is affine, say $f^{-1}(U) = \operatorname{Spec}(B)$, where $B$ is a
                                                               finite $A$-module. \end{theorem}
2. Definition (IsProjective)
   The definition must be named `IsProjective`.
   Matched text (candidate 1, definition, label=Projective morphism): \begin{definition}[Projective morphism] A morphism of schemes $f : X \to Y$ is called
                                                                      \emph{projective} if there exists an integer $n \ge 0$ and a closed immersion \[ i : X
                                                                      \hookrightarrow \mathbb{P}^n_Y \] such that $f$ factors as \[ X \xrightarrow{i}
                                                                      \mathbb{P}^n_Y \to Y, \] where $\mathbb{P}^n_Y$ denotes the projective $n$-space over $Y$.
                                                                      \end{definition}
3. Theorem (finite_implies_projective)
   The theorem must be named `finite_implies_projective`.
   Matched text (candidate 2, theorem, label=finite_implies_projective): \begin{theorem}[finite_implies_projective] Let $f : X \to Y$ be a finite morphism of
                                                                         schemes. Then $f$ is projective. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
