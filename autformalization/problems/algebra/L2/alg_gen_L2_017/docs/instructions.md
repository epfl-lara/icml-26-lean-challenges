# ShadowBench Instructions: `algebra/L2/alg_gen_L2_017`

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
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
```

## Expected Declaration Names

- `MvPolynomial.monomialIdeal`
- `MonomialOrder.mem_monomialIdeal_iff_divisible`

## Formalization Rules

```text
/-
Formalize in Lean the following named items from the lemma in the text.

1. Definition (monomialIdeal)
   The definition must be named `MvPolynomial.monomialIdeal`.
   Matched text (candidate 0, definition):
Let $I = \langle x^\alpha \mid \alpha \in A \rangle$ be a monomial ideal.

2. Lemma (mem_monomialIdeal_iff_divisible)
   The lemma must be named `MonomialOrder.mem_monomialIdeal_iff_divisible`.
   Matched text (candidate 0, lemma, label=mem_monomialIdeal_iff_divisible):
\begin{lemma}[mem_monomialIdeal_iff_divisible]\label{lem:mem_monomialIdeal_iff_divisible}
    Let $I = \langle x^\alpha \mid \alpha \in A \rangle$ be a monomial ideal.
    Then a monomial $x^\beta$ lies in $I$ if and only if $x^\beta$ is divisible by
    $x^\alpha$ for some $\alpha \in A$.
\end{lemma}

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
