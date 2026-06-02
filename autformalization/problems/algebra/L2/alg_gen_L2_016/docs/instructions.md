# ShadowBench Instructions: `algebra/L2/alg_gen_L2_016`

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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
```

## Expected Declaration Names

- `span_pow_card_mul_le_span_image_pow`

## Formalization Rules

```text
/-
Formalize in Lean the Theorem (span_pow_card_mul_le_span_image_pow) from Text.

The theorem must be named `span_pow_card_mul_le_span_image_pow`.
   Matched text (candidate 0, theorem, label=span_pow_card_mul_le_span_image_pow): \begin{theorem}[span_pow_card_mul_le_span_image_pow] Let $s=\{g_1,\dots,g_r\}$ be a finite
                                                                                   subset of $k[x_1,\dots,x_n]$. Set $J := \langle s\rangle$ and let $M\ge 0$. Then \[ J^{\,rM}
                                                                                   \;\subseteq\; \left\langle\, g^M \mid g\in s \,\right\rangle. \] \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
