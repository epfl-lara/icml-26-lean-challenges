# ShadowBench Instructions: `algebra/L2/alg_gen_L2_007`

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
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
```

## Expected Declaration Names

- `isGCD_iff_span_is_least_principal_above_span_pair`

## Formalization Rules

```text
/-
Formalize in Lean the named statement from the theorem in the text.

The Lean declaration must be named exactly:
- `isGCD_iff_span_is_least_principal_above_span_pair`

Matched text (candidate 0, theorem):
\begin{theorem}
Given polynomials $f,g,h$ in $k[x_1,\dots,x_n]$, where
$h=\gcd(f,g)$ means that $h$ divides both $f$ and $g$ and is divisible by every common divisor of
$f$ and $g$, prove that $h=\gcd(f,g)$ if and only if $\langle h\rangle$ is the smallest
principal ideal containing $\langle f,g\rangle$.
\end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
