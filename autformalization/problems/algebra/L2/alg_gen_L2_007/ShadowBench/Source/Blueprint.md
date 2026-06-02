# Formalization Blueprint: `algebra/L2/alg_gen_L2_007`

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
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
```

## Required Names

- `isGCD_iff_span_is_least_principal_above_span_pair`

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
