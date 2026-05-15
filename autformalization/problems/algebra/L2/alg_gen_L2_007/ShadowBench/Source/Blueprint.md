# Formalization Blueprint: `algebra/L2/alg_gen_L2_007`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
```

## Required Names

- `ABM_algebra_L2_alg_gen_L2_007_item_1`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

## Formalization Rules

```text
open scoped BigOperators
open MvPolynomial

/-
Formalize in Lean the Theorem (ABM_algebra_L2_alg_gen_L2_007_item_1) from Text.

The theorem must be named `ABM_algebra_L2_alg_gen_L2_007_item_1`.
   Matched text (candidate 0, theorem, label=Ch.\ 4 \S 2, Exercise 10): \begin{theorem}[Ch.\ 4 \S 2, Exercise 10] Prove the following ideal-theoretic
                                                                        characterization of $\gcd(f,g)$: given polynomials $f,g,h$ in $k[x_1,\dots,x_n]$, then
                                                                        $h=\gcd(f,g)$ if and only if $h$ is a generator of the smallest principal ideal containing
                                                                        $\langle f,g\rangle$ (i.e., if $\langle h\rangle \subseteq J$, whenever $J$ is a principal
                                                                        ideal such that $J \supseteq \langle f,g\rangle$). \end{theorem}
-/
```
