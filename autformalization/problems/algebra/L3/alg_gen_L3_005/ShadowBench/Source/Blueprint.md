# Formalization Blueprint: `algebra/L3/alg_gen_L3_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file formalization containing the explicit polynomial-ring bridge definitions and the two source-backed theorem skeletons.
- `ShadowBench/Source.lean`: root project module importing `ShadowBench.Source.Main`, so project-level `lake build` covers the generated target module.

No additional Lean files are planned for this small source document.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.

## Import Plan

```lean
import Mathlib
import Aesop
```

These are the direct imports used by `ShadowBench/Source/Main.lean`, matching the allowed starting import block in `docs/instructions.md`.

## Suggested Search Modules

Non-gating search/proof hints for the later prover queue:

- `Mathlib.RingTheory.Ideal.IsPrimary`: `Ideal.IsPrimary`, `Ideal.isPrimary_of_isMaximal_radical`.
- `Mathlib.Order.Irreducible`: `InfIrred` and basic lattice irreducibility facts.
- `Mathlib.RingTheory.MvPolynomial.Ideal`: monomial ideal membership lemmas such as `MvPolynomial.mem_ideal_span_monomial_image` and `MvPolynomial.mem_ideal_span_monomial_image_iff_dvd`.
- `Mathlib.Algebra.MvPolynomial.Basic`: variables `MvPolynomial.X` and monomial notation.

## Required Names

- `I_isPrimary`
- `I_not_infIrred`

## Representation Bridge Definitions

The source writes the polynomial ring as `k[x, y]`. The Lean draft makes this representation explicit with implemented companion definitions:

- `algGenL3005Ring k := MvPolynomial (Fin 2) k`.
- `algGenL3005_x k := MvPolynomial.X 0` and `algGenL3005_y k := MvPolynomial.X 1`.
- `algGenL3005_I k := Ideal.span {x^2, x*y, y^2}`.
- `algGenL3005_J k := Ideal.span {x^2, y}`.
- `algGenL3005_K k := Ideal.span {x, y^2}`.

This bridge is an explicit Lean representation of the source notation, not a mathematical weakening. No construction stubs are planned.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem lines 17–23 and proof lines 23–45.
- Source statement: Let `I = <x^2, xy, y^2> ⊆ k[x,y]`; item `I_isPrimary` states that `I` is primary; item `I_not_infIrred` states `I = <x^2,y> ∩ <x,y^2>` and concludes that `I` is not irreducible.
- Planned Lean declarations: `I_isPrimary`, `I_not_infIrred`.
- Skeleton candidate used: `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` shaped the field parameter and polynomial-ring encoding; their second statement used `¬ Irreducible I`, so this draft changes it to `¬ InfIrred I` because the source proof is about a nontrivial intersection of ideals. `Skeleton4.lean` is malformed and was not adopted.
- Dependencies: implemented bridge definitions `algGenL3005Ring`, `algGenL3005_x`, `algGenL3005_y`, `algGenL3005_I`, `algGenL3005_J`, and `algGenL3005_K`; Mathlib concepts `MvPolynomial`, `Ideal.span`, `Ideal.IsPrimary`, ideal infimum `⊓`, and `InfIrred`.
- Formal statement review: The source implicitly quantifies over a field `k`; the Lean statements explicitly quantify `(k : Type*) [Field k]`. The source ring `k[x,y]` is represented by `algGenL3005Ring k = MvPolynomial (Fin 2) k` with `x = X 0` and `y = X 1`. The ideals `I`, `J`, and `K` are represented by `algGenL3005_I k`, `algGenL3005_J k`, and `algGenL3005_K k`. The source’s ideal-intersection irreducibility conclusion is represented as `¬ InfIrred (algGenL3005_I k)`, not as monoid-factorization irreducibility `¬ Irreducible I`.
- Source qualifiers: mathematical object class is ideals in the polynomial ring `k[x,y]` over an arbitrary field `k`; quantifier order is for every field `k`, define the fixed variables and ideals, then assert the two named conclusions; parameter domain is an arbitrary Lean type `k` with `[Field k]`; output codomain is propositions about `Ideal (algGenL3005Ring k)`; equality condition is `I = J ⊓ K`, where `⊓` is ideal intersection; side conditions are exactly the field assumption on `k`; follow-on claims are that `I` is primary and that `I` is not irreducible in the intersection/infimum sense.
- Lean coverage: `I_isPrimary` covers the primary-ideal claim for the represented ideal `I`; `I_not_infIrred` covers the stated intersection equality and the follow-on non-irreducibility claim using `InfIrred`; the bridge definitions cover the source representation of `k[x,y]`, `x`, `y`, `I`, `J`, and `K`.
- Scope changes: representation bridge only: source notation `k[x,y]` is encoded as `MvPolynomial (Fin 2) k` with the ordered variables `0 ↦ x`, `1 ↦ y`; all mathematical qualifiers from the source statement are represented.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof: Let `m := <x,y>`. Then `I = <x^2,xy,y^2> = m^2` and `sqrt I = sqrt(m^2) = m`. Since `k[x,y]/m ≃ k`, `m` is maximal. Thus `sqrt I` is maximal, hence `I` is primary. Put `J := <x^2,y>` and `K := <x,y^2>`. Clearly `I ⊆ J ∩ K`. Conversely, for a monomial `x^a y^b`, membership in `J ∩ K` is equivalent to `(a ≥ 2 or b ≥ 1)` and `(a ≥ 1 or b ≥ 2)`, hence the monomial is divisible by `x^2`, `xy`, or `y^2`; since the ideals are monomial ideals this gives `J ∩ K ⊆ I`. Finally, `y ∈ J \ I` and `x ∈ K \ I`, so the intersection is nontrivial and `I` is not irreducible.
- Source proof / prover notes: For `I_isPrimary`, introduce `m = <x,y>`, identify `I` with `m^2`, identify `radical I` with `m`, show `m` is maximal using the quotient `k[x,y]/m ≃ k`, then apply the Mathlib theorem that an ideal with maximal radical is primary. For `I_not_infIrred`, prove `I = J ⊓ K` by monomial ideal membership; for a monomial `x^a y^b`, membership in the intersection is equivalent to `(a ≥ 2 or b ≥ 1)` and `(a ≥ 1 or b ≥ 2)`, hence divisibility by one of `x^2`, `xy`, or `y^2`; then prove `I ≠ J` using `y ∈ J \ I` and `I ≠ K` using `x ∈ K \ I`, and use that equality as a nontrivial infimum to refute `InfIrred I`.

## Formalization Rules

```text
open MvPolynomial

/-
Formalize in Lean the two named statements from the theorem in the text.

The Lean declarations must be named:
- `I_isPrimary`
- `I_not_infIrred`

Matched text (candidate 0, theorem):
\begin{theorem}
Let $I = \langle x^2, xy, y^2 \rangle \subseteq k[x, y]$.
\begin{enumerate}
    \item[I_isPrimary] $I$ is primary.
    \item[I_not_infIrred] $I = \langle x^2, y \rangle \cap \langle x, y^2 \rangle$ and conclude that $I$ is not irreducible.
\end{enumerate}
\end{theorem}
-/
```
