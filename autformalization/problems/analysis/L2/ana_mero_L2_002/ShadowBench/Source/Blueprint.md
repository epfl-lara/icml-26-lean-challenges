# Formalization Blueprint: `analysis/L2/ana_mero_L2_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Import Plan

Direct Lean imports used by `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.Analysis.Meromorphic.Divisor
```

`Mathlib.Analysis.Meromorphic.Divisor` is the direct Mathlib home of `MeromorphicOn.divisor`; it publicly imports the starting modules listed in `docs/instructions.md` (`WithTop.Untop0`, `Meromorphic.Order`, and `Topology.LocallyFinsupp`).

## Suggested Search Modules

These are search/proof hints, not direct imports unless a later proof run shows they are needed explicitly.

- `Mathlib.Analysis.Meromorphic.Divisor`
- `Mathlib.Analysis.Meromorphic.Order`
- `Mathlib.Analysis.Meromorphic.Basic`

Search results used during planning:

- `MeromorphicOn.divisor`, `MeromorphicOn.divisor_def`, `MeromorphicOn.divisor_apply` from `Mathlib.Analysis.Meromorphic.Divisor`.
- `meromorphicOrderAt`, `meromorphicOrderAt_add` from `Mathlib.Analysis.Meromorphic.Order`.
- `Meromorphic.meromorphicAt` / related `MeromorphicOn` pointwise meromorphicity lemmas from `Mathlib.Analysis.Meromorphic.Basic`.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: one source-backed theorem skeleton, `min_divisor_le_divisor_add`, with a compact source proof/prover-note doc comment and a `by sorry` proof placeholder for the later prover workflow.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so project-level `lake build` covers the generated target module.

No split into additional generated files is planned: the source document contains a single theorem, and one file keeps the statement/source mapping clear.

## Required Names

- `min_divisor_le_divisor_add`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` introduce an artificial `IsMeromorphicOn` class and a `div_U` definition with a construction `sorry`. Those construction stubs do not match Mathlib's meromorphic API and would block proof handoff, so they were rejected.
- `docs/skeletons/Skeleton4.lean` has the closest Mathlib shape: `NontriviallyNormedField`, `NormedAddCommGroup`, `NormedSpace`, pointwise meromorphic hypotheses, finite order of the sum, and a divisor inequality. The final draft adopts the Mathlib object-class and name style from Skeleton4, but replaces the non-existing/ambiguous `OrderAt` and unqualified `divisor 𝕜 E U f z` syntax with Mathlib's actual `meromorphicOrderAt` and `MeromorphicOn.divisor f U z`.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Planned Lean declarations: `min_divisor_le_divisor_add` in `ShadowBench/Source/Main.lean`.
- Source locator: `docs/source.tex`, theorem environment lines 17-24; proof environment lines 26-97.
- Source statement:
  ```text
  Let f_1,f_2 : \mathbb K \to E be meromorphic on a set U \subseteq \mathbb K, and let z \in U.
  Assume that the order of f_1+f_2 at z is finite. Then
  min(div_U(f_1)(z), div_U(f_2)(z)) <= div_U(f_1+f_2)(z).
  ```
- Planned Lean statement:
  ```lean
  theorem min_divisor_le_divisor_add {𝕜 : Type*} [NontriviallyNormedField 𝕜]
      {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
      {U : Set 𝕜} {f₁ f₂ : 𝕜 → E} {z : 𝕜}
      (hf₁ : MeromorphicOn f₁ U) (hf₂ : MeromorphicOn f₂ U)
      (hz : z ∈ U) (h_fin : meromorphicOrderAt (f₁ + f₂) z ≠ ⊤) :
      min (MeromorphicOn.divisor f₁ U z) (MeromorphicOn.divisor f₂ U z) ≤
        MeromorphicOn.divisor (f₁ + f₂) U z
  ```
- Skeleton candidate used: Skeleton4 shaped the final statement's Mathlib class assumptions; Skeleton1-3 were rejected because their custom class/definition stubs are not source-backed Mathlib constructions.
- Dependencies:
  - `MeromorphicOn.divisor` as the Mathlib formalization of `div_U`.
  - `meromorphicOrderAt` as the Mathlib formalization of `ord_z`.
  - `MeromorphicOn.divisor_apply` / `MeromorphicOn.divisor_def` for reducing divisor values at `z` to `(meromorphicOrderAt f z).untop₀` under meromorphicity and `z ∈ U`.
  - `meromorphicOrderAt_add` for the source's standard order inequality for sums.
  - Expected proof support from `hf₁ z hz`, `hf₂ z hz`, and `hf₁.add hf₂` or the corresponding Mathlib `MeromorphicOn` addition lemma.
- Formal statement review:
  - The source's field `\mathbb K` and codomain `E` are represented by Mathlib's meromorphic function API: `[NontriviallyNormedField 𝕜]`, `[NormedAddCommGroup E]`, and `[NormedSpace 𝕜 E]`.
  - Source functions `f_1,f_2 : \mathbb K \to E` are Lean functions `f₁ f₂ : 𝕜 → E`.
  - Source meromorphic-on hypotheses are represented by `hf₁ : MeromorphicOn f₁ U` and `hf₂ : MeromorphicOn f₂ U`.
  - Source `z ∈ U` is represented by `hz : z ∈ U`.
  - Source finite order of the sum is represented by `h_fin : meromorphicOrderAt (f₁ + f₂) z ≠ ⊤`.
  - Source divisor value `div_U(f)(z)` is represented by `MeromorphicOn.divisor f U z`, an integer value with Mathlib's convention that the divisor is zero outside `U` or at infinite order.
  - Source conclusion is represented exactly as the integer inequality `min (...) (...) ≤ ...`.
- Source qualifiers:
  - Mathematical object class: meromorphic vector-valued functions on a set over a nontrivially normed field.
  - Quantifier order: choose the field and codomain/typeclass instances, then `U`, `f₁`, `f₂`, `z`, then assumptions `hf₁`, `hf₂`, `hz`, and finite order of the sum.
  - Parameter domain: `U : Set 𝕜`, `z : 𝕜`, with side condition `z ∈ U`.
  - Output codomain: divisor values in `ℤ`; order values in `WithTop ℤ` before applying divisor's finite/infinite convention.
  - Equality/image condition: none beyond identifying source notation with Mathlib definitions.
  - Side conditions: `f₁` and `f₂` meromorphic on `U`; `meromorphicOrderAt (f₁ + f₂) z` finite.
  - Follow-on claims: none.
- Lean coverage:
  - The theorem declaration covers the object class, functions, domain, point membership, meromorphic-on hypotheses, finite-order side condition, and divisor inequality.
  - The representation bridge for source notation is recorded by using Mathlib's existing definitions `MeromorphicOn.divisor` and `meromorphicOrderAt`; no new construction stub is introduced.
- Scope changes:
  - Lean makes explicit the normed-field/normed-space assumptions required by Mathlib's meromorphic API; these are implicit prerequisites of the source's meromorphic terminology.
  - The source statement says `z ∈ U`; the source proof nevertheless begins with a `z ∉ U` case. The Lean statement follows the theorem statement and keeps `hz : z ∈ U`; the outside-`U` case is noted as proof commentary only, not a separate theorem branch.
  - No intentional weakening of the theorem conclusion is made.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof text:
  ```text
  We distinguish cases.

  Case 1: z notin U. By definition of the divisor, all divisor values at z vanish:
  div_U(f_1)(z) = div_U(f_2)(z) = div_U(f_1+f_2)(z) = 0.
  Hence min(0,0) <= 0, and the inequality holds.

  Case 2: z in U. Since f_1, f_2, and f_1+f_2 are meromorphic on U, their divisors at z are given by their orders, with the convention that infinite order contributes zero:
  div_U(f_i)(z) = ord_z(f_i) if ord_z(f_i) is finite, and 0 if ord_z(f_i) = infinity, for i=1,2, and similarly for f_1+f_2.

  Case 2a: ord_z(f_1) = infinity. Then div_U(f_1)(z)=0, so
  min(div_U(f_1)(z), div_U(f_2)(z)) = 0 <= div_U(f_1+f_2)(z), and the claim follows.

  Case 2b: ord_z(f_2)=infinity. This is symmetric to the previous case and yields the same conclusion.

  Case 2c: ord_z(f_1) and ord_z(f_2) are both finite. In this case, the divisor values coincide with the actual orders, and
  min(div_U(f_1)(z), div_U(f_2)(z)) = min(ord_z(f_1), ord_z(f_2)).
  Since f_1 and f_2 are meromorphic at z, the standard inequality for orders of sums gives
  min(ord_z(f_1), ord_z(f_2)) <= ord_z(f_1+f_2).
  By the assumption that ord_z(f_1+f_2) is finite, we have
  ord_z(f_1+f_2) = div_U(f_1+f_2)(z), and combining the inequalities yields the desired result.
  ```
- Prover notes:
  - Start with `rw [MeromorphicOn.divisor_apply hf₁ hz, MeromorphicOn.divisor_apply hf₂ hz]` and the corresponding divisor formula for `f₁ + f₂`; establish sum meromorphic on `U` from `hf₁` and `hf₂`.
  - Convert the finite-order assumption `h_fin` into an `untop₀` comparison goal. The key Mathlib order inequality is `meromorphicOrderAt_add (hf₁ z hz) (hf₂ z hz)`.
  - The source proof's infinite-order cases correspond to `untop₀` mapping `⊤` to `0`. Expect case splits on whether each `meromorphicOrderAt fᵢ z = ⊤`, or use available `WithTop.untop₀` lemmas plus monotonicity under the finite right side.
  - Source-proof caveat for proving only: the written infinite-order subcases say `min(0, div f₂)=0`; for possible poles this equality should not be used literally. The statement is unaffected; prove those branches via the Mathlib order inequality/`untop₀` monotonicity or by reducing to the unchanged summand when a function is identically zero near `z`.
  - Do not alter the theorem statement during proof unless an independent statement/source review requests a correction.

## Handoff Notes

- The only intended proof obligation in the generated target file is theorem `min_divisor_le_divisor_add`.
- Proof search should not start until the independent statement/source verification pass approves or corrects the blueprint and Lean statement.
- Suggested command after review approval: `/prove ShadowBench/Source/Main.lean min_divisor_le_divisor_add`.
