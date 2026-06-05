# Formalization Blueprint: `number-theory/L4/nt_gen_L4_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Documents and Support Files Read

- `docs/source.tex` via `formalization_document_inspect`; theorem-like blocks `line-17`, `line-21`, `line-28`, `line-35`, and `line-48`.
- Preflight manifest: `.epflemma/workflow-state/formalization/docs-source/manifest.json`.
- Planner context: `.epflemma/workflow-state/formalization/docs-source/context.md`.
- Companion instructions: `docs/instructions.md`.
- Skeleton README: `docs/skeletons/README.md`.
- Candidate skeletons: `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, `Skeleton3.lean`, and `Skeleton4.lean`.
- No bibliography files, citations, labels, figures, or project-local PDFs were listed in the manifest.

## Search Record

- Lean search found `Finset.lcm` in `Mathlib.Algebra.GCDMonoid.Finset`, matching the candidate skeleton definition of the least common multiple over a finite interval.
- A remote/semantic search suggested `Nat.lcmUpto`, but content search in this project's Mathlib checkout found no such constant; the generated Lean therefore uses the available finite-set LCM representation.

## Import Plan

```lean
import Mathlib
```

The direct import plan matches `ShadowBench/Source/Main.lean`. `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`, and `ShadowBench.lean` imports `ShadowBench.Source`, so the generated target module is reachable from the root project module.

## Suggested Search Modules

These are non-gating search hints for the prover; do not add them as direct imports unless Lean verification later proves a narrower import is needed.

- `Mathlib.Algebra.GCDMonoid.Finset`: finite-set LCM operation `Finset.lcm`.
- `Mathlib.Data.Finset.Interval`: interval finsets such as `Finset.Icc` and inclusion facts.
- `Init.Data.Nat.Lcm`: basic `Nat.lcm` positivity, divisibility, and nonzero facts.
- Nat-choose/binomial modules reachable from `Mathlib`: `Nat.choose` identities and inequalities for the divisibility and lower-bound lemmas.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single source-fidelity draft file. It imports `Mathlib`, defines `LCM`, and declares the four source lemmas with `by sorry` proof placeholders for the later prover queue.
- `ShadowBench/Source.lean`: aggregator already imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: project root module already imports `ShadowBench.Source`.

No file split is needed for the initial draft because the source is short and all declarations share the same LCM definition.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`.
- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` are identical and propose the required names with `LCM (m) := (Finset.Icc 1 m).lcm id`.
- `docs/skeletons/Skeleton4.lean` has the same proposed declarations but includes a malformed extra `:= by sorry` at the end, so it is not copied directly.
- Adopted from the skeletons: required declaration names, `LCM` as a finite-interval LCM, binder domains over `ℕ`, side conditions, `Nat.choose`, and natural-number divisibility.

## Required Names

- `LCM`
- `LCM_gt_0`
- `LCM_monotone`
- `LCM_dvd_by`
- `LCM_range_lower_bdd`

## Detected Theorem-Like Blocks

1. `line-17` (definition, lines 17-19) - LCM
2. `line-21` (lemma, lines 21-23; proof lines 23-26) - LCM_gt_0
3. `line-28` (lemma, lines 28-30; proof lines 30-33) - LCM_monotone
4. `line-35` (lemma, lines 35-37; proof lines 37-46) - LCM_dvd_by
5. `line-48` (lemma, lines 48-50; proof lines 50-59) - LCM_range_lower_bdd

## Source Map

- line-17 -> `LCM` (`docs/source.tex` lines 17-19)
- line-21 -> `LCM_gt_0` (`docs/source.tex` lines 21-23; proof lines 23-26)
- line-28 -> `LCM_monotone` (`docs/source.tex` lines 28-30; proof lines 30-33)
- line-35 -> `LCM_dvd_by` (`docs/source.tex` lines 35-37; proof lines 37-46)
- line-48 -> `LCM_range_lower_bdd` (`docs/source.tex` lines 48-50; proof lines 50-59)

## Source inventory

- label: line-17
  source_id: line-17
  kind: definition
  source_title: LCM
  planned_lean_declaration: LCM
  source_locator: docs/source.tex lines 17-19
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.
- label: line-21
  source_id: line-21
  kind: lemma
  source_title: LCM_gt_0
  planned_lean_declaration: LCM_gt_0
  source_locator: docs/source.tex lines 21-23, proof lines 23-26
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.
- label: line-28
  source_id: line-28
  kind: lemma
  source_title: LCM_monotone
  planned_lean_declaration: LCM_monotone
  source_locator: docs/source.tex lines 28-30, proof lines 30-33
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.
- label: line-35
  source_id: line-35
  kind: lemma
  source_title: LCM_dvd_by
  planned_lean_declaration: LCM_dvd_by
  source_locator: docs/source.tex lines 35-37, proof lines 37-46
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.
- label: line-48
  source_id: line-48
  kind: lemma
  source_title: LCM_range_lower_bdd
  planned_lean_declaration: LCM_range_lower_bdd
  source_locator: docs/source.tex lines 48-50, proof lines 50-59
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source title: definition `LCM`.
- Planned Lean declarations: `LCM`
- Adopted statement shape:

```lean
def LCM (m : ℕ) : ℕ :=
  (Finset.Icc 1 m).lcm id
```

- Source inventory entry: `line-17`.
- Source locator: `docs/source.tex`, definition environment lines 17-19.
- Source statement: “Define `LCM(m)` as the least common multiple of all positive integers up to a given natural number `m`.”
- Skeleton candidate used: `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` supplied exactly this finite-interval LCM shape. `Skeleton4.lean` was rejected as syntactically malformed after the same declarations.
- Dependencies:
  - `Finset.Icc 1 m` for the finite interval of natural numbers from `1` through `m`.
  - `Finset.lcm` for the least common multiple of values of `id` over that interval.
- Formal statement review:
  - The source specifies a total natural-number function; the Lean declaration has domain `ℕ` and codomain `ℕ`.
  - The source set is the positive integers up to `m`; the Lean set is `Finset.Icc 1 m`, whose elements are natural numbers satisfying `1 ≤ i ∧ i ≤ m`.
  - The finite LCM operation starts from `1`, so `LCM 0 = 1`, matching the source proof of monotonicity, which explicitly mentions `LCM(0) = 1`.
- Source qualifiers:
  - Mathematical object class: natural-number least common multiple over a finite initial positive interval.
  - Quantifier/order: one parameter `m`.
  - Parameter domain: `m : ℕ`.
  - Output codomain: `ℕ`.
  - Equality/image condition: the indexing interval is exactly the naturals `i` with `1 ≤ i ≤ m`.
  - Side conditions: none.
  - Follow-on claims: positivity and monotonicity are separate source lemmas, not part of the definition.
- Lean coverage:
  - Object class covered by `Finset.Icc 1 m` and `Finset.lcm id` over naturals.
  - The `m = 0` convention is covered by the empty finite-set LCM value `1`.
- Scope changes: none.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: definition entry only. Provers should unfold `LCM` to the finite-set LCM over `Finset.Icc 1 m`.

### line-21

- Source inventory entry: `line-21`
- Source title: lemma `LCM_gt_0`.
- Planned Lean declarations: `LCM_gt_0`
- Adopted statement shape:

```lean
lemma LCM_gt_0 (m : ℕ) : 0 < LCM m := by
  sorry
```

- Source inventory entry: `line-21`.
- Source locator: `docs/source.tex`, lemma environment lines 21-23; proof lines 23-26.
- Source statement: “For any natural number `m`, the least common multiple `LCM(m)` is greater than zero.”
- Skeleton candidate used: all four skeletons propose the required name and the equivalent proposition `∀ m : ℕ, LCM m > 0`; the final statement uses an explicit binder and writes the inequality as `0 < LCM m`.
- Dependencies:
  - `LCM`.
  - Positivity of finite LCMs over nonzero positive natural entries; empty interval case evaluates to `1`.
- Formal statement review:
  - The source quantifies over every natural number `m`; the Lean lemma has one arbitrary binder `m : ℕ`.
  - The source conclusion `LCM(m) > 0` is exactly Lean's `0 < LCM m`.
  - No source side conditions are added or removed.
- Source qualifiers:
  - Mathematical object class: natural number `m` and natural-valued finite LCM.
  - Quantifier order: `m` only.
  - Parameter domain: `m : ℕ`.
  - Output codomain/proposition: strict positivity proposition in `ℕ`.
  - Side conditions: none.
  - Follow-on claims: none beyond positivity.
- Lean coverage: full source coverage.
- Scope changes: none.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```tex
We unfold the definition of \( \text{LCM} \) and use logical simplifications to reduce the statement to basic properties of natural numbers. The key steps involve showing that the least common multiple cannot be zero, as it is defined over positive integers and their multiples. The simplification tactic resolves the inequality \( \text{LCM}(m) > 0 \) by verifying that zero cannot be the least common multiple of any natural number \( m \).
```

- Source proof / prover notes:
  - Unfold `LCM` to `(Finset.Icc 1 m).lcm id`.
  - Use the empty-interval value `1` for `m = 0`; otherwise all entries in `Finset.Icc 1 m` are positive and finite LCM positivity follows from `Nat.lcm_pos`/`Finset.lcm` induction.

### line-28

- Source inventory entry: `line-28`
- Source title: lemma `LCM_monotone`.
- Planned Lean declarations: `LCM_monotone`
- Adopted statement shape:

```lean
lemma LCM_monotone (m n : ℕ) (h : m ≤ n) : LCM m ≤ LCM n := by
  sorry
```

- Source inventory entry: `line-28`.
- Source locator: `docs/source.tex`, lemma environment lines 28-30; proof lines 30-33.
- Source statement: “For all natural numbers `m ≤ n`, `LCM(m) ≤ LCM(n)`.”
- Skeleton candidate used: all four skeletons propose the required name and the equivalent proposition `∀ m n : ℕ, m ≤ n → LCM m ≤ LCM n`; the final statement uses explicit hypotheses.
- Dependencies:
  - `LCM`.
  - Inclusion `Finset.Icc 1 m ⊆ Finset.Icc 1 n` under `m ≤ n`.
  - Divisibility/order facts for natural-number finite LCMs.
- Formal statement review:
  - The source has two natural variables and side condition `m ≤ n`; Lean has binders `m n : ℕ` and hypothesis `h : m ≤ n`.
  - The source conclusion `LCM(m) ≤ LCM(n)` is exactly the Lean conclusion.
- Source qualifiers:
  - Mathematical object class: natural numbers and their finite-interval LCMs.
  - Quantifier order: `m`, then `n`, then the side condition.
  - Parameter domain: `m n : ℕ`.
  - Output codomain/proposition: inequality in `ℕ`.
  - Side conditions: `m ≤ n`.
  - Follow-on proof claims: successor divisibility and base case `LCM(0) = LCM(1) = 1` are proof ingredients.
- Lean coverage: full source coverage.
- Scope changes: none.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```tex
We verify monotonicity by showing \( \mathrm{LCM}(n) \mid \mathrm{LCM}(n+1) \). For \( n > 0 \), the interval \( [1, n] \) is contained in \( [1, n+1] \), so the least common multiple over the larger set is divisible by the smaller one. For \( n = 0 \), we directly confirm \( \mathrm{LCM}(0) = 1 \le \mathrm{LCM}(1) = 1 \).
```

- Source proof / prover notes:
  - Either prove finite-set LCM monotonicity by interval inclusion and divisibility, then convert divisibility to `≤` using positivity, or prove the source's successor step and iterate along `m ≤ n`.
  - The `m = 0`/empty interval convention should simplify to `1`.

### line-35

- Source inventory entry: `line-35`
- Source title: lemma `LCM_dvd_by`.
- Planned Lean declarations: `LCM_dvd_by`
- Adopted statement shape:

```lean
lemma LCM_dvd_by (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    m * Nat.choose n m ∣ LCM n := by
  sorry
```

- Source inventory entry: `line-35`.
- Source locator: `docs/source.tex`, lemma environment lines 35-37; proof lines 37-46.
- Source statement: “For natural numbers `m` and `n` with `1 ≤ m ≤ n`, the product `m * binom(n,m)` divides the least common multiple `LCM(1,2,...,n)`. That is, `m * binom(n,m) ∣ LCM(n)`.”
- Skeleton candidate used: all four skeletons propose the same natural-number divisibility statement with side conditions `1 ≤ m` and `m ≤ n`; the final declaration keeps that shape.
- Dependencies:
  - `LCM`.
  - `Nat.choose` for binomial coefficients over natural numbers.
  - Natural-number divisibility `∣`.
  - Denominator-clearing facts that each `i ∈ Finset.Icc 1 n` divides `LCM n`.
- Formal statement review:
  - The source parameters `m` and `n` are natural numbers; Lean has binders `m n : ℕ` in the same order.
  - The source side condition `1 ≤ m ≤ n` is represented by two hypotheses `hm : 1 ≤ m` and `hmn : m ≤ n`.
  - The source product `m · binom(n,m)` is represented by `m * Nat.choose n m`.
  - The source divisibility target `LCM(1,2,...,n)` is represented by the previously defined one-argument `LCM n`.
- Source qualifiers:
  - Mathematical object class: natural numbers, binomial coefficients, and natural-number divisibility.
  - Quantifier order: `m`, then `n`, then side conditions.
  - Parameter domain: `m n : ℕ`.
  - Output codomain/proposition: divisibility proposition in `ℕ`.
  - Side conditions: `1 ≤ m` and `m ≤ n`.
  - Equality/image condition: `LCM n` is the LCM of exactly the positive integers `1..n`.
  - Follow-on proof claims: beta-integral identity, polynomial expansion with integer coefficients, and denominator clearing are proof ingredients, not extra theorem conclusions.
- Lean coverage: full source coverage.
- Scope changes: none.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```tex
We begin by defining a function \( \beta'(m, n) \) as the integral \( \int_0^1 x^{m-1}(1-x)^{n-m} \, dx \), which is known to equal \( \frac{1}{m \cdot \binom{n}{m}} \). This is established using properties of the Gamma function and factorial identities.

Next, we expand \( \beta'(m, n) \) into a sum involving rational coefficients divided by integers from 1 to \( n \). This expansion is achieved by expressing the integrand as a polynomial, applying the binomial theorem, and integrating term-by-term. The result is a sum of the form \( \sum_{i=1}^n \frac{a_i}{i} \), where \( a_i \) are integers derived from binomial coefficients and powers of \( -1 \).

By equating the two expressions for \( \beta'(m, n) \), we find that \( \frac{1}{m \cdot \binom{n}{m}} = \sum_{i=1}^n \frac{a_i}{i} \). Multiplying both sides by \( m \cdot \binom{n}{m} \cdot \mathrm{LCM}(n) \), we obtain an integer linear combination of terms \( \mathrm{LCM}(n) \cdot \frac{a_i}{i} \), which are integers due to the divisibility of \( \mathrm{LCM}(n) \) by all \( i \in \{1, \dots, n\} \).

This implies that \( m \cdot \binom{n}{m} \) divides \( \mathrm{LCM}(n) \), completing the proof.
```

- Source proof / prover notes:
  - The source proof is analytic. The Lean proof may be easier using existing arithmetic/binomial LCM divisibility lemmas if found.
  - If reproducing the source proof, isolate helper lemmas for the beta-integral evaluation, polynomial expansion with integer coefficients, and rational denominator clearing by `LCM n`.
  - For the denominator-clearing step, prove `i ∣ LCM n` whenever `1 ≤ i ∧ i ≤ n` by unfolding `LCM` and using `Finset.lcm` divisibility.

### line-48

- Source inventory entry: `line-48`
- Source title: lemma `LCM_range_lower_bdd`.
- Planned Lean declarations: `LCM_range_lower_bdd`
- Adopted statement shape:

```lean
lemma LCM_range_lower_bdd (m : ℕ) (hm : 7 ≤ m) : 2 ^ m ≤ LCM m := by
  sorry
```

- Source inventory entry: `line-48`.
- Source locator: `docs/source.tex`, lemma environment lines 48-50; proof lines 50-59.
- Source statement: “For all natural numbers `m ≥ 7`, the least common multiple of the numbers from `1` to `m` satisfies `LCM(m) ≥ 2^m`.”
- Skeleton candidate used: all four skeletons propose the same quantification and conclusion; the final declaration writes the inequality as `2 ^ m ≤ LCM m`.
- Dependencies:
  - `LCM`.
  - `LCM_gt_0`, `LCM_monotone`, and `LCM_dvd_by` as source-proof dependencies.
  - Binomial coefficient lower bounds and divisibility/coprimality facts.
- Formal statement review:
  - The source universally quantifies over one natural number `m`; Lean has binder `m : ℕ`.
  - The source side condition `m ≥ 7` is represented as `hm : 7 ≤ m`.
  - The source conclusion `LCM(m) ≥ 2^m` is represented by the equivalent Lean order `2 ^ m ≤ LCM m`.
- Source qualifiers:
  - Mathematical object class: natural numbers and finite-interval LCMs.
  - Quantifier order: `m`, then side condition.
  - Parameter domain: `m : ℕ`.
  - Output codomain/proposition: inequality in `ℕ`.
  - Side conditions: `7 ≤ m`.
  - Equality/image condition: `LCM m` is the LCM of exactly the positive integers `1..m`.
  - Follow-on proof claims: base cases `m = 7, 8`, odd/even split, binomial-product divisibility, and monotonic reduction are proof ingredients.
- Lean coverage: full source coverage.
- Scope changes: none.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```tex
We proceed by case analysis on \( m \). For \( m < 9 \), we directly verify the inequality for \( m = 7 \) and \( m = 8 \) using computational checks. For \( m \geq 9 \), we consider two subcases based on the parity of \( m \).

For the odd case \( m = 2k + 1 \), we establish the inequality \( 2^{2k+2} \leq \mathrm{LCM}(2k+1) \) using properties of binomial coefficients and the fact that certain products divide \( \mathrm{LCM}(2k+1) \). Specifically, we show that \( k \cdot (k+1) \cdot \binom{2k+1}{k} \) divides \( \mathrm{LCM}(2k+1) \), and use this to derive the required bound.

For the even case \( m = 2k \), we reduce it to the odd case by showing that \( \mathrm{LCM}(2k) \geq \mathrm{LCM}(2l+1) \) for an appropriate \( l \), and then apply the previously established bound for the odd case.

The key steps involve bounding the sum of binomial coefficients, using monotonicity of the LCM function, and applying properties of divisibility and coprimality to combine bounds from multiple divisors.
```

- Source proof / prover notes:
  - Keep the base cases `m = 7` and `m = 8` computational.
  - For larger odd `m = 2*k + 1`, combine `LCM_dvd_by` instances, binomial coefficient bounds, and coprimality/divisibility facts to force a sufficiently large divisor of `LCM (2*k+1)`.
  - For even `m`, reduce to a nearby odd input via `LCM_monotone`.

## Construction Gaps

- No definitions, structures, classes, or instances are left as construction stubs.
- `LCM` is implemented concretely as `(Finset.Icc 1 m).lcm id`.
- The only planned proof obligations are the four source lemmas `LCM_gt_0`, `LCM_monotone`, `LCM_dvd_by`, and `LCM_range_lower_bdd`, intentionally left as `by sorry` for the later proof workflow after statement/source review.

## Handoff Checklist

- [x] Source document and preflight manifest read.
- [x] Companion instructions and all candidate skeletons read.
- [x] Local project/Mathlib search performed before choosing identifiers.
- [x] Source theorem inventory includes `line-17`.
- [x] Source theorem inventory includes `line-21`.
- [x] Source theorem inventory includes `line-28`.
- [x] Source theorem inventory includes `line-35`.
- [x] Source theorem inventory includes `line-48`.
- [x] Lean statements contain source proof/prover notes in declaration doc comments.
- [x] Root project module imports the generated target path.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
