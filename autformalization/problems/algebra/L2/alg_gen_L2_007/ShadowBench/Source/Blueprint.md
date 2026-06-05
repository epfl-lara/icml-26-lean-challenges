# Formalization Blueprint: `algebra/L2/alg_gen_L2_007`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Inventory Entries

- Source inventory entry `line-17`: theorem, source `docs/source.tex:17-22`, Lean declaration `isGCD_iff_span_is_least_principal_above_span_pair`.

No labels, references, citations, bibliography files, figures, PDFs, or auxiliary source files were found in the preflight manifest.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`: adopted as the main statement shape after adding explicit `Set` type annotations to ideal spans.
- `docs/skeletons/Skeleton2.lean`: same usable statement shape as Skeleton1.
- `docs/skeletons/Skeleton3.lean`: same usable statement shape as Skeleton1.
- `docs/skeletons/Skeleton4.lean`: not adopted because it contains a duplicated proof terminator (`:= by sorry`).

The adopted shape matches the source theorem: the polynomial ring is represented by `MvPolynomial (Fin n) k`; the source-defined gcd predicate is expanded as divisibility by `h` together with the universal common-divisor condition; and principal ideals are represented by singleton spans.

## Import Plan

```lean
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
```

These are the direct imports in `ShadowBench/Source/Main.lean` and match the allowed import block from `docs/instructions.md`.

## Suggested Search Modules

These are proof-search hints only, not required direct imports for the current draft.

- `Mathlib.RingTheory.Ideal.Span`: searched result `Ideal.span_singleton_le_span_singleton`; also likely useful for `Ideal.span_le` and pair/singleton span reasoning.
- `Mathlib.RingTheory.Ideal.Operations`: ideal order and span operations already available through the direct import block.
- `Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid`: relevant if the prover later relates the expanded predicate to Mathlib gcd APIs.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed theorem declaration with a `by sorry` proof placeholder for the prover workflow.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

No file split is planned for this single-statement source document.

## Required Names

- `isGCD_iff_span_is_least_principal_above_span_pair`

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source label: `line-17`
- Source block id: `line-17`
- Source locator: `docs/source.tex:17-22` (`line-17`).
- Planned Lean declarations: `isGCD_iff_span_is_least_principal_above_span_pair`
- Lean statement: `theorem isGCD_iff_span_is_least_principal_above_span_pair (k : Type*) [Field k] (n : ℕ) (f g h : MvPolynomial (Fin n) k) : (h ∣ f ∧ h ∣ g ∧ ∀ d : MvPolynomial (Fin n) k, d ∣ f → d ∣ g → d ∣ h) ↔ ((Ideal.span ({f, g} : Set (MvPolynomial (Fin n) k)) ≤ Ideal.span ({h} : Set (MvPolynomial (Fin n) k))) ∧ ∀ h' : MvPolynomial (Fin n) k, Ideal.span ({f, g} : Set (MvPolynomial (Fin n) k)) ≤ Ideal.span ({h'} : Set (MvPolynomial (Fin n) k)) → Ideal.span ({h} : Set (MvPolynomial (Fin n) k)) ≤ Ideal.span ({h'} : Set (MvPolynomial (Fin n) k))) := by sorry`
- Source statement:
  > Given polynomials $f,g,h$ in $k[x_1,\dots,x_n]$, where $h=\gcd(f,g)$ means that $h$ divides both $f$ and $g$ and is divisible by every common divisor of $f$ and $g$, prove that $h=\gcd(f,g)$ if and only if $\langle h\rangle$ is the smallest principal ideal containing $\langle f,g\rangle$.
- Complete source proof text: none provided in `docs/source.tex`.
- Skeleton candidate used: Skeleton1/Skeleton2/Skeleton3 statement shape; Skeleton4 rejected as malformed. The final Lean statement keeps the expected declaration name and adds explicit `Set` annotations for robust elaboration.
- Dependencies:
  - Polynomial ring over a field: `(k : Type*) [Field k] (n : ℕ)` and `MvPolynomial (Fin n) k` for `k[x_1,\dots,x_n]`.
  - Divisibility relation `∣` on `MvPolynomial (Fin n) k`.
  - Ideal generation by finite sets: `Ideal.span ({f, g} : Set (MvPolynomial (Fin n) k))` and `Ideal.span ({h} : Set (MvPolynomial (Fin n) k))`.
  - Ideal inclusion order `≤`, used to formalize “containing” and “smallest”.
- Formal statement review:
  - The left side expands the source phrase “`h = gcd(f,g)` means ...” as `h ∣ f ∧ h ∣ g ∧ ∀ d, d ∣ f → d ∣ g → d ∣ h`.
  - The right side expands “`⟨h⟩` is the smallest principal ideal containing `⟨f,g⟩`” as two clauses: first `⟨f,g⟩ ≤ ⟨h⟩`, and second every principal ideal `⟨h'⟩` containing `⟨f,g⟩` also contains `⟨h⟩`, i.e. `⟨h⟩ ≤ ⟨h'⟩`.
  - The order used is ideal inclusion, so “smallest” means least by `≤` among principal ideals above `⟨f,g⟩`.
- Source qualifiers:
  - Mathematical object class: polynomials in `k[x_1,\dots,x_n]`.
  - Quantifier order and domains: `k` is a field, `n : ℕ`, and `f g h` are polynomials over `k` in `n` variables.
  - GCD definition: `h` divides both `f` and `g`, and every common divisor of `f` and `g` divides `h`.
  - Ideal side: principal ideal generated by `h`; ideal generated by the pair `f,g`; least principal ideal containing the pair-generated ideal.
  - Equality/equivalence condition: an iff between the expanded gcd predicate and the least-principal-ideal predicate.
  - Follow-on claims: none beyond the iff.
- Lean coverage:
  - Object class covered by `MvPolynomial (Fin n) k`; `Fin n` indexes the `n` variables corresponding to the source notation `x_1,\dots,x_n`.
  - GCD definition covered by the explicit divisibility conjunction and universal common-divisor clause in the theorem statement.
  - Principal ideal `⟨a⟩` covered by `Ideal.span ({a} : Set (MvPolynomial (Fin n) k))`.
  - Pair-generated ideal `⟨f,g⟩` covered by `Ideal.span ({f, g} : Set (MvPolynomial (Fin n) k))`.
  - Smallest/least principal ideal covered by the conjunction of containment and universal minimality over all polynomial generators `h'`.
- Scope changes:
  - No mathematical weakening or strengthening is intended.
  - Representation choices are explicit Lean encodings: source variables `x_1,\dots,x_n` are indexed by `Fin n`, and angle-bracket ideal notation is expanded to `Ideal.span` over `Set`s.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes:
  - The source document supplies no proof. The intended proof is the standard order-reversing relation between divisibility and principal ideal containment.
  - Key Mathlib search result: `Ideal.span_singleton_le_span_singleton` states that `Ideal.span {x} ≤ Ideal.span {y}` iff `y ∣ x`.
  - Direction `gcd → smallest principal ideal`: use `h ∣ f` and `h ∣ g` to show `⟨f,g⟩ ≤ ⟨h⟩`; for any `h'` with `⟨f,g⟩ ≤ ⟨h'⟩`, convert generator membership to `h' ∣ f` and `h' ∣ g`, apply the common-divisor clause to get `h' ∣ h`, then convert back to `⟨h⟩ ≤ ⟨h'⟩`.
  - Direction `smallest principal ideal → gcd`: from `⟨f,g⟩ ≤ ⟨h⟩`, get `h ∣ f` and `h ∣ g`; for any common divisor `d`, show `⟨f,g⟩ ≤ ⟨d⟩`, apply minimality to obtain `⟨h⟩ ≤ ⟨d⟩`, then convert to `d ∣ h`.
  - Useful tactics/lemmas for the prover: unfold the pair/singleton spans with `Ideal.span_le`, use membership of set insertions/singletons for the generators, and use `Ideal.span_singleton_le_span_singleton` for the final divisibility/inclusion conversions.

## Formalization Checklist

- [x] Source document and preflight manifest read.
- [x] Candidate skeletons and instructions read.
- [x] Local/Mathlib search performed before drafting.
- [x] Blueprint source inventory entry `line-17` populated.
- [x] Lean theorem declaration drafted with a proof placeholder for the prover queue.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
- [ ] Prover queue completed the theorem without `sorry`.
