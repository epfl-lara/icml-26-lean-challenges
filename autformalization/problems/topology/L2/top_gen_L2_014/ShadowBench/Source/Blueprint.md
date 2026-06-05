# Formalization Blueprint: `topology/L2/top_gen_L2_014`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the three required source-backed declarations.
- `ShadowBench/Source.lean`: source-module aggregator; imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: root project module; imports `ShadowBench.Source` so plain project builds include the generated target.

No file split is currently needed: the source document has only two named definitions and one theorem, all relying on the same Mathlib singular homology module.

## Import Plan

Direct imports used by `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.AlgebraicTopology.SingularHomology.Basic
```

This single direct import provides the singular chain complex functor, singular homology functor, totally disconnected-space calculation, category-theoretic coproduct notation, and the needed topology/category instances. Earlier scaffold imports with unqualified module prefixes (`CategoryTheory.*`, `Topology.*`) were replaced because this project uses Mathlib-prefixed module names.

## Suggested Search Modules

These are search/prover hints only, not direct imports in the generated Lean file unless a later proof run needs them explicitly:

- `Mathlib.Algebra.Homology.AlternatingConst`
- `Mathlib.AlgebraicTopology.SingularSet`
- `Mathlib.Topology.Connected.TotallyDisconnected`
- `Mathlib.Topology.Separation.Connected`
- `Mathlib.Algebra.Homology.ShortComplex.Homology`

## Required Names

- `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace`
- `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`
- `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`

## Candidate Skeletons Reviewed

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` proposed the required names, but used non-existing or underspecified symbols such as `HasHomology` and `singularHomology`, and used `TopCat → ChainComplex C` instead of the Mathlib functor category `TopCat ⥤ ChainComplex C ℕ`.
- `docs/skeletons/Skeleton4.lean` was closest for the singular chain complex codomain and for the theorem's use of `TotallyDisconnectedSpace X`, but it made the two source definitions into unimplemented `sorry` constructions and stated the theorem as a literal object equality with an `if`, which is not the standard Lean categorical formulation.
- Final draft uses Mathlib's existing singular homology API from `Mathlib.AlgebraicTopology.SingularHomology.Basic`, with the required source names as source-backed aliases/theorem skeletons.

## Source Statement Inventory

- Source inventory entry: line-17 — `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace`.
- Source inventory entry: line-28 — `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`.
- Source inventory entry: line-36 — `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`.

### line-17

Source inventory entry: line-17.
Definition `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace`.

- Source kind: definition.
- Source locator: `docs/source.tex`, lines 17-26.
- Source title: `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace`.
- Planned Lean declarations: `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace`.
- Lean declaration kind: `noncomputable def`.
- Skeleton candidate used: shaped by `docs/skeletons/Skeleton4.lean` for the codomain `C ⥤ TopCat ⥤ ChainComplex C ℕ`, corrected to the Mathlib implementation.
- Dependencies:
  - `AlgebraicTopology.singularChainComplexFunctor`
  - `CategoryTheory.Category`, `CategoryTheory.Preadditive`, `CategoryTheory.CategoryWithHomology`
  - `CategoryTheory.Limits.HasCoproducts`
  - `TopCat`, `ChainComplex`
- Source statement summary: for a preadditive category `C` with coproducts and homology, the singular chain complex functor sends an object of coefficients `R : C` and a topological space `X` to the chain complex whose degree-`n` object is the coproduct over singular `n`-simplices, with alternating face-map differential.
- Source qualifiers:
  - Mathematical object class: a preadditive category `C` equipped with coproducts and homology; coefficient objects `R : C`; topological spaces `X`.
  - Quantifier order: choose the category `C` with its categorical/preadditive/coproduct/homology structures; the functor then takes coefficients `R` and topological spaces `X`.
  - Parameter domain: source category `C`, object `R ∈ C`, topological space `X`, degree `n ∈ ℕ`, and singular `n`-simplices as continuous maps `Δ_n → X`.
  - Output codomain: source functor `C → Fun(Top, Ch_{≥0}(C))`; at `R` and `X` it outputs a nonnegative chain complex in `C`.
  - Equality/image condition: the degree-`n` term is `C_n(X; R) = ∐_{Sing(X)_n} R`, and the differential is the alternating sum `d_n = ∑_{i=0}^n (-1)^i d_i^n` of face restrictions.
  - Side conditions: no total-disconnectedness hypothesis is part of this definition.
  - Follow-on claims in the source statement: none beyond this construction; later entries use the functor for homology and the totally disconnected computation.
- Lean coverage: the Lean definition
  `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace C : C ⥤ TopCat.{w} ⥤ ChainComplex C ℕ`
  aliases `AlgebraicTopology.singularChainComplexFunctor C`. This covers the source construction through Mathlib's singular homology API, including singular sets, coproducts over simplices, and alternating face-map differentials.
- Scope changes: source notation `Top`, `Fun(Top, -)`, and `Ch_{≥0}(C)` is represented by Lean's bundled `TopCat`, functor category notation `⥤`, and `ChainComplex C ℕ`; the prose construction is represented by the existing Mathlib definition rather than reimplemented locally.
- Formal statement review: independently checked; the Lean declaration preserves the source category assumptions and functor codomain up to the recorded Lean representations.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: definition only; no proof text in the source. For unfolding/proof use, reduce this alias to `AlgebraicTopology.singularChainComplexFunctor`.

### line-28

Source inventory entry: line-28.
Definition `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`.

- Source kind: definition.
- Source locator: `docs/source.tex`, lines 28-34.
- Source title: `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`.
- Planned Lean declarations: `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`.
- Lean declaration kind: `noncomputable def`.
- Skeleton candidate used: candidate skeletons provided only a rough name/codomain hint; final statement corrected to Mathlib's fixed-degree singular homology functor.
- Dependencies:
  - `AlgebraicTopology.singularHomologyFunctor`
  - `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace` conceptually, through the Mathlib construction
  - `HomologicalComplex.homologyFunctor`
- Source statement summary: for a preadditive category `C` with coproducts and homology, the singular homology functor sends coefficients `R` and a topological space `X` to the homology of the singular chain complex `C_•(X; R)`.
- Source qualifiers:
  - Mathematical object class: a preadditive category `C` equipped with coproducts and homology; coefficient objects `R : C`; topological spaces `X`; homological degrees `n ∈ ℕ`.
  - Quantifier order: choose `C` with its structures; the source graded functor takes coefficients `R` and spaces `X`, with components indexed by `n`.
  - Parameter domain: source category `C`, object `R ∈ C`, topological space `X`, and degree `n ∈ ℕ` for the component `H_n(X; R)`.
  - Output codomain: source writes a graded singular homology functor `H_•(-;-) : C → Fun(Top, Ch_{≥0}(C))`/component family; the explicit component `H_n(X; R)` is an object of `C`.
  - Equality/image condition: `H_n(X; R)` is the `n`-th homology object of the singular chain complex `C_•(X; R)`.
  - Side conditions: no total-disconnectedness hypothesis is part of this definition.
  - Follow-on claims in the source statement: this definition supplies the `H_n` objects computed in line-36; no separate theorem is stated here.
- Lean coverage: the Lean definition aliases the degree-indexed Mathlib family
  `fun n => AlgebraicTopology.singularHomologyFunctor C n : ℕ → C ⥤ TopCat.{w} ⥤ C`; for each degree `n`, this covers the explicitly stated component `H_n(X; R)` as the homology object of `C_•(X; R)` through Mathlib's singular homology construction.
- Scope changes: the source's richer graded notation `H_•` and codomain `Fun(Top, Ch_{≥0}(C))` are represented as a degree-indexed family of fixed-degree functors to `C`, rather than as a separately bundled chain-complex-valued or graded-object-valued functor. This is an intentional representation change because Mathlib's API and the source theorem use fixed-degree components. The declaration name is inherited from the source even though Mathlib uses this name for the nonzero-degree vanishing lemma inside the `AlgebraicTopology` namespace.
- Formal statement review: independently checked; the Lean declaration preserves the source's fixed-degree `H_n` content, with the omitted bundled `H_•` packaging recorded as partial coverage and a scope change.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: definition only; no proof text in the source. For unfolding/proof use, reduce this alias to `AlgebraicTopology.singularHomologyFunctor C n`.

### line-36

Source inventory entry: line-36.
Theorem `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`.

- Source kind: theorem.
- Source locator: `docs/source.tex`, statement lines 36-44; proof lines 44-64.
- Source title: `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`.
- Planned Lean declarations: `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`.
- Lean declaration kind: `theorem` with `by sorry` proof placeholder for the prover queue.
- Skeleton candidate used: `docs/skeletons/Skeleton4.lean` was the closest shape for parameter order and the zero-degree coproduct target; final statement replaces literal object equality/`if` with a `Nonempty` categorical isomorphism assertion and `IsZero` clauses.
- Dependencies:
  - `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`
  - `AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace`
  - `AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`
  - `TotallyDisconnectedSpace`, `IsZero`, coproduct notation `∐`
- Source statement summary: if `X` is totally disconnected, then the singular homology of `X` with coefficients in `R` is the coproduct `∐_{x ∈ X} R` in degree `0` and is zero in all positive degrees.
- Source qualifiers:
  - Mathematical object class: a totally disconnected topological space `X`; a preadditive category `C` equipped with coproducts and homology; an object of coefficients `R : C`.
  - Quantifier order: source lists `X`, the total-disconnectedness condition, `C` with structures, `R`, and an implicit homological degree `n` in the notation `H_n`.
  - Parameter domain: source topological space `X`, object `R ∈ C`, and degree `n ∈ ℕ`.
  - Output codomain: the singular homology object `H_n(X; R)` in `C`.
  - Equality/image condition: when `n = 0`, `H_n(X; R)` is the coproduct `∐_{x ∈ X} R`; when `n > 0`, `H_n(X; R)` is zero.
  - Side conditions: total disconnectedness of `X` and positive degree for the vanishing branch; no discreteness, Hausdorffness, or singleton-open assumption is part of the theorem statement.
  - Follow-on claims in the source statement: none beyond the displayed two-case homology computation. The singular-simplex identification and alternating differential are source proof content and are recorded below as proof notes, not as extra theorem conclusions.
- Lean coverage: the Lean theorem covers the two source cases using the fixed-degree homology alias from line-28. It quantifies `X : TopCat.{w}` with `[TotallyDisconnectedSpace X]`, `C` with `[Category] [Preadditive] [HasCoproducts] [CategoryWithHomology]`, `R : C`, and `n : ℕ`; it states a degree-zero isomorphism to `∐ fun _ : X ↦ R` and positive-degree `IsZero`.
- Scope changes: the source topological space is represented by a bundled `TopCat` object; source object equality in an abstract category is represented by `Nonempty` of an isomorphism in degree zero and by the categorical predicate `IsZero` in positive degree; the displayed piecewise equality is represented by a conjunction of implications for a fixed `n`. These are intentional categorical representation changes, not proof weakenings for the source computation.
- Formal statement review: independently checked; the Lean statement preserves the source assumptions and degree case split with the categorical representations recorded above. The incorrect proof sentence "any singleton is open" is not included as a Lean assumption.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: "Since $X$ is totally disconnected, any singleton of $X$ is open. So any continuous map from a connected space is constant. Hence, any singular $n$-simplex of $X$ is a constant map, and we have identification $\text{Sing}(X)_n \simeq X$, $\sigma \mapsto \text{Im}(\sigma)$. Moreover, face maps $d_i^n$ are just restrictions of singular simplices, so they are all the identity map $X \to X$ under the identifications $\text{Sing}(X)_n \simeq X \simeq \text{Sing}(X)_{n-1}$. Thus, we have
  \begin{align*}
      d_n = \sum_{i=0}^n (-1)^nd_i^n = \begin{cases}
          0, &\text{if } n= \text{ even} \\
          \text{id}, &\text{if } n= \text{ odd}
      \end{cases}
  \end{align*}
  and the singular chain complex $C_\bullet(X;R)$ is of the form
  \begin{align*}
      \coprod_{x \in X} R \xleftarrow{0} \coprod_{x \in X} R \xleftarrow{\text{id}} \coprod_{x \in X} R \xleftarrow{0} \cdots
  \end{align*}
  THerefore, we have
  \begin{align*}
      H_n(X;R) = \begin{cases}
          \coprod_{x \in X} R, &\text{ if }n = 0\\
          0, &\text{ if } n > 0
      \end{cases}
  \end{align*}"
- Prover notes: do not reprove the simplicial-set calculation from scratch unless necessary. The source proof text has two proof-level slips: a totally disconnected space need not have open singletons, and the displayed differential uses `(-1)^n` where the definition used the alternating sign `(-1)^i`. The intended argument is that the image of a connected simplex is connected and hence a singleton, making all face maps identities and yielding the alternating zero/identity complex. Mathlib already provides `AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace C R X` for the zero-degree isomorphism and `AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R X` for nonzero degrees. For the drafted statement, split the conjunction; in the first branch introduce `h : n = 0`, substitute `n`, and use the zero-degree isomorphism. In the second branch introduce `hpos : 0 < n`, convert it to `n ≠ 0` using `Nat.ne_of_gt hpos`, and apply the Mathlib vanishing lemma.

## Formalization Handoff Notes

- Draft Lean declarations are source-backed and compile except for the intentional theorem proof placeholder.
- Definition/construction stubs were avoided: both source definitions are implemented as aliases to existing Mathlib constructions.
- The theorem proof is intentionally left as `by sorry` for the later `/prove` workflow after independent statement/source review.
- The proof-ready checklist is intentionally not marked complete here; statement/source verification must approve the source entries first.

Suggested next command after review approval:

```text
/prove ShadowBench/Source/Main.lean singularHomologyFunctorZeroOfTotallyDisconnectedSpace
```
