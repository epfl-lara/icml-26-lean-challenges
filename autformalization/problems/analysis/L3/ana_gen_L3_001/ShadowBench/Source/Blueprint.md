# Formalization Blueprint: `analysis/L3/ana_gen_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Documents and Support Files Read

- `docs/source.tex`: inspected directly and through `formalization_document_inspect`; contains one theorem-like block, `line-17`, with theorem statement at lines 17--19 and proof at lines 21--147.
- `.epflemma/workflow-state/formalization/docs-source/manifest.json`: inspected; it lists no bibliography files, citations, refs, or additional local PDFs/figures/support files.
- Project-local PDF search: no `*.pdf` files were present, so `read_pdf` had no project-local PDF text to extract.
- `.epflemma/workflow-state/formalization/docs-source/context.md`: workflow context and handoff contract read.
- `docs/instructions.md`: requires the theorem name `exists_affine_between_of_concaveOn_le_convexOn`, target file `ShadowBench/Source/Main.lean`, and the starting imports.
- `docs/skeletons/README.md` and `docs/skeletons/Skeleton1.lean` through `Skeleton4.lean`: used only as candidate statement shapes and checked against the source theorem.

## Import Plan

```lean
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Real.Hom
```

The instruction file listed `Mathlib.Data.Real.CompleteField`; Lean reports that module as deprecated and recommends `Mathlib.Data.Real.Hom`, so the generated Lean draft uses the direct replacement to avoid the deprecation diagnostic.

## Suggested Search Modules

These are proof-search hints, not direct imports for the current draft.

- `Mathlib.Topology.Algebra.ContinuousAffineMap`: contains bundled continuous affine maps and decomposition lemmas if the prover wants to connect the local affine predicate to Mathlib's bundled affine-map API.
- `Mathlib.Analysis.Convex.Approximation`: contains related convex-function affine minorant results.
- `Mathlib.Analysis.LocallyConvex.Separation`: provides `geometric_hahn_banach_open_open`, matching the source proof's separation step.

## Generated File Layout

- `ShadowBench.lean` imports `ShadowBench.Source`.
- `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- `ShadowBench/Source/Main.lean` contains the bridge definition `IsAffineRealMap` and the single source theorem skeleton, with imports first and a source-aware doc comment immediately above the theorem.

No split into additional files is planned for this one-theorem source.

## Required Names

- `exists_affine_between_of_concaveOn_le_convexOn`

## Generated Bridge Definitions

### `IsAffineRealMap`

- Purpose: records the source phrase “an affine function `h : ℝ^n → ℝ`” in the chosen Lean representation of `ℝ^n` as `Fin n → ℝ`.
- Lean definition:

```lean
def IsAffineRealMap {n : ℕ} (h : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ l : ((Fin n → ℝ) →L[ℝ] ℝ), ∃ b : ℝ, ∀ x, h x = l x + b
```

- Coverage note: this is an explicit representation bridge, not a source theorem. It says that a real-valued function on `ℝ^n` is affine when it is a continuous linear functional plus a constant. The source proof obtains a continuous linear functional from Hahn--Banach, matching this bridge.

## Candidate Skeleton Review

- `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` use coordinate coefficients `a : Fin n → ℝ` and an offset `b`, with `h x = ∑ i, a i * x i + b`. This is a valid coordinate representation of an affine real-valued function on `ℝ^n`, but it commits the statement to a basis/finite sum representation that the source proof does not use explicitly.
- `Skeleton4.lean` uses a bundled continuous linear functional `l : (Fin n → ℝ) →L[ℝ] ℝ` and an offset `b`. This matches the Hahn--Banach separation proof more directly, but it does not quantify over the source's function `h` explicitly.
- The reviewed draft uses a source-literal witness `h : (Fin n → ℝ) → ℝ` plus the bridge predicate `IsAffineRealMap h`. This keeps the source conclusion “there exists an affine function `h`” visible while retaining the linear-functional-plus-constant representation needed by the proof.

## Mathlib/Search Notes

- `ConvexOn` and `ConcaveOn` were found in `Mathlib.Analysis.Convex.Function`, imported by `Mathlib.Analysis.Convex.Continuous`.
- `geometric_hahn_banach_open_open` was found in `Mathlib.Analysis.LocallyConvex.Separation`; it separates disjoint open convex subsets with a continuous linear functional and a scalar.
- `LinearMap`, `ContinuousLinearMap`, and their notations are available through the imported algebra/topology modules.
- Search found bundled `ContinuousAffineMap` declarations, but the reviewed statement keeps a small local predicate to avoid an unnecessary import and to make the representation bridge explicit in the theorem statement.

## Source Statement Inventory

### line-17

- Source inventory label: `line-17`
- Source title: theorem `exists_affine_between_of_concaveOn_le_convexOn`.
- Kind: theorem
- Planned Lean declaration: `exists_affine_between_of_concaveOn_le_convexOn`
- Source locator: `docs/source.tex`, theorem lines 17--19; proof lines 21--147.
- Source statement: Suppose `f : ℝ^n → ℝ` is convex, `g : ℝ^n → ℝ` is concave, both have full domain `ℝ^n`, and `g x ≤ f x` for every `x`. Then there exists an affine function `h` such that `g x ≤ h x ≤ f x` for every `x`. Equivalently, a concave underestimator of a convex function admits an affine function between the two.
- Skeleton candidate used: revised from `docs/skeletons/Skeleton4.lean`; the review changed the output from direct `∃ l b` to `∃ h, IsAffineRealMap h ∧ ...` so the source's affine-function witness is explicit.
- Dependencies: `ConvexOn`, `ConcaveOn`, `Set.univ`, real finite-dimensional space `Fin n → ℝ`, local bridge definition `IsAffineRealMap`, pointwise order on `ℝ`, and the future proof's separation theorem `geometric_hahn_banach_open_open`.
- Lean statement used for coverage:

```lean
theorem exists_affine_between_of_concaveOn_le_convexOn {n : ℕ}
    (f g : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hg : ConcaveOn ℝ Set.univ g)
    (hfg : ∀ x, g x ≤ f x) :
    ∃ h : (Fin n → ℝ) → ℝ, IsAffineRealMap h ∧ ∀ x, g x ≤ h x ∧ h x ≤ f x
```

- Source qualifiers:
  - Mathematical object class: total finite real-valued functions `f, g : ℝ^n → ℝ`; `f` is convex; `g` is concave; `g` is a pointwise underestimator of `f`.
  - Quantifier order: fix the dimension `n`; quantify over `f` and `g`; assume convexity, concavity, full-domain finite-valuedness, and pointwise domination; then produce one affine function `h` valid for every `x`.
  - Parameter domain: all of `ℝ^n`; the source explicitly says `dom f = dom g = ℝ^n`.
  - Output codomain: all functions in the statement are finite-valued real functions with codomain `ℝ`, not extended-real functions.
  - Equality/image condition: the only equality condition in the statement is the full-domain condition `dom f = dom g = ℝ^n`; the conclusion is pointwise inequality, not equality or image equality.
  - Side conditions: convexity of `f`, concavity of `g`, and `∀ x, g(x) ≤ f(x)`.
  - Follow-on claim: the “in other words” sentence is the same assertion that an affine separator can be fit between the concave underestimator and the convex upper estimator.
- Lean coverage:
  - `ℝ^n` is represented by the standard Lean finite-coordinate model `Fin n → ℝ`.
  - Full domains and finite-valuedness are represented by Lean total functions `(Fin n → ℝ) → ℝ`.
  - Convexity and concavity over all of `ℝ^n` are represented by `ConvexOn ℝ Set.univ f` and `ConcaveOn ℝ Set.univ g`.
  - The pointwise underestimator condition is represented by `hfg : ∀ x, g x ≤ f x`.
  - The affine-function witness is represented explicitly as `h : (Fin n → ℝ) → ℝ` together with `IsAffineRealMap h`, which expands to a linear functional plus a constant.
  - The conclusion `∀ x, g x ≤ h x ∧ h x ≤ f x` covers the source's pointwise sandwich inequality `g(x) ≤ h(x) ≤ f(x)`.
- Scope changes:
  - Representation change: `ℝ^n` is encoded as the finite product type `Fin n → ℝ`.
  - Representation bridge: “affine function” is encoded by the implemented predicate `IsAffineRealMap`, i.e. a linear functional plus a constant. This is an explicit bridge and is not an omission.
  - Import change: deprecated `Mathlib.Data.Real.CompleteField` is replaced by `Mathlib.Data.Real.Hom`.
  - No intended mathematical weakening. The Lean theorem makes the source's affine witness explicit and preserves the hypotheses and pointwise conclusion.
- Formal statement review: source-fidelity axes checked. The reviewed Lean statement preserves the source hypotheses, quantifier order, full-domain/finite-valued interpretation, affine-function witness, and sandwich conclusion, modulo the explicit standard representation of `ℝ^n` by `Fin n → ℝ`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```text
Define
\[
E := \{(x,t)\in \mathbb R^n\times \mathbb R : t>f(x)\},
\qquad
H := \{(x,t)\in \mathbb R^n\times \mathbb R : t<g(x)\}.
\]

Since $f$ is convex, $E$ is convex; since $g$ is concave, $H$ is convex.
Because $f$ and $g$ are finite-valued on all of $\mathbb R^n$, they are continuous, so
both $E$ and $H$ are open.
They are also nonempty: for any $x\in\mathbb R^n$,
\[
(x,f(x)+1)\in E,
\qquad
(x,g(x)-1)\in H.
\]
Finally, $E\cap H=\varnothing$, because if $(x,t)\in E\cap H$, then
\[
t>f(x)\ge g(x)>t,
\]
a contradiction.

Therefore, by the Hahn--Banach separation theorem for two disjoint nonempty open convex
sets in a real topological vector space, there exist a nonzero linear functional
$L:\mathbb R^{n+1}\to\mathbb R$ and a scalar $u\in\mathbb R$ such that
\[
L(z)<u \quad \text{for all } z\in H,
\qquad
u<L(z) \quad \text{for all } z\in E.
\]

Let
\[
A(x):=L(x,0), \qquad c:=L(0,1).
\]
Then
\[
L(x,t)=A(x)+ct
\]
for all $(x,t)\in \mathbb R^n\times\mathbb R$, where $A:\mathbb R^n\to\mathbb R$ is linear. Thus
\[
A(x)+ct<u \quad \text{for all } (x,t)\in H,
\]
\[
u<A(x)+ct \quad \text{for all } (x,t)\in E.
\]

We claim that $c>0$.

Assume for contradiction that $c\le 0$.
Since
\[
(0,g(0)-1)\in H,
\qquad
(0,f(0)+1)\in E,
\]
the separation inequalities give
\[
A(0)+c(g(0)-1)<u,
\qquad
u<A(0)+c(f(0)+1).
\]
Since $A(0)=0$, it follows that
\[
c(g(0)-1)<u<c(f(0)+1),
\]
hence
\[
c(g(0)-1)<c(f(0)+1).
\]
On the other hand, from $g(0)\le f(0)$ we have
\[
g(0)-1\le f(0)+1.
\]
Because $c\le 0$, multiplying this inequality by $c$ reverses the direction:
\[
c(f(0)+1)\le c(g(0)-1).
\]
This contradicts
\[
c(g(0)-1)<c(f(0)+1).
\]
Therefore $c>0$.

Now define
\[
h(x):=\frac{u-A(x)}{c}.
\]
Then $h$ is affine.

Fix $x\in\mathbb R^n$ and let $\varepsilon>0$. Since
\[
(x,g(x)-\varepsilon)\in H,
\qquad
(x,f(x)+\varepsilon)\in E,
\]
the separation inequalities give
\[
A(x)+c(g(x)-\varepsilon)<u,
\qquad
u<A(x)+c(f(x)+\varepsilon).
\]
Since $c>0$, dividing by $c$ yields
\[
g(x)-\varepsilon < h(x),
\qquad
h(x)<f(x)+\varepsilon
\qquad (\forall \varepsilon>0).
\]

Hence $g(x)\le h(x)$ and $h(x)\le f(x)$. Indeed, if $h(x)<g(x)$, then taking
\[
\varepsilon=\frac{g(x)-h(x)}{2}>0
\]
contradicts $g(x)-\varepsilon<h(x)`. Similarly, if $f(x)<h(x)$, then taking
\[
\varepsilon=\frac{h(x)-f(x)}{2}>0
\]
contradicts $h(x)<f(x)+\varepsilon$.

Therefore
\[
g(x)\le h(x)\le f(x)\qquad \forall x\in\mathbb R^n.
\]
Thus there exists an affine function $h$ lying between $g$ and $f$.
```

- Prover notes:
  - Work in the product space `(Fin n → ℝ) × ℝ` with strict upper epigraph `E = {z | z.2 > f z.1}` and strict lower hypograph `H = {z | z.2 < g z.1}`.
  - Use convexity/concavity to prove `Convex ℝ E` and `Convex ℝ H`; use continuity of finite convex/concave functions on `Set.univ` if available, or prove openness of strict epi/hypographs from continuity lemmas.
  - Apply `geometric_hahn_banach_open_open` to disjoint nonempty open convex sets. Pay attention to which set receives the `< u` and which receives the `> u` inequality; swap `E`/`H` or negate the functional if needed.
  - Write the separating functional as `A x + c * t`, where `A` is the spatial linear functional and `c` is the coefficient of the scalar coordinate. The source proves `c > 0` by applying the strict separation inequalities to `(0, g 0 - 1)` and `(0, f 0 + 1)`.
  - Define `h x = (u - A x) / c`; show `IsAffineRealMap h` by choosing the linear functional `x ↦ -(A x) / c` and the constant `u / c`.
  - For the pointwise bounds, use `(x, g x - ε) ∈ H` and `(x, f x + ε) ∈ E`, divide by `c > 0`, then close with the source's contradiction argument as `ε → 0`.

## Handoff Notes

- The source document, manifest, context, instructions, and skeleton files were read during review.
- Candidate skeletons were compared against the source.
- The source inventory contains the single source theorem `line-17`; no definitions, lemmas, propositions, corollaries, conjectures, or remarks are present in the source document.
- The Lean statement was corrected to expose the source's affine-function witness `h` and its representation bridge `IsAffineRealMap`.
- The target module is imported by the root project module path (`ShadowBench.lean` → `ShadowBench/Source.lean` → `ShadowBench/Source/Main.lean`), so project-level verification covers it.
- Draft Lean declaration intentionally ends with `by sorry` for the later prover queue.
- Suggested proof command after the verifier stamp: `/prove ShadowBench/Source/Main.lean`.
