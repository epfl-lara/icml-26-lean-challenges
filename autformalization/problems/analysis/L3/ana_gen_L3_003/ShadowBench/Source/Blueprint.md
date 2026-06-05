# Formalization Blueprint: `analysis/L3/ana_gen_L3_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Document Review

- Document inspected with `formalization_document_inspect` on `docs/source.tex`.
- Preflight manifest: `.epflemma/workflow-state/formalization/docs-source/manifest.json`.
- No bibliography files, citations, section headings, PDFs, or figures are listed in the manifest.
- Detected theorem-like source blocks: one theorem, `line-17`, named `convexOn_sq_div`, with proof at lines 19-37.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the formal statement for the source theorem.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

## Import Plan

```lean
import Mathlib
```

## Suggested Search Modules

- `Mathlib.Analysis.Convex.Function` for `ConvexOn`, `ConcaveOn`, restriction and composition lemmas.
- `Mathlib.Analysis.Convex.Mul` for convexity of powers/products if a prover chooses a derived proof route.
- Scalar real inequality lemmas around squares, division by positive denominators, and `nlinarith`/`field_simp` may be useful for the quadratic-over-linear Jensen inequality.

## Required Names

- `convexOn_sq_div`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` propose the same finite-dimensional statement over `Fin n → ℝ`, with domain sets `dom_f` and `dom_g`, hypotheses that `f` is nonnegative and convex on `dom_f`, `g` is positive and concave on `dom_g`, and conclusion convexity of `x ↦ f x ^ 2 / g x` on `dom_f ∩ dom_g`.
- `docs/skeletons/Skeleton4.lean` proposes a more general real vector-space statement.
- The draft adopts the finite-dimensional shape from Skeletons 1-3 because it matches the source object class `ℝ^n → ℝ` more literally than the generalized vector-space version. The statement is written directly rather than using local `let` bindings, so the theorem conclusion is transparent to later proof search.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source label: `line-17`
- Source kind: theorem
- Source title/name: `convexOn_sq_div`
- Source locator: `docs/source.tex`, theorem environment lines 17--19; proof lines 19--37.
- Source statement: Suppose that `f : ℝ^n → ℝ` is nonnegative and convex, and `g : ℝ^n → ℝ` is positive and concave. Show that `f^2/g`, with domain `dom f ∩ dom g`, is convex.
- Complete source proof text: see the verbatim source proof block in the detailed Statement Inventory below.
- Planned Lean declarations: `convexOn_sq_div`.
- Formal statement review: The Lean statement represents `ℝ^n` as `Fin n → ℝ`, uses explicit domain sets `dom_f` and `dom_g` for Lean total functions, assumes `ConvexOn ℝ dom_f f`, `ConcaveOn ℝ dom_g g`, `0 ≤ f x` on `dom_f`, and `0 < g x` on `dom_g`, and concludes `ConvexOn ℝ (dom_f ∩ dom_g) (fun x => (f x)^2 / g x)`.
- Source qualifiers: mathematical object class is real finite-dimensional space `ℝ^n`; quantifiers range over the dimension `n`, source domains, functions `f g`, then the side conditions; parameter domain is `dom f` for the nonnegativity/convexity of `f`, `dom g` for the positivity/concavity of `g`, and the common domain `dom f ∩ dom g` for the quotient; output codomain is `ℝ`; side conditions are `f ≥ 0` and convex on its domain and `g > 0` and concave on its domain; equality/image condition is pointwise `x ↦ f(x)^2/g(x)`; follow-on claim is convexity of that quotient function on the common domain.
- Lean coverage: exact. `Fin n → ℝ` is the coordinate model used for the source object `ℝ^n`; explicit set parameters `dom_f` and `dom_g` are the Lean bridge for the source domains of the otherwise total functions; `ConvexOn`/`ConcaveOn` carry the convex-domain/function inequalities, and the conclusion is on `dom_f ∩ dom_g` for `x ↦ (f x)^2/g x`.
- Scope changes: `none`.
- Representation notes: the standard coordinate model `Fin n → ℝ` represents `ℝ^n`, and explicit domain sets represent `dom f`, `dom g` for Lean total functions; no source qualifier is omitted.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Later proof can either formalize the monotone convex/concave composition rule or prove Jensen directly using the scalar inequality `(a*u+b*v)^2/(a*r+b*s) ≤ a*(u^2/r)+b*(v^2/s)` for `u,v ≥ 0`, `r,s > 0`.

## Source Inventory

1. `line-17` (theorem, lines 17-19) - convexOn_sq_div
   Source statement: Suppose that $f : \mathbb{R}^n \to \mathbb{R}$ is nonnegative and convex, and $g : \mathbb{R}^n \to \mathbb{R}$ is positive and concave. Show that the function $f^2/g$, with domain $\mathbf{dom} f \cap \mathbf{dom} g$, is convex.
   Source proof excerpt: The proof introduces the quadratic-over-linear map `h(x,y)=x^2/y`, notes that it is convex, non-decreasing in `x` on `x ≥ 0`, and non-increasing in `y` on `y > 0`, then applies the convex/concave composition rule to `h(f(z),g(z))`.
   Lean declarations: `convexOn_sq_div`.
   Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

### Source inventory entry `line-17`: theorem `convexOn_sq_div`

- line-17: theorem `convexOn_sq_div` formalized by Lean declaration `convexOn_sq_div`.
- Source inventory entry `line-17`: theorem `convexOn_sq_div`
- Source inventory entry line-17: theorem convexOn_sq_div
- Source inventory entry: line-17
- Source inventory entry: `line-17`
- Source label: line-17
- Source label: `line-17`
- Source kind: theorem
- Source title/name: `convexOn_sq_div`
- Lean declaration: `convexOn_sq_div`

## Statement Inventory

### line-17

- Source inventory entry: `line-17`.
- Source label: `line-17`.
- Source kind: theorem.
- Source title/name: `convexOn_sq_div`.
- Planned Lean declaration: `convexOn_sq_div` in `ShadowBench/Source/Main.lean`.
- Source locator: `docs/source.tex`, theorem block lines 17-19, proof lines 19-37.
- Source statement: Suppose that `f : ℝ^n → ℝ` is nonnegative and convex, and `g : ℝ^n → ℝ` is positive and concave. Show that the function `f^2/g`, with domain `dom f ∩ dom g`, is convex.
- Lean statement:

```lean
theorem convexOn_sq_div {n : ℕ} {dom_f dom_g : Set (Fin n → ℝ)}
    (f g : (Fin n → ℝ) → ℝ)
    (hf_nonneg : ∀ x ∈ dom_f, 0 ≤ f x)
    (hf_convex : ConvexOn ℝ dom_f f)
    (hg_pos : ∀ x ∈ dom_g, 0 < g x)
    (hg_concave : ConcaveOn ℝ dom_g g) :
    ConvexOn ℝ (dom_f ∩ dom_g) (fun x => (f x) ^ 2 / g x) := by
  sorry
```

- Skeleton candidate used: Skeletons 1-3, adjusted to a direct conclusion without `let` bindings; Skeleton4 noted as a valid generalization but not adopted to preserve the literal `ℝ^n` source class.
- Dependencies: `Mathlib`; principal notions are `ConvexOn`, `ConcaveOn`, finite-dimensional Euclidean model `Fin n → ℝ`, set intersection, real square/division.
- Source qualifiers:
  - Mathematical object class: finite-dimensional real vectors `ℝ^n`, represented by `Fin n → ℝ`.
  - Quantifier order: choose `n`, domains `dom_f dom_g`, functions `f g`, then nonnegativity/convexity assumptions for `f` and positivity/concavity assumptions for `g`.
  - Parameter domains: `f` is controlled on `dom_f`; `g` is controlled on `dom_g`; conclusion is on `dom_f ∩ dom_g`.
  - Output codomain: real-valued functions.
  - Side conditions: `0 ≤ f x` on `dom_f`, `0 < g x` on `dom_g`; the strict positivity gives nonzero denominators on the conclusion domain.
  - Equality/image condition: the target function is pointwise `x ↦ (f x)^2 / g x`.
  - Follow-on claim: convexity of this quotient function on the common domain.
- Lean coverage: exact modulo the standard Lean representation of `ℝ^n` as `Fin n → ℝ` and convex-analysis domains as explicit sets for total functions. The assumptions on `dom_f` and `dom_g` are carried by `ConvexOn`/`ConcaveOn`, and the result uses their intersection as the source domain specifies.
- Scope changes: `none`.
- Representation notes: the source's informal `dom f` and `dom g` are represented explicitly by set parameters `dom_f` and `dom_g` because Lean functions are total; this is the Lean domain bridge, not an omission.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text (verbatim from `docs/source.tex`, lines 21--36):

```text
Consider the function $h : \mathbb{R} \times \mathbb{R}_{++} \to \mathbb{R}$ defined by $h(x, y) = x^2 / y$.
It is easy to show that the quadratic-over-linear function $h$ is convex.

Furthermore, we observe the monotonicity properties of $h(x, y)$ on the restricted domain where $x \ge 0$ and $y > 0$:
\begin{itemize}
    \item $h$ is non-decreasing in $x$, because $\frac{\partial h}{\partial x} = \frac{2x}{y} \ge 0$.
    \item $h$ is non-increasing in $y$, because $\frac{\partial h}{\partial y} = -\frac{x^2}{y^2} \le 0$.
\end{itemize}

Now, consider the composition $h(f(z), g(z)) = f(z)^2 / g(z)$.
By the assumptions, $f(z) \ge 0$ and $g(z) > 0$ for all $z \in \mathbf{dom} f \cap \mathbf{dom} g$, meaning the outputs of $f$ and $g$ always fall into the region where the above monotonicity properties hold.

We can apply the composition rule: since $f$ is convex, $g$ is concave, and the outer function $h$ is convex, non-decreasing in its first argument, and non-increasing in its second argument (on the range of the inner functions), the composition $h(f(z), g(z))$ is convex.

Therefore, $f^2/g$ is convex.
```
- Prover notes: A future proof can either formalize the stated composition argument or prove the Jensen inequality directly. For `x,y ∈ dom_f ∩ dom_g` and weights `a,b ≥ 0`, `a+b=1`, use convexity of `f` and concavity of `g` to compare the numerator and denominator with `a*f x+b*f y` and `a*g x+b*g y`; then apply the scalar quadratic-over-linear inequality
  `(a*u + b*v)^2 / (a*r + b*s) ≤ a*(u^2/r) + b*(v^2/s)` for `u,v ≥ 0`, `r,s > 0`. Clearing denominators reduces the scalar inequality to a square nonnegativity/Cauchy-style calculation. The positivity hypotheses should discharge denominator side conditions.

## Formalization Rules

```text
/-
Formalize in Lean the Theorem (convexOn_sq_div) from Text.

The theorem must be named `convexOn_sq_div`.
   Matched text (candidate 0, theorem, label=convexOn_sq_div): \begin{theorem}[convexOn_sq_div] Suppose that $f : \mathbb{R}^n \to \mathbb{R}$ is
                                                               nonnegative and convex, and $g : \mathbb{R}^n \to \mathbb{R}$ is positive and concave. Show
                                                               that the function $f^2/g$, with domain $\mathbf{dom} f \cap \mathbf{dom} g$, is convex.
                                                               \end{theorem}
-/
```

## Review Checklist

- [x] Source document and manifest inspected.
- [x] Candidate skeletons compared against the source theorem.
- [x] Lean statement drafted with source proof/prover notes in the Lean doc comment.
- [x] Root project module path includes `ShadowBench.Source.Main` through `ShadowBench.Source`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
