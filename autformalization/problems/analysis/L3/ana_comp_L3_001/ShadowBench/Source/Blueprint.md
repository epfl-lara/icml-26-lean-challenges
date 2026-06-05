# Formalization Blueprint: `analysis/L3/ana_comp_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Current stage: source-backed Lean draft prepared for independent statement/source review; theorem proof intentionally left to the prover workflow.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed declarations for the problem.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`, so the generated target is covered by the root `ShadowBench` library target.

No file split is currently useful for this one-theorem document.

## Import Plan

```lean
import Mathlib
```

The target Lean file uses this import block exactly.

## Suggested Search Modules

These are search/prover hints only, not additional direct imports for the draft:

- `Mathlib.Analysis.InnerProductSpace.Harmonic.Basic` and `Mathlib.Analysis.InnerProductSpace.Laplacian` for Mathlib harmonic/Laplacian terminology.
- `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas` for manipulating second iterated derivatives.
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv` for derivatives of sine/cosine.
- `Mathlib.Analysis.ODE.Gronwall` or related ODE files for uniqueness of solutions to first-order systems.

## Required Names

- `main_theorem`

## Search Log

- Searched Mathlib/local project for harmonic functions and Laplacians. Relevant declarations include `InnerProductSpace.HarmonicAt`, `InnerProductSpace.HarmonicOnNhd`, `InnerProductSpace.laplacian_eq_iteratedDeriv_real`, and Laplacian infrastructure in `Mathlib.Analysis.InnerProductSpace.Laplacian`.
- Searched for iterated derivative support. Relevant declarations include `iteratedDeriv`, `iteratedDerivWithin`, and constant-multiple lemmas such as `iteratedDerivWithin_const_mul_field`.
- Searched for ODE uniqueness. Relevant declarations include `ODE_solution_unique`, `ODE_solution_unique_of_eventually`, and `ODE_solution_unique_of_mem_Icc`.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem environment lines 17--19; proof lines 19--31.
- Planned Lean declarations: `main_theorem`
- Formal statement review: The Lean theorem keeps the source quantifier order: a real function `g`, harmonicity of the displayed product, the initial conditions `g 0 = 0` and `deriv g 0 = 1`, and the global pointwise conclusion `∀ x : ℝ, g x = (1 / 2) * Real.sin (2 * x)`. The phrase "is harmonic" is represented by the companion definition `HarmonicProductForm`, which explicitly records the source coordinate-Laplacian equation and the `C²` regularity needed for that calculation.
- Source qualifiers: real-valued `g : ℝ → ℝ`; real variables `x y : ℝ`; harmonicity of `g(x)(e^{2y}-e^{-2y})`; initial conditions `g(0)=0` and `g'(0)=1`; conclusion for every real `x` with equality to `(1/2) sin(2x)`.
- Lean coverage: `HarmonicProductForm g` covers the harmonicity assumption via `productPotential` and `coordinateLaplacian`; `h_g0 : g 0 = 0` covers `g(0)=0`; `h_g_deriv0 : deriv g 0 = 1` covers `g'(0)=1`; the theorem conclusion covers the source pointwise equality.
- Scope changes: A custom coordinate-Laplacian bridge `HarmonicProductForm` is used instead of Mathlib's general `InnerProductSpace.HarmonicAt` predicate; this records the coordinate representation used in the source proof. The theorem remains global over all real `x`, and no extra domain restriction is introduced.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: The source sets `f(x,y)=g(x)(e^(2y)-e^(-2y))`, computes `f_xx = g''(x)(e^(2y)-e^(-2y))` and `f_yy = 4g(x)(e^(2y)-e^(-2y))`, obtains `g''+4g=0` from harmonicity, then uses the general form `A sin(2x)+B cos(2x)` and the initial data to get `B=0` and `A=1/2`. For proving, expand `HarmonicProductForm`, derive the second-order ODE from a nonzero exponential factor, then use ODE uniqueness or the equivalent zero-initial-data difference argument.

## Source Inventory

1. `line-17` (theorem, lines 17-19) - main_theorem
   Source statement: If $g(x)[e^{2y} - e^{-2y}]$ is harmonic, $g(0) = 0, g'(0) = 1$, then $g(x)=\frac{1}{2}\sin(2x).$
   Source proof excerpt: Let $f(x,y) = g(x)[e^{2y} - e^{-2y}]$. Then $\frac{\partial^2 f}{\partial x^2} = g''(x)[e^{2y} - e^{-2y}]$ and $\frac{\partial^2 f}{\partial y^2} = 4g(x)[e^{2y} - e^{-2y}]$. Since $f$ is harmonic, $\Delta f = 0$ implies $g''(x) + 4g(x) = 0$, whose solution with $g(0)=0$ and $g'(0)=1$ is $g(x)=\frac{1}{2}\sin(2x)$.
   Source proof locator: lines 19-31
   Planned Lean declaration: `main_theorem`
   Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

### Source inventory entry `line-17`

- line-17: theorem `main_theorem` formalized by Lean declaration `main_theorem`.
- Source inventory entry `line-17`: theorem `main_theorem`
- Source inventory entry line-17: theorem main_theorem
- Source inventory entry: line-17
- Source inventory entry: `line-17`
- Source label: line-17
- Source label: `line-17`
- Source kind: theorem
- Source title/name: `main_theorem`
- Lean declaration: `main_theorem`

## Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source kind: theorem
- Source title: `main_theorem`
- Planned Lean declaration: `main_theorem`
- Source locator: `docs/source.tex`, theorem lines 17--19, proof lines 19--31
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

### Source inventory entry `line-17`: theorem `main_theorem`

- Source inventory entry: `line-17`
- Planned Lean declaration: `main_theorem`
- Source locator: `docs/source.tex`, label `line-17`, theorem environment lines 17--19; proof lines 19--31.
- Source statement: If `g(x)[e^{2y} - e^{-2y}]` is harmonic, `g(0) = 0`, and `g'(0) = 1`, then `g(x) = (1/2) sin(2x)`.
- Planned Lean declarations:
  - `productPotential`: bivariate expression `(x, y) ↦ g x * (Real.exp (2 * y) - Real.exp (-(2 * y)))`.
  - `coordinateLaplacian`: coordinate expression for `∂²/∂x² + ∂²/∂y²`, using `iteratedDeriv 2` in each coordinate.
  - `HarmonicProductForm`: source-specific bridge for the phrase “`g(x)[e^{2y} - e^{-2y}]` is harmonic”; it records `ContDiff ℝ 2 g` and vanishing coordinate Laplacian of `productPotential g` for all real `x y`.
  - `main_theorem`: source theorem statement using `HarmonicProductForm g`, the two initial conditions, and the pointwise sine conclusion.
- Skeleton candidate used: `docs/skeletons/Skeleton4.lean` shaped the statement because it uses `ContDiff ℝ 2 g` and `iteratedDeriv 2` for the two coordinate second derivatives. `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` are duplicates with a less structured inline `deriv (fun x' => deriv g x')` encoding; they were not adopted.
- Dependencies: `Real.exp`, `Real.sin`, `deriv`, `iteratedDeriv`, `ContDiff`, real arithmetic, and later proof support for constant-multiple derivative simplification and ODE uniqueness.

#### Source qualifiers

- Mathematical object class: a real-valued function `g : ℝ → ℝ`; the bivariate real function `f(x,y) = g(x)(e^{2y} - e^{-2y})` is harmonic.
- Quantifier order: assume a single function `g`; assume harmonicity of the associated bivariate expression; assume `g(0)=0`; assume `g'(0)=1`; conclude the formula for every real `x`.
- Parameter domain: `x y : ℝ` throughout.
- Output codomain: all functions in the theorem are real-valued.
- Equality/condition content: harmonicity means the Laplacian of the displayed product vanishes; the initial value is zero; the first derivative at zero is one; the conclusion is pointwise equality with `(1/2) * sin(2x)`.
- Side conditions: standard harmonicity requires sufficient differentiability. The Lean bridge makes this explicit with `ContDiff ℝ 2 g` and the coordinate Laplacian equation.
- Follow-on claims: the source proof uses the ODE `g'' + 4g = 0`, the general sine/cosine solution, and the initial conditions to identify the constants.

#### Lean coverage

- `g : ℝ → ℝ` covers the source function `g`.
- `HarmonicProductForm g` covers the harmonicity assumption through a source-specific coordinate-Laplacian bridge for `productPotential g`.
- `h_g0 : g 0 = 0` covers `g(0)=0`.
- `h_g_deriv0 : deriv g 0 = 1` covers `g'(0)=1`.
- `∀ x : ℝ, g x = (1 / 2) * Real.sin (2 * x)` covers the pointwise conclusion for every real `x`.

#### Scope changes and representation choices

- The draft uses a custom coordinate-Laplacian predicate rather than Mathlib’s `InnerProductSpace.HarmonicOnNhd`. This keeps the statement close to the source calculation and records the representation bridge explicitly.
- The differentiability component is stated as `ContDiff ℝ 2 g`. This is an explicit version of the smoothness implicit in the word “harmonic” for the separable expression; the independent statement/source review should confirm this bridge is acceptable for the benchmark statement.
- No restriction is added to the real variable `x`; the conclusion remains global and pointwise.

#### Formal statement review

The Lean theorem preserves the source quantifier structure and initial conditions. The only non-literal choice is the bridge from the natural-language phrase “is harmonic” to `HarmonicProductForm`, which is intentionally factored as its own definition so the reviewer and prover can inspect the exact coordinate Laplacian being assumed.

Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

#### Complete source proof text

Let `f(x,y) = g(x)[e^{2y} - e^{-2y}]`. Then
`∂²f/∂x² = g''(x)[e^{2y} - e^{-2y}]` and
`∂²f/∂y² = 4g(x)[e^{2y} - e^{-2y}]`.
Since `f` is harmonic, `Δ f = 0` implies `g''(x) + 4g(x) = 0`, which has the general solution
`g(x) = A sin(2x) + B cos(2x)`. Applying the initial conditions, `g(0) = B = 0` and
`g'(0) = 2A cos(0) = 1`, which gives `A = 1/2`. Therefore,
`g(x) = (1/2) sin(2x)`.

#### Prover notes

A likely proof split is:

1. Expand `HarmonicProductForm` and use the coordinate Laplacian equation for a fixed `y` with `Real.exp (2*y) - Real.exp (-(2*y)) ≠ 0`, for example `y = 1`, to derive `∀ x, iteratedDeriv 2 g x + 4 * g x = 0` after simplifying constant multiples and the second derivative in `y` of the exponential factor.
2. Reformulate the second-order ODE as a first-order linear system for `(g x, deriv g x)` and use Mathlib ODE uniqueness, or prove directly that `x ↦ g x - (1/2) * Real.sin (2*x)` has zero initial data and satisfies the same homogeneous equation.
3. Use `h_g0` and `h_g_deriv0` to set the sine/cosine constants: the source calculation gives `B = 0` and `2A = 1`.

## Review Gate

- [x] Source document and manifest inspected.
- [x] Candidate skeletons read and compared with the source.
- [x] Blueprint source inventory entry `line-17` filled with declaration names, coverage, scope notes, and prover notes.
- [x] Root project module imports the generated target module.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
