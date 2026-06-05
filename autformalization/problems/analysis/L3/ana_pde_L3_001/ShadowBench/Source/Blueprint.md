# Formalization Blueprint: `analysis/L3/ana_pde_L3_001`

- Source document: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.
- Preflight manifest: `.epflemma/workflow-state/formalization/docs-source/manifest.json`
- Manifest support files: no bibliography, references, figures, or PDFs were listed.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem lines 17-45; proof environment lines 46-56 (proof text lines 47-55).
- Source block: theorem `satisfies_interior_sphere`, source label `line-17`.
- Planned Lean declarations: `satisfies_interior_sphere`.
- Lean declaration: `satisfies_interior_sphere` in `ShadowBench/Source/Main.lean`.
- Formal statement review: The Lean statement keeps the source domain as a connected open set `Ω` in the finite-coordinate space `CoordinateSpace n := Fin n → ℝ`; quantifies continuous coefficient fields `a`, `b`, and `c`; records uniform ellipticity via `UniformlyEllipticOn a Ω`; records `c ≤ 0`, `u ∈ C²(Ω)`, `Lu ≥ 0`, and an attained nonnegative maximum at `x₀`; and concludes `∀ x ∈ Ω, u x = M`, matching `u ≡ M` on `Ω`.
- Source qualifiers: for arbitrary finite dimension `n`, the theorem quantifies over a connected open set `Ω ⊆ ℝ^n`; a non-divergence-form linear elliptic operator `L` acting on real-valued functions on `Ω`; continuous coefficient families `a^{ij} : Ω → ℝ`, `b^i : Ω → ℝ`, and `c : Ω → ℝ`; uniform ellipticity of the second-order coefficient matrix on `Ω`; the side condition `c(x) ≤ 0` on `Ω`; a real-valued function `u ∈ C²(Ω)` satisfying `Lu ≥ 0` on `Ω`; an interior point `x₀ ∈ Ω` at which `u` attains the maximum value `M = max_Ω u`; the nonnegativity side condition `M ≥ 0`; and the follow-on conclusion/equality condition `u(x) = M` for every `x ∈ Ω`.
- Lean coverage: `{n : ℕ}` and `CoordinateSpace n := Fin n → ℝ` cover the finite-dimensional source space `ℝ^n`; `Ω`, `hΩ_open : IsOpen Ω`, `hΩ_connected : IsConnected Ω`, and `hx₀ : x₀ ∈ Ω` cover the connected open domain and interior maximum point; `a`, `b`, `c`, `ha_cont`, `hb_cont`, `hc_cont`, `hc_nonpos`, and `h_elliptic : UniformlyEllipticOn a Ω` cover the coefficient assumptions and uniform ellipticity; `firstPartial`, `secondPartial`, and `linearEllipticOperator` encode the displayed operator `Lu`; `u`, `hu_C2 : ContDiffOn ℝ 2 u Ω`, and `h_Lu_nonneg` cover the function class and PDE inequality; `M`, `hM_nonneg`, `hM_attained : u x₀ = M`, and `hM_isMax : ∀ x ∈ Ω, u x ≤ M` cover `u(x₀)=max_Ω u=:M≥0`; the conclusion `∀ x ∈ Ω, u x = M` covers `u ≡ M` in `Ω`.
- Scope changes: no mathematical weakening or strengthening. Representation bridges used and checked: source `ℝ^n` is represented by `CoordinateSpace n := Fin n → ℝ`; source coordinate derivatives `u_i` and `u_{ij}` are represented by Fréchet derivatives in the coordinate directions `Pi.single i 1`; the displayed maximum notation `M = max_Ω u` is represented by explicit attainment at `x₀` plus the upper-bound property on `Ω`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Let `v = M - u`. Then `v ≥ 0`, `v x₀ = 0`, and the operator inequality reverses to `Lv ≤ 0`. Let `A = {x ∈ Ω | v x = 0}`; it is closed and nonempty. If a point of `A` is not interior, use an interior tangent ball and Hopf's lemma to get a strictly negative normal derivative, contradicting the zero gradient at an interior minimum. Hence `A` is open; connectedness of `Ω` gives `A = Ω`, so `u = M` on `Ω`.

#### Complete source statement

Let $\Omega\subset \mathbb{R}^n$ be connected and open. Let
\[
Lu = \sum_{i,j=1}^n a^{ij}(x)u_{ij} + \sum_{i=1}^n b^i(x)u_i + c(x)u
\]
be uniformly elliptic in $\Omega$, where $a^{ij},b^i,c$ are continuous and
\[
c(x)\le 0 \qquad \text{in } \Omega.
\]
Suppose
\[
u\in C^2(\Omega), \qquad Lu\ge 0 \quad \text{in } \Omega.
\]
If $u$ attains a nonnegative maximum at an interior point $x_0\in \Omega$, i.e.
\[
u(x_0)=\max_{\Omega}u=:M\ge 0,
\]
then
\[
u\equiv M \qquad \text{in } \Omega.
\]

#### Lean statement

```lean
theorem satisfies_interior_sphere {n : ℕ}
    (Ω : Set (CoordinateSpace n))
    (hΩ_open : IsOpen Ω)
    (hΩ_connected : IsConnected Ω)
    (a : Fin n → Fin n → CoordinateSpace n → ℝ)
    (b : Fin n → CoordinateSpace n → ℝ)
    (c : CoordinateSpace n → ℝ)
    (ha_cont : ∀ i j, ContinuousOn (a i j) Ω)
    (hb_cont : ∀ i, ContinuousOn (b i) Ω)
    (hc_cont : ContinuousOn c Ω)
    (h_elliptic : UniformlyEllipticOn a Ω)
    (hc_nonpos : ∀ x ∈ Ω, c x ≤ 0)
    (u : CoordinateSpace n → ℝ)
    (hu_C2 : ContDiffOn ℝ 2 u Ω)
    (h_Lu_nonneg : ∀ x ∈ Ω, linearEllipticOperator a b c u x ≥ 0)
    (x₀ : CoordinateSpace n)
    (hx₀ : x₀ ∈ Ω)
    (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hM_attained : u x₀ = M)
    (hM_isMax : ∀ x ∈ Ω, u x ≤ M) :
    ∀ x ∈ Ω, u x = M
```

#### Complete source proof text

Let $M=\max_{\Omega}u$ and set $v:=M-u$. Then $v\ge 0$, $v(x_0)=0$, and $Lv\le 0$.

Let $A:=\{x\in\Omega:\, v(x)=0\}$. Then $A$ is closed and nonempty.

If $z\in A$ is not interior, pick $y\notin A$ and a ball $B_\rho(y)\subset\Omega$ tangent to $A$ at $z_0\in A$; then $v>0$ in $B_\rho(y)$ and $v(z_0)=0$.

By the Hopf lemma, $\partial_\nu v(z_0)<0$, but $z_0$ is an interior minimum of $v$, so $\nabla v(z_0)=0$ — contradiction.

Hence $A$ is open; since $\Omega$ is connected, $A=\Omega$, so $u\equiv M$.

## Import Plan

Direct imports used by `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Real.Basic
```

`ShadowBench/Source.lean` directly imports `ShadowBench.Source.Main` so a plain `lake build` covers the generated target module.

## Suggested Search Modules

These are search hints only, not direct imports unless a later prover needs them.

- `Mathlib.Topology.LocallyConstant.Basic` for connected/preconnected local-constancy patterns.
- `Mathlib.Analysis.Calculus.FDeriv.Pi` for coordinate derivative facts involving `Pi.single`.
- PDE Hopf/strong maximum principle facts were searched but no direct Mathlib theorem was found.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: one-file draft containing the finite-coordinate PDE definitions and the source theorem skeleton.
- `ShadowBench/Source.lean`: root project module importing `ShadowBench.Source.Main`.

## Definitions and Local Conventions

- `CoordinateSpace n := Fin n → ℝ`: finite-coordinate model for the source space `ℝ^n`.
- `firstPartial i u x`: coordinate first derivative `u_i`, encoded as `fderiv ℝ u x (Pi.single i 1)`.
- `secondPartial i j u x`: coordinate second derivative `u_{ij}`, encoded by differentiating `firstPartial j u` in direction `Pi.single i 1`.
- `linearEllipticOperator a b c u x`: the non-divergence-form expression
  `∑ i, ∑ j, a i j x * secondPartial i j u x + ∑ i, b i x * firstPartial i u x + c x * u x`.
- `UniformlyEllipticOn a Ω`: existence of a positive lower ellipticity constant for the quadratic form of the coefficient matrix on `Ω`.

## Required Lean Names

- `satisfies_interior_sphere`

## Search and Planning Notes

- `formalization_document_inspect` re-inspected `docs/source.tex` and found the single theorem block `line-17`.
- Local/project and Mathlib searches were run before drafting; no direct formal strong maximum principle/Hopf lemma theorem for this PDE operator was found.
- The draft therefore records the source statement faithfully and leaves the theorem proof as the single later `/prove` obligation after independent statement/source review.

## Handoff Checklist

- [x] Source document and preflight manifest read.
- [x] Instructions and all candidate skeletons read and compared against the source.
- [x] Local/project and Mathlib search run before drafting.
- [x] Blueprint source statement inventory includes `line-17` with source qualifiers, Lean coverage, scope bridge, full source proof text, and prover notes.
- [x] Root project module `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- [x] Project-level Lean verification passed for the draft.
- [ ] Run independent statement/source verification review and apply corrections.
- [ ] Mark stable theorem/lemma/example `sorry` declarations ready for a user-started prove workflow.
