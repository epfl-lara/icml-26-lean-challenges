# Formalization Blueprint: `analysis/L4/ana_pde_L4_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: one-file source-backed draft containing the representation bridge, operator definitions, coefficient predicates, and the two required source declarations.
- `ShadowBench/Source.lean`: root project module importing `ShadowBench.Source.Main`, so a project build covers the generated target module.

No split into auxiliary Lean files is planned for this short source document.

## Import Plan

```lean
import Mathlib
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
```

The import block above is identical to the target Lean file import block.

## Suggested Search Modules

These are non-gating hints found during local/Mathlib search and are not forced into the Lean import block beyond the direct imports above.

- `Mathlib.Analysis.Calculus.ContDiff.Defs` for `ContDiffOn` and Fréchet derivatives.
- `Mathlib.Topology.Closure` for `closure`/`frontier` facts.
- `Mathlib.Topology.MetricSpace.Bounded` for `Bornology.IsBounded` facts.
- `Mathlib.Order.Filter.Extr` for possible maximum-on-set API (`IsMaxOn`) if a later proof wants it.

Search notes: local/project search found no existing source theorem. Mathlib search found no direct uniformly elliptic PDE maximum principle; the formalization therefore records the PDE operator and assumptions explicitly.

## Required Names

- `no_interior_max_of_Lu_pos`
- `main_theorem`

## Representation and Definition Plan

- `PDEPoint n := Fin n → ℝ` represents the source space `ℝ^n` with coordinate access by `Fin n`.
- `firstCoordDeriv u x i` represents `u_i(x)` using `fderiv ℝ u x (Pi.single i 1)`.
- `secondCoordDeriv u x i j` represents `u_{ij}(x)` using the derivative of the Fréchet derivative in coordinate directions.
- `Lu a b c u x` implements the displayed operator
  `∑ᵢⱼ a^{ij}(x) u_{ij}(x) + ∑ᵢ b^i(x) u_i(x) + c(x) u(x)`.
- `UniformlyEllipticOn Ω a` encodes uniform ellipticity as a positive lower quadratic-form bound on the coefficient matrix over `Ω`.
- `ContinuousCoefficientsOn Ω a b c` and `BoundedCoefficientsOn Ω a b c` record the source assumptions that the coefficients are continuous and bounded.
- `HasNonnegativeMaximumOnClosure Ω u M` bridges the source phrase “u has/attains a nonnegative maximum in `\bar Ω`” by naming a maximum value `M`, asserting `u ≤ M` on `closure Ω`, asserting `M` is attained on `closure Ω`, and asserting `0 ≤ M`.

## Source Statement Inventory

### line-17

- Source inventory label: `line-17`
- Planned Lean declarations: `no_interior_max_of_Lu_pos`
- Source locator: `docs/source.tex`, lemma environment lines 17–25; proof lines 25–32.
- Skeleton candidate used: shaped primarily by `docs/skeletons/Skeleton4.lean`, because it uses `Fin n → ℝ`, includes openness of the domain, includes explicit uniform ellipticity, coefficient continuity/boundedness, and states contradiction from an interior maximum. The final draft replaces the raw `M` hypotheses with the bridge predicate `HasNonnegativeMaximumOnClosure` and uses the reusable `Lu` definition. Skeletons 1–3 were used only as hints for the displayed operator and were not adopted because their maximum witness shape is less stable and they omit explicit domain openness.
- Dependencies: `PDEPoint`, `firstCoordDeriv`, `secondCoordDeriv`, `Lu`, `UniformlyEllipticOn`, `ContinuousCoefficientsOn`, `BoundedCoefficientsOn`, `HasNonnegativeMaximumOnClosure`.
- Source statement: Suppose `Ω` is a bounded connected domain in `ℝ^n`; `Lu = ∑ᵢⱼ a^{ij}(x)u_{ij}+∑ᵢ b^i(x)u_i+c(x)u` is uniformly elliptic with continuous bounded coefficients and `c≤0`; `u ∈ C²(Ω) ∩ C(\bar Ω)` satisfies `Lu>0` in `Ω`; if `u` has a nonnegative maximum in `\bar Ω`, then `u` cannot attain this maximum in `Ω`.
- Formal statement review: the Lean statement quantifies over `n`, `Ω`, coefficients `a b c`, `u`, and a maximum value `M`. It assumes domain, ellipticity, coefficient regularity/boundedness, `c≤0`, `u` regularity, `Lu>0`, and `HasNonnegativeMaximumOnClosure Ω u M`; it concludes `¬ ∃ x ∈ Ω, u x = M`. This exactly captures the lemma’s “cannot attain this maximum in the interior” once the source phrase “nonnegative maximum” is interpreted through the bridge predicate.
- Source qualifiers:
  - Mathematical object class: bounded connected domain in `ℝ^n`.
  - Quantifier order: domain/operator/function/max assumptions precede the no-interior-attainment conclusion.
  - Parameter domain: all points lie in `Ω`, `closure Ω`, or `frontier Ω` as specified.
  - Output codomain: real-valued scalar function and real-valued coefficients.
  - Equality/attainment condition: interior point would satisfy `u x = M`, where `M` is the closure maximum value.
  - Side conditions: uniform ellipticity, coefficient continuity and boundedness, `c≤0`, `u` is `C²` on `Ω` and continuous on `closure Ω`, `Lu>0` on `Ω`, and `0≤M`.
  - Follow-on claim: no point of `Ω` attains that maximum value.
- Lean coverage:
  - `ℝ^n` is covered by `PDEPoint n`.
  - “Domain” is covered by `hΩ_open : IsOpen Ω`, `hΩ_connected : IsConnected Ω`, and `hΩ_bounded : Bornology.IsBounded Ω`.
  - The displayed operator is covered by `Lu`.
  - Uniform ellipticity is covered by `UniformlyEllipticOn Ω a`.
  - Coefficient regularity/boundedness is covered by `ContinuousCoefficientsOn Ω a b c` and `BoundedCoefficientsOn Ω a b c`.
  - `c≤0` and `Lu>0` are covered by pointwise hypotheses on `Ω`.
  - `C²(Ω) ∩ C(\bar Ω)` is covered by `ContDiffOn ℝ 2 u Ω` and `ContinuousOn u (closure Ω)`.
  - The nonnegative closure maximum is covered by `HasNonnegativeMaximumOnClosure Ω u M`.
- Scope changes: representation bridge from source `ℝ^n` to `Fin n → ℝ`; uniform ellipticity is encoded by the lower quadratic-form bound and does not separately assert a symmetry convention; nonemptiness of the domain is not a separate hypothesis because the maximum-attainment bridge supplies the needed inhabited closure point.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: “Suppose `u` attains its nonnegative maximum of `\bar{Ω}` at `x₀ ∈ Ω`. Then `Dᵢu(x₀)=0` and the matrix `[Dᵢⱼu(x₀)]` is semi-negative definite. By the ellipticity condition, the matrix `aᵢⱼ(x₀)` is positive definite. This implies `Lu(x₀)=aᵢⱼ(x₀)Dᵢⱼu(x₀)≤0`, which is a contradiction.”
- Prover notes: unfold `Lu` and argue at an assumed interior maximum point. The source proof needs the first derivative to vanish and the Hessian to be negative semidefinite at an interior maximum, then combines this with the ellipticity/positive-definiteness of `a` and `c≤0` plus `0≤u x₀` to contradict `Lu x₀ > 0`. These analytic facts are nontrivial in Lean and may require helper lemmas about Fréchet derivatives at interior extrema.

### line-35

- Source inventory label: `line-35`
- Planned Lean declarations: `main_theorem`
- Source locator: `docs/source.tex`, theorem environment lines 35–44; proof paragraph after the theorem through the end of the document.
- Skeleton candidate used: shaped primarily by `docs/skeletons/Skeleton4.lean`, because it gives a boundary-attainment conclusion for a named maximum value and includes the domain/operator side conditions. The final draft uses the bridge predicate `HasNonnegativeMaximumOnClosure` and concludes boundary attainment of the same nonnegative maximum value.
- Dependencies: all dependencies of `no_interior_max_of_Lu_pos`; mathematically the source proof also uses the lemma `no_interior_max_of_Lu_pos` applied to the perturbed function `w(x)=u(x)+ε exp(α x₁)`.
- Source statement: Under the same bounded connected domain, uniformly elliptic operator, continuous bounded coefficient, `c≤0`, `u ∈ C²(Ω) ∩ C(\bar Ω)`, and `Lu>0` assumptions, `u` attains on `∂Ω` its nonnegative maximum in `\bar Ω`.
- Formal statement review: the Lean statement is a conditional maximum-value formulation: given a value `M` satisfying `HasNonnegativeMaximumOnClosure Ω u M`, it concludes `∃ x ∈ frontier Ω, u x = M ∧ 0 ≤ u x`. This captures boundary attainment of the specified nonnegative closure maximum. The explicit `M`/maximum assumption records the source phrase “its nonnegative maximum” rather than deriving existence of a maximum from compactness.
- Source qualifiers:
  - Mathematical object class: bounded connected domain in `ℝ^n` with boundary `∂Ω`.
  - Quantifier order: domain/operator/function assumptions precede the boundary-attainment conclusion.
  - Parameter domain: operator inequalities on `Ω`; maximum over `closure Ω`; boundary point in `frontier Ω`.
  - Output codomain: real-valued scalar function and real-valued coefficients.
  - Equality/attainment condition: the boundary point has value equal to the closure maximum value `M`.
  - Side conditions: uniform ellipticity, coefficient continuity and boundedness, `c≤0`, `u` is `C²` on `Ω` and continuous on `closure Ω`, `Lu>0` on `Ω`, and the maximum value is nonnegative.
  - Follow-on claim: the attained boundary value is nonnegative.
- Lean coverage:
  - `∂Ω` is covered by `frontier Ω`.
  - The nonnegative maximum over `\bar Ω` is covered by `HasNonnegativeMaximumOnClosure Ω u M`.
  - Boundary attainment is covered by `∃ x ∈ frontier Ω, u x = M ∧ 0 ≤ u x`.
  - All operator, coefficient, domain, and regularity assumptions are covered as in the lemma entry.
- Scope changes: representation bridge from source `ℝ^n` to `Fin n → ℝ`; the source theorem’s implicit/ambiguous existence of “its nonnegative maximum” is made explicit through `HasNonnegativeMaximumOnClosure Ω u M`; uniform ellipticity is encoded by a lower quadratic-form bound; no separate proof of compactness-based maximum existence is included in this draft.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: “For any `ε>0`, consider `w(x)=u(x)+ε e^{αx₁}` with `α` to be determined. Then `Lw = Lu + ε e^{αx₁}(a₁₁ α² + b₁ α + c)`. Since `b₁` and `c` are bounded and `a₁₁(x) ≥ λ > 0` for any `x ∈ Ω`, by choosing `α>0` large enough we get `a₁₁(x)α² + b₁(x)α + c(x) > 0` for any `x ∈ Ω`. This implies `Lw > 0` in `Ω`. By the above lemma, `w` attains its nonnegative maximum only on `∂Ω`, that is, `sup_Ω w ≤ sup_{∂Ω} w⁺`. Then `sup_Ω u ≤ sup_Ω w ≤ sup_{∂Ω} w⁺ ≤ sup_{∂Ω} u⁺ + ε sup_{x∈∂Ω} e^{αx₁}`. Finish by letting `ε→0`.”
- Prover notes: the source proof is a perturbation argument with `w = u + ε exp(α x₁)`, choosing `α` using the ellipticity lower bound and boundedness of `b₁,c`. In the current Lean statement with `Lu>0` and an explicit maximum value, a later prover may either follow the perturbation proof or use `no_interior_max_of_Lu_pos` plus topology (`frontier = closure \ interior`, and `IsOpen Ω`) to move an attained closure maximum that is not interior to the boundary. If the independent reviewer wants exact coverage of the source’s supremum/positive-part inequality, add a separate reviewed theorem before proof handoff.

## Handoff Notes

- The two source-backed proof obligations are intentionally left as `by sorry` in `ShadowBench/Source/Main.lean` for the later `/prove` workflow.
- Definition and predicate declarations are implemented without construction stubs.
- Independent statement/source review should decide whether the explicit maximum-value bridge in `main_theorem` is the intended reading of the source theorem or whether an additional compactness/supremum statement is required.
