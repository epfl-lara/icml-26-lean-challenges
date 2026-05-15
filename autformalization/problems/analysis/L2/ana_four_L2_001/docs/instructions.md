# ShadowBench Instructions: `analysis/L2/ana_four_L2_001`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Fourier.Notation
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
```

## Expected Declaration Names

- `fourierIntegral`
- `fourierIntegral_const_smul`

## Formalization Rules

```text
open MeasureTheory Filter
open scoped Topology

/-
Formalize in Lean the following named items from Text.

1. Definition (fourierIntegral)
   The definition must be named `fourierIntegral`.
   Matched text (candidate 0, theorem): \begin{theorem} Let $K$ be a commutative ring and let $V, W$ be modules over $K$. Let $E$ be
                                        a complete normed $\mathbb{C}$-vector space, $\mu$ be a measure on $V$, $L : V \times W \to
                                        K$ a bilinear form, and let $e : K \to \mathbb{S}$ be an additive character. For a function
                                        $f : V \to E$, its Fourier transform is defined: \[ \widehat{f}_{e,\mu,L}(w) \;:=\; \int_V
                                        e\!\bigl(-L(v,w)\bigr)\, f(v)\, d\mu(v), \qquad w \…
2. Theorem (fourierIntegral_const_smul)
   The theorem must be named `fourierIntegral_const_smul`.
   Matched text (candidate 1, theorem, label=fourierIntegral_const_smul): \begin{theorem}[fourierIntegral_const_smul] Let $r \in \mathbb{C}$. Then $ \mathcal
                                                                          F_{e,\mu,L}(r \cdot f) \;=\; r \cdot \widehat{f}_{e,\mu,L}. $ \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
