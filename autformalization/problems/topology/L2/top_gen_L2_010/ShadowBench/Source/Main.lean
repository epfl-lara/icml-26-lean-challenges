import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Operator.Prod

open Bundle Set FiberBundle

noncomputable section

section PullbackVectorBundle

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜]
variable [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} {B' : Type*} [TopologicalSpace B']
variable [TopologicalSpace (TotalSpace F E)]
variable [∀ x : B, AddCommMonoid (E x)] [∀ x : B, Module 𝕜 (E x)]

instance Bundle.Pullback.addCommMonoid (f : B' → B) (x : B') :
    AddCommMonoid ((f *ᵖ E) x) :=
  inferInstanceAs (AddCommMonoid (E (f x)))

instance Bundle.Pullback.module (f : B' → B) (x : B') : Module 𝕜 ((f *ᵖ E) x) :=
  inferInstanceAs (Module 𝕜 (E (f x)))

/--
Source definition (`docs/source.tex`, line 17): the pullback bundle has fiber
`E (f x)` over `x : B'`, with total-space topology making the projection and
lift to the original bundle continuous. In Mathlib this bundle is `(f : B' → B) *ᵖ E`,
with topology and maps supplied by `Mathlib.Topology.FiberBundle.Constructions`.

Prover notes: for a local trivialization `e`, the pulled-back trivialization
`e.pullback f` acts on each fiber by the same linear map as `e` at `f x`, so
fiberwise linearity is inherited directly from `e.linear`.
-/
instance Bundle.Trivialization.pullback_linear (e : Trivialization F (π F E))
    [e.IsLinear 𝕜] (f : C(B', B)) : (e.pullback f).IsLinear 𝕜 where
  linear _ h := e.linear 𝕜 h

/--
Source theorem (`docs/source.tex`, line 25): a vector bundle pulled back along a
continuous map is again a vector bundle over the pullback base.

Source proof: the fiber of the pullback over `x` is the original fiber over
`f x`; local trivializations pull back over preimages of their base sets; their
fiber restrictions remain linear isomorphisms; and pullback transition maps are
`g_{UV} ∘ f`, hence continuous because both `g_{UV}` and `f` are continuous.

Prover notes: use `FiberBundle.pullback` for the pullback atlas. Atlas members
are `e.pullback f`; linearity follows from `Bundle.Trivialization.pullback_linear`.
For coordinate changes, reduce `(e.pullback f).coordChangeL 𝕜 (e'.pullback f) b`
to `e.coordChangeL 𝕜 e' (f b)` and compose the original `continuousOn_coordChange`
with `f.continuous`.
-/
theorem VectorBundle.pullback [∀ x : B, TopologicalSpace (E x)] [FiberBundle F E]
    [VectorBundle 𝕜 F E] (f : C(B', B)) :
    VectorBundle 𝕜 F ((f : B' → B) *ᵖ E) := by
  sorry

end PullbackVectorBundle
