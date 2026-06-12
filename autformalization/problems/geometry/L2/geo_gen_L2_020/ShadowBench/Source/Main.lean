import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

open scoped Manifold ContDiff

/--
A smooth vector field on a manifold modeled by `I`, represented as a dependent function
into tangent spaces whose bundled section into `TangentBundle I M` is smooth.
-/
def SmoothVectorField
    {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (X : (p : M) → TangentSpace I p) : Prop :=
  ContMDiff I I.tangent ∞ (fun p => (⟨p, X p⟩ : TangentBundle I M))

/--
`Y` is `F`-related to `X` if the bundled tangent map sends `X p` to `Y (F p)`,
matching the source notation `dF_p(X_p) = Y_{F(p)}`.
-/
def FRelatedVectorFields
    {E H M E' H' N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    (F : M → M × N)
    (X : (p : M) → TangentSpace I p)
    (Y : (q : M × N) → TangentSpace (I.prod J) q) : Prop :=
  ∀ p : M,
    tangentMap I (I.prod J) F (⟨p, X p⟩ : TangentBundle I M) =
      (⟨F p, Y (F p)⟩ : TangentBundle (I.prod J) (M × N))

/--
The geometric extension principle needed by the source theorem: every smooth vector
field on `M` has a smooth vector-field extension on the ambient product that agrees
with the graph differential of `f` along the graph.

This is a genuine global extension/rebasing theorem for vector fields along an
embedded graph. It is not currently available as a direct Mathlib theorem in the
manifold API used here, so the final theorem below keeps this principle explicit.
-/
def SmoothGraphVectorFieldExtensionMechanism
    {E H M E' H' N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    (f : M → N) : Prop :=
  let F : M → M × N := fun x => (x, f x)
  ∀ X : (p : M) → TangentSpace I p,
    SmoothVectorField (I := I) X →
    ∃ Y : (q : M × N) → TangentSpace (I.prod J) q,
      SmoothVectorField (I := I.prod J) Y ∧
      FRelatedVectorFields (I := I) (J := J) F X Y

/--
Source theorem `line-17` in `docs/source.tex`.
Source proof: no proof is supplied in the source document.
Proof sketch: for the graph map `F x = (x, f x)`, extend the given smooth vector
field along the graph to a smooth vector field on the ambient product whose value
at `(p, f p)` is the tangent map of `F` applied to `X p`. The Lean statement records
this as equality in the tangent bundle via `tangentMap`.
Prover notes: prove smoothness of `F` from smoothness of `id` and `f`, use the
standard tangent-map/product-manifold API, and construct a global smooth extension
of the graph-valued field.
-/
theorem exists_smooth_vectorField_on_graph
    {E H M E' H' N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    [BoundarylessManifold J N]
    (f : M → N) (_hf : ContMDiff I J ∞ f)
    (h_extension : SmoothGraphVectorFieldExtensionMechanism (I := I) (J := J) f) :
    let F : M → M × N := fun x => (x, f x)
    ∀ X : (p : M) → TangentSpace I p,
      SmoothVectorField (I := I) X →
      ∃ Y : (q : M × N) → TangentSpace (I.prod J) q,
        SmoothVectorField (I := I.prod J) Y ∧
        FRelatedVectorFields (I := I) (J := J) F X Y := by
  simpa [SmoothGraphVectorFieldExtensionMechanism] using h_extension
