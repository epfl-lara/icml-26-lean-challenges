# Formalization Blueprint: `algebraic-geometry/L4/alg_sche_L4_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Import Plan

Direct Lean imports used by `ShadowBench/Source/Main.lean`:

```lean
import Mathlib
```

## Suggested Search Modules

Non-gating search hints for the prover/reviewer:

- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.AlgebraicGeometry.PullbackCarrier`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the projective-space bridge definitions, the projective morphism predicate used for this document, and the source theorem `prod_projective` with a `by sorry` proof skeleton.
- Root coverage: `ShadowBench.lean` imports `ShadowBench.Source`; `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`, so project-level verification covers the generated target module.

## Search and Library Notes

- Candidate skeletons all proposed the required theorem name `prod_projective` and the informal shape “projective over `S` is closed under fiber products.”
- The skeleton type `IsProjective S X` is not a Mathlib scheme predicate in this project; local/Mathlib search found projectivity for modules and measure families, but no built-in `AlgebraicGeometry.IsProjective` morphism property for schemes.
- Mathlib does provide `Scheme`, categorical pullbacks of schemes, `IsClosedImmersion`, and `Proj` for graded rings. The draft therefore implements a source-faithful bridge predicate `AlgebraicGeometry.IsProjective f` as existence of a closed immersion into a relative projective space over the target.
- Relative projective space is represented as the base change of `Proj` of the standard graded polynomial ring over `ℤ` with `n + 1` homogeneous coordinates. This is sufficient to state the source theorem without adding axioms or construction stubs.

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`: supplies the required name but omits the structure morphisms `X ⟶ S`, `Y ⟶ S`; also uses a non-existing binary predicate `IsProjective S X` and informal notation `X ×_S Y`.
- `docs/skeletons/Skeleton2.lean`: same statement shape as Skeleton1; useful only for the name and high-level theorem shape.
- `docs/skeletons/Skeleton3.lean`: same statement shape as Skeleton1; useful only for the name and high-level theorem shape.
- `docs/skeletons/Skeleton4.lean`: contains the same candidate plus an extra malformed `:= by sorry`; not adopted.
- Adopted choice: preserve the theorem name `prod_projective`, but redraft the statement with explicit morphisms `f : X ⟶ S` and `g : Y ⟶ S` and the Lean pullback `Limits.pullback f g`.

## Local Definitions and Bridges

### `AlgebraicGeometry.standardProjectiveSpace`

- Kind: definition.
- Source role: bridge for projective spaces `\mathbb{P}^n` appearing in the source proof.
- Lean meaning: `Proj` of the standard graded polynomial ring over `ULift ℤ` in `n + 1` variables.
- Construction status: implemented in `Main.lean`; no proof obligation.

### `AlgebraicGeometry.projectiveSpace`

- Kind: definition.
- Source role: bridge for relative projective spaces `\mathbb{P}^n_S`.
- Lean meaning: base change of `standardProjectiveSpace n` along the terminal morphism from `S`.
- Construction status: implemented in `Main.lean`; no proof obligation.

### `AlgebraicGeometry.projectiveSpaceToBase`

- Kind: definition.
- Source role: structural morphism `\mathbb{P}^n_S \to S`.
- Lean meaning: the first projection from the above pullback.
- Construction status: implemented in `Main.lean`; no proof obligation.

### `AlgebraicGeometry.IsProjective`

- Kind: definition.
- Source role: formalizes “projective over `S`” for a morphism `f : X ⟶ S`.
- Lean meaning: there exists `n : ℕ` and a closed immersion `X ⟶ projectiveSpace n S` whose composition with `projectiveSpaceToBase n S` is `f`.
- Construction status: implemented in `Main.lean`; no proof obligation.
- Fidelity note: this matches the standard definition of a projective morphism used by the source theorem. The bridge is local because the current Mathlib import set does not expose a built-in scheme-projectivity predicate.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source title: theorem `prod_projective`.
- Planned Lean declaration: `prod_projective`
- Source locator: `docs/source.tex`, theorem lines 17-19; proof lines 21-114.
- Source statement: “Let `S` be a scheme. The fiber product `X ×_S Y` of two projective `S`-schemes is again projective over `S`.”
- Lean statement:

```lean
theorem prod_projective {S X Y : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    (hX : AlgebraicGeometry.IsProjective f) (hY : AlgebraicGeometry.IsProjective g) :
    AlgebraicGeometry.IsProjective (CategoryTheory.Limits.pullback.fst f g ≫ f) := by
  sorry
```

- Dependencies: `Scheme`, `CategoryTheory.Limits.pullback`, `CategoryTheory.Limits.pullback.fst`, categorical composition, `AlgebraicGeometry.projectiveSpace`, `AlgebraicGeometry.projectiveSpaceToBase`, `AlgebraicGeometry.IsProjective`, and `IsClosedImmersion`.
- Formal statement review:
  - The source phrase “projective `S`-scheme” is encoded as a scheme equipped with an explicit structure morphism to `S` satisfying `AlgebraicGeometry.IsProjective`.
  - The source fiber product `X ×_S Y` is encoded as `CategoryTheory.Limits.pullback f g`.
  - The resulting object is asserted projective over `S` via the structure morphism `pullback.fst f g ≫ f`; by the pullback condition this agrees with `pullback.snd f g ≫ g`.
  - The statement does not assert the Segre embedding or its quadratic image equations as separate conclusions; those are proof ingredients in the source proof and are recorded below as prover notes.
- Source qualifiers:
  - Mathematical object class: schemes and morphisms of schemes.
  - Quantifier order: first schemes `S`, `X`, `Y`; then structure morphisms `f : X ⟶ S`, `g : Y ⟶ S`; then projectivity assumptions for those morphisms.
  - Parameter domain: arbitrary schemes in Mathlib’s `Scheme` category.
  - Output codomain: a proposition that the fiber-product structure morphism to `S` is projective.
  - Equality/image condition in statement: none beyond the categorical fiber-product structure; the equality of the two projections to `S` is implicit in `pullback.condition`.
  - Side conditions: `hX : IsProjective f` and `hY : IsProjective g`.
  - Follow-on claims: the Segre embedding and quadratic rank-one image equations occur in the proof, not as separate theorem conclusions.
- Lean coverage:
  - The object-class qualifier is covered by `S X Y : Scheme` and explicit morphisms `f`, `g`.
  - The projective-over-`S` qualifier is covered by `AlgebraicGeometry.IsProjective f` and `AlgebraicGeometry.IsProjective g`.
  - The fiber product is covered by `CategoryTheory.Limits.pullback f g` through the domain of `pullback.fst f g ≫ f`.
  - The conclusion “again projective over `S`” is covered by `AlgebraicGeometry.IsProjective (pullback.fst f g ≫ f)`.
- Scope changes:
  - No intentional weakening or strengthening of the theorem statement.
  - Representation bridge: the draft introduces a local `AlgebraicGeometry.IsProjective` predicate because Mathlib does not currently expose a scheme-projectivity predicate matching the skeleton. This bridge is definitionally tied to closed immersions into relative projective spaces constructed from `Proj`, rather than an unconstrained abstract predicate.
  - The proof’s explicit Segre morphism and rank-one quadratic equations are not separately formalized as named lemmas in the planner draft; they are intended proof steps for the later prover queue.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof text (verbatim from `docs/source.tex`, lines 21-113):

```text
It suffices to consider the case where $X, Y$ are both projective spaces over $S$. 
Write homogeneous coordinates on $\mathbb{P}^n_S$ as
\[
[x_0:\cdots:x_n]
\]
and on $\mathbb{P}^m_S$ as
\[
[y_0:\cdots:y_m].
\]
Define a morphism
\[
\sigma : \mathbb{P}^n_S \times_S \mathbb{P}^m_S \to \mathbb{P}^{(n+1)(m+1)-1}_S
\]
by
\[
([x_0:\cdots:x_n],[y_0:\cdots:y_m])
\longmapsto
[x_i y_j]_{0 \le i \le n,\ 0 \le j \le m},
\]
where the target coordinates are indexed by the pairs $(i,j)$.

We claim that this is a closed immersion whose image is cut out by the quadratic equations
\[
z_{ij} z_{i'j'} = z_{ij'} z_{i'j}
\qquad
(0 \le i,i' \le n,\ 0 \le j,j' \le m).
\]
Indeed, if $z_{ij} = x_i y_j$, then
\[
z_{ij} z_{i'j'} = (x_i y_j)(x_{i'} y_{j'}) = (x_i y_{j'})(x_{i'} y_j) = z_{ij'} z_{i'j},
\]
so every point in the image satisfies these equations.

Conversely, suppose a point
\[
[z_{ij}] \in \mathbb{P}^{(n+1)(m+1)-1}_S
\]
satisfies all these quadratic relations. These equations say exactly that the matrix $(z_{ij})$ has rank at most $1$. Since the point is projective, not all $z_{ij}$ vanish, so the matrix has rank exactly $1$. Hence, locally on $S$, one may write
\[
z_{ij} = x_i y_j
\]
for suitable homogeneous coordinates $[x_0:\cdots:x_n] \in \mathbb{P}^n_S$ and $[y_0:\cdots:y_m] \in \mathbb{P}^m_S$. This shows that the image of $\sigma$ is precisely the closed subscheme defined by the above equations.

To see that $\sigma$ is a closed immersion, it suffices to check on the standard affine opens. Let
\[
U_i = D_+(x_i) \subset \mathbb{P}^n_S, \qquad
V_j = D_+(y_j) \subset \mathbb{P}^m_S.
\]
Then
\[
U_i \times_S V_j
\]
is affine, and on this open the morphism $\sigma$ identifies it with the affine open
\[
D_+(z_{ij})
\]
inside the closed subscheme cut out by the above quadratic equations. On coordinate rings, this map is given by
\[
\mathcal{O}_S\!\left[\frac{x_k}{x_i}, \frac{y_\ell}{y_j}\right]
\longrightarrow
\mathcal{O}_S\!\left[\frac{z_{k\ell}}{z_{ij}}\right]/(z_{k\ell}z_{ij}-z_{kj}z_{i\ell}),
\]
and the relations imply
\[
\frac{z_{k\ell}}{z_{ij}}=
\frac{z_{kj}}{z_{ij}}\cdot \frac{z_{i\ell}}{z_{ij}}.
\]
Thus the coordinate ring of the image is generated by the ratios
\[
\frac{z_{kj}}{z_{ij}}, \qquad \frac{z_{i\ell}}{z_{ij}},
\]
which correspond exactly to
\[
\frac{x_k}{x_i}, \qquad \frac{y_\ell}{y_j}.
\]
Hence this map on coordinate rings is an isomorphism. Therefore $\sigma$ is a closed immersion.

It follows that
\[
\mathbb{P}^n_S \times_S \mathbb{P}^m_S
\]
admits a closed immersion into a projective space over $S$, so it is projective over $S$.

Finally, if $X \to S$ and $Y \to S$ are projective morphisms, choose closed immersions
\[
X \hookrightarrow \mathbb{P}^n_S, \qquad Y \hookrightarrow \mathbb{P}^m_S.
\]
Then
\[
X \times_S Y \hookrightarrow \mathbb{P}^n_S \times_S \mathbb{P}^m_S
\]
is a closed immersion, and by the Segre embedding the latter admits a closed immersion into a projective space over $S$. Hence $X \times_S Y$ is projective over $S$.
```

- Prover notes:
  - Unpack `AlgebraicGeometry.IsProjective` for `hX` and `hY` to obtain closed immersions into relative projective spaces.
  - Construct or locate a Segre closed immersion from `projectiveSpace n S ×_S projectiveSpace m S` to `projectiveSpace ((n+1)*(m+1)-1) S`.
  - Use stability of closed immersions under pullback/product to get a closed immersion from `Limits.pullback f g` into the product of the two projective spaces.
  - Compose closed immersions and use the defining existential of `AlgebraicGeometry.IsProjective`.

## Review Gate

- Draft Lean declarations are intended to compile with one theorem `sorry` for `prod_projective`.
- Independent statement/source verification must review the local projectivity bridge, the explicit structure morphisms, and the choice of `pullback.fst f g ≫ f` as the fiber-product map to `S` before any proof workflow starts.
- Suggested prover command after review approval: `/prove ShadowBench/Source/Main.lean prod_projective`.
