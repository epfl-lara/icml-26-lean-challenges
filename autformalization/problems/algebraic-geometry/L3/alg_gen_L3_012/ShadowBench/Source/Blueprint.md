# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_012`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Documents Read

- `docs/source.tex`: inspected with `formalization_document_inspect`; source has one named definition and one named theorem.
- `.epflemma/workflow-state/formalization/docs-source/manifest.json`: preflight manifest read; no bibliography, references, labels, figures, PDFs, or support files requiring PDF extraction were listed. Project file search found no local `*.pdf`, so no `read_pdf` target was available.
- `.epflemma/workflow-state/formalization/docs-source/context.md`: workflow contract and extracted source map read.
- `docs/instructions.md`: required names and import discipline read.
- `docs/skeletons/README.md` and `docs/skeletons/Skeleton{1,2,3,4}.lean`: candidate skeletons read and compared against the source.

## Import Plan

```lean
import Mathlib
```

## Suggested Search Modules

- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` for `AlgebraicGeometry.LocallyOfFinitePresentation` and `locallyOfFinitePresentation_iff`.
- `Mathlib.AlgebraicGeometry.Over` for schemes over a base, `Over.mk`, and overcategory notation.
- `Mathlib.AlgebraicGeometry.AffineScheme` for `AlgebraicGeometry.IsAffine`.
- `Mathlib.CategoryTheory.Limits.Preserves.Filtered` and `Mathlib.CategoryTheory.Limits.Opposites` for filtered colimits and opposite-category limit/colimit translations.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed definition `functorOfPointsOver` and theorem skeleton `locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving`.
- Root coverage: `ShadowBench.lean` imports `ShadowBench.Source`, and `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`, so project-level `lake build`/`lean_verify(mode=project)` covers the generated file.
- No split into auxiliary files is used at this draft stage; one file best preserves the short source context.

## Required Names

- `functorOfPointsOver`
- `locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving`

## Local/Mathlib Search Summary

- Search found `AlgebraicGeometry.LocallyOfFinitePresentation` in `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, matching the source's locally finite presentation property for scheme morphisms.
- Search found `AlgebraicGeometry.locallyOfFinitePresentation_iff`, the affine-open characterization used by the first half of the source proof.
- Search found `AlgebraicGeometry.Scheme.Over`, `Over.mk`, and `AlgebraicGeometry.Scheme.asOver`, matching `Sch/S` as Lean's overcategory `Over S`.
- Search found `AlgebraicGeometry.IsAffine`, matching the source restriction to affine schemes in the inverse system.
- Search found `CategoryTheory.Limits.PreservesColimit` and `PreservesFilteredColimits`, giving a categorical formulation of the equality `F(T) = colim_i F(T_i)`.

## Skeleton Review

- `Skeleton1.lean`: rejected as a direct draft because it uses non-existent or ill-typed names such as `Schemes_over`, `AffineSite`, `Colim`, and proof-omission terms inside a definition. It did identify the expected theorem shape.
- `Skeleton2.lean`: same issues as Skeleton1 and adds an unusable proof-omitted construction stub for `functorOfPointsOver`, which is not acceptable for a definition handoff.
- `Skeleton3.lean`: same ill-typed categorical encoding and unacceptable construction stubs.
- `Skeleton4.lean`: syntactically malformed theorem stub and an incorrect theorem-style `functorOfPointsOver : True`; rejected.
- Adopted from skeletons: only the required names, the broad idea that the theorem compares `LocallyOfFinitePresentation f` with a limit-preservation property of a functor of points, and the starting import `Mathlib`.

## Source Statement Inventory

Source inventory entries covered in this plan:

- `line-17`: Definition `[functorOfPointsOver]`, Lean declaration `functorOfPointsOver`.
- `line-20`: Theorem `[locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving]`, Lean declaration `locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving`.

### line-17

Source inventory entry `line-17`.

- Source inventory entry: `line-17`
- Source label: `line-17`.
- Kind: definition.
- Source locator: `docs/source.tex`, `line-17`, lines 17-19.
- Source statement: Let `S` be a scheme. A functor `F : (Sch/S)^opp -> Sets` is limit preserving if for every directed inverse system `{T_i}_{i in I}` of affine schemes with limit `T`, one has `F(T) = colim_i F(T_i)`.
- Planned Lean declaration: `functorOfPointsOver`.
- Lean statement:
  ```lean
  def functorOfPointsOver {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) : Prop :=
    ∀ (J : Type u) [SmallCategory J] [IsFiltered J] (T : Jᵒᵖ ⥤ Over S) [HasLimit T],
      (∀ j : Jᵒᵖ, IsAffine (T.obj j).left) →
        PreservesColimit T.op F
  ```
- Dependencies: `CategoryTheory.Over`, `CategoryTheory.Limits.PreservesColimit`, `CategoryTheory.IsFiltered`, `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.IsAffine`.
- Skeleton candidate used: no skeleton copied; candidate files were used only to confirm the required name and high-level intent.
- Formal statement review: `Over S` formalizes `Sch/S`; `(Over S)ᵒᵖ ⥤ Type u` formalizes set-valued functors on the opposite overcategory; `T : Jᵒᵖ ⥤ Over S` with `J` filtered formalizes an inverse system indexed by a directed/filtered category; `[HasLimit T]` records the existence of the limit object; `IsAffine (T.obj j).left` records that each source scheme is affine; `PreservesColimit T.op F` is the categorical version of the comparison map `colim_i F(T_i) -> F(lim_i T_i)` being an isomorphism.
- Source qualifiers:
  - Base scheme `S` is explicit.
  - Functor domain is `(Sch/S)^opp`; Lean uses `(Over S)ᵒᵖ`.
  - Functor codomain is `Sets`; Lean uses `Type u` as Mathlib's type-valued set model.
  - The inverse system is directed and inverse; Lean uses a filtered category `J` and a diagram `Jᵒᵖ ⥤ Over S`.
  - Every object in the system is affine; Lean requires `IsAffine (T.obj j).left`.
  - The system has a limit; Lean includes `[HasLimit T]`.
  - The equality with a colimit is expressed categorically as preservation of the corresponding colimit in the opposite category.
- Lean coverage: covers the source base scheme, overcategory domain, set-valued codomain, inverse filtered affine systems, existence of the limit object, and the comparison `F(lim T_i) ≅ colim_i F(T_i)` through `PreservesColimit T.op F`. `Over S` is the explicit representation bridge for `Sch/S`; `Type u` is the Mathlib model for `Sets`.
- Scope changes: directed preorders are generalized to filtered small categories. This is an intentional categorical strengthening of the indexing language, not an omission of any source case. The Lean declaration is restricted to systems in the overcategory `Over S`, matching the source domain `(Sch/S)^opp`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: no source proof is attached to this definition. Provers should unfold the definition and use opposite-category limit/colimit preservation lemmas when connecting it to explicit morphism-set colimits.

### line-20

Source inventory entry `line-20`.

- Source inventory entry: `line-20`
- Source label: `line-20`.
- Kind: theorem.
- Source locator: `docs/source.tex`, `line-20`, theorem lines 20-22; proof lines 22-59.
- Source statement: Let `f : X -> S` be a morphism of schemes. Then `f` is locally of finite presentation if and only if the functor of points `h_X` of `X` is limit preserving.
- Planned Lean declaration: `locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving`.
- Lean statement:
  ```lean
  theorem locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving
      {X S : Scheme.{u}} (f : X ⟶ S) :
      LocallyOfFinitePresentation f ↔
        functorOfPointsOver (yoneda.obj (Over.mk f))
  ```
- Dependencies: `functorOfPointsOver`, `AlgebraicGeometry.LocallyOfFinitePresentation`, `CategoryTheory.yoneda`, `Over.mk`.
- Skeleton candidate used: the skeletons suggested a theorem comparing locally finite presentation with limit preservation of a functor of points, but their concrete Lean names were not type-correct. The final statement uses Mathlib's `LocallyOfFinitePresentation f`, `Over.mk f`, and `yoneda.obj (Over.mk f)`.
- Formal statement review: `f : X ⟶ S` exactly represents a morphism of schemes. `LocallyOfFinitePresentation f` is Mathlib's locally finite presentation property for scheme morphisms. The functor of points of `X` over `S` is represented by the Yoneda functor on the object `Over.mk f : Over S`, namely `yoneda.obj (Over.mk f) : (Over S)ᵒᵖ ⥤ Type u`; this sends an `S`-scheme `T` to morphisms `T -> X` over `S`, matching `h_X(T)`. `functorOfPointsOver` then asserts the source's limit-preservation property.
- Source qualifiers:
  - Quantifies over schemes `X` and `S` and a morphism `f : X -> S`; Lean has `{X S : Scheme.{u}} (f : X ⟶ S)`.
  - Left side is locally of finite presentation; Lean uses `LocallyOfFinitePresentation f`.
  - Right side is the functor of points of `X` over `S`; Lean uses the representable overcategory functor `yoneda.obj (Over.mk f)`.
  - Limit preservation is the `line-17` definition.
  - The theorem is an iff with no extra side conditions, matching the source.
- Lean coverage: covers the quantifiers over schemes `X`, `S`, and a morphism `f : X ⟶ S`; covers the left side by `LocallyOfFinitePresentation f`; covers the right side by applying the `line-17` definition `functorOfPointsOver` to the explicit overcategory representable functor `yoneda.obj (Over.mk f)`.
- Scope changes: no theorem-side assumptions were added or removed. The right side uses Yoneda in `Over S` as the explicit representation bridge for the source notation `h_X`; the indexing and `Sets`/`Type u` conventions are exactly those recorded for `line-17`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:
  ```text
  First, assume that $h_X$ is limit preserving. Choose any affine opens $U \subset X$ and $V\subset S $ such that $f(U) \subset V$. We have to show that $\mathcal{O}_S(V) \to \mathcal{O}_X(U)$ is of finite presentation. Let $(A_i, \varphi_{ii'})$ be a directed system of $\mathcal{O}_S(V)$-algebras. Set $A=\mathrm{colim}_i A_i$. We have to show that
  \[
      \mathrm{Hom}_{\mathcal{O}_S(V)} (\mathcal{O}_X(U),A) = \mathrm{colim}_i\mathrm{Hom}_{\mathcal{O}_S(V)}(\mathcal{O}_X(U),A_i)
  \]
  Consider the schemes $T_i=\mathrm{Spec}(A_i)$. They form an inverse system of $V$-schemes over $I$ with transition morphisms $f_{ii'}:T_i \to T_{i'}$ induced by the $\mathcal{O}_S(V)$-algebra maps $\varphi_{i'i}$. Set $T:=\mathrm{Spec}(A)=\mathrm{lim}_i T_i$. The formula above becomes in terms of morphism sets of schemes
  \[
      \mathrm{Mor}_V(\mathrm{lim}_i T_i,U) = \mathrm{colim}_i \mathrm{Mor}_V (T_i,U).
  \]
  We first observe that $\mathrm{Mor}_V(T_i,U)=\mathrm{Mor}_S(T_i,U)$ and $\mathrm{Mor}_V(T,U)=\mathrm{Mor}_S(T,U)$. Hence we have to show that
  \[
      \mathrm{Mor}_S(\mathrm{lim}_i T_i,U) = \mathrm{colim}_i \mathrm{Mor}_S(T_i,U)
  \]
  and we are given that
  \[
      \mathrm{Mor}_S(\mathrm{lim}_i T_i,X) = \mathrm{colim}_i \mathrm{Mor}_S(T_i,X).
  \]
  Hence it suffices to prove that given a morphism $g_i:T_i \to X$ over $S$ such that the composition $T \to T_i \to X$ ends up in $U$ there exists some $i' \ge i$ such that the composition $g_{i'}:T_{i'} \to T_i \to X$ ends up in $U$. Denote $Z_{i'}= g_{i'}^{-1}(X \setminus U)$. Assume each $Z_{i'}$ is nonempty to get a contradiction. Note that there exists a point $t$ of $T$ which is mapped into $Z_{i'}$ for all $i' \ge i$. Such a point is not mapped into $U$. A contradiction.

  Now assume that $f$ is locally of finite presentation. Let an inverse directed system $(T_i,f_{ii'})$ of $S$-schemes with each $T_i$ affine be given. Since each $T_i$ is affine, the morphisms $f_{ii'}$ are affine and each $T_i$ is quasi-compact and quasi-separated as a scheme. Let $T=\mathrm{lim}_i T_i$. Denote $f_i:T \to T_i$ the projection morphisms. We have to show:
  \begin{enumerate}[label=(\alph*)]
      \item Given morphisms $g_i,g_i':T_i \to X$ over $S$ such that $g_i \circ f_i=g_i' \circ f_i$, then there exists an $i' \ge i$ such that $g_i\circ f_{i'i}=g_i' \circ f_{i'i}$.
      \item Given any morphism $g:T \to X$ over $S$ there exists an $i \in I$ and a morphism $g_i:T_i \to X$ such that $g=f_i \circ g_i$.
  \end{enumerate}

  First let us prove the uniqueness part (a). Let $g_i,g_i':T_i \to X$ be morphisms such that $g_i \circ f_i=g_i' \circ f_i$. For any $i' \ge i$ we set $g_i' = g_i \circ f_{i' i}$ and $g_{i'}'=g_i' \circ f_{i'i}$. We also set $g=g_i \circ f_i=g_i' \circ f_i$. Consider the morphism $(g_i,g_i'):T_i \to X \times_S X$. Set
  \[
      W = \bigcup \nolimits _{U \subset X \text{ affine open}, V \subset S \text{ affine open}, f(U) \subset V} U \times_V U.
  \]
  This is an open in $X \times_S X$, with the property that the morphism $\Delta_{X/S}$ factors through a closed immersion into $W$. Note that the composition $(g_i,g_i') \circ f_i:T \to X \times_S X$ is a morphism into $W$ because it factors through the diagonal by assumption. Set $Z_{i'}=(g_{i'},g_{i'}')^{-1}(X \times_S X \setminus W)$. If each $Z_{i'}$ is nonempty, then there exists a point $t \in T$ which maps to $Z_{i'}$ for all $i' \ge i$. This is a contradiction with the fact that $T$ maps into $W$. Hence we may increase $i$ and assume that $(g_i,g_i'):T_i \to X \times_S X$ is a morphism into $W$. By construction of $W$, and since $T_i$ is quasi-compact we can find a finite affine open covering $T_i=T_{1,i} \cup \dots \cup T_{n,i}$ such that $(g_i,g_i')|_{T_{j,i}}$ is a morphism into $U \times_V U$ for some pair $(U,V)$ as in the definition of $W$ above. Since it suffices to prove that $g_{i'}$ and $g_{i'}'$ agree on each of the $f_{i'i}^{-1}(T_{j,i})$ this reduces us to the affine case. The affine case follows from the fact that the ring map $\mathcal{O}_S(V) \to \mathcal{O}_X(U)$ is of finite presentation.

  Finally, we prove the existence part (b). Let $g:T \to X$ be a morphism of schemes over $S$. We can find a finite affine open covering $T=W_1 \cup \dots \cup W_n$ such that for each $j \in \{1,\dots,n\}$ there exist affine opens $U_j \subset X$ and $V_j \subset S$ with $f(U_j) \subset V_j$ and $g(W_j) \subset U_j$. After possibly shrinking $I$, we may assume that there exist affine open coverings $T_i=W_{1,i} \cup \dots \cup W_{n,i}$ compatible with transition maps such that $W_j=\mathrm{lim}_i W_{j,i}$. Since $\mathcal{O}_S(V_j) \to \mathcal{O}_X(U_j)$ is of finite presentation, we can find for each $j$ an index $i_j \in I$ and a morphism $g_{j,i_j}:W_{j,i_j} \to X$ such that $g_{j,i_j}\circ f_i|_{W_j}:W_j \to W_{j,i} \to X$ equals $g|_{W_j}$. By part (a) proved above, using the quasi-compactness of $W_{j_1,i} \cap W_{j_2,i}$ which follows as $T_i$ is quasi-separated, we can find an index $i' \in I$ larger than all $i_j$ such that
  \[
      g_{j_1,i_{j_1}} \circ f_{i' i_{j_1}} |_{W_{j_1,i'} \cap W_{j_2,i'}} = g_{j_2,i_{j_2}} \circ f_{i' i_{j_2}} |_{W_{j_1,i'} \cap W_{j_2,i'}}
  \]
  for all $j_1,j_2 \in \{1,\dots,n\}$. Hence the morphisms $g_{j,i_j} \circ f_{i' i_j}|_{W_{j,i'}}$ glue to give the desired morphism $T_{i'} \to X$.
  ```
- Proof sketch for Lean doc comment: reduce the forward implication using `locallyOfFinitePresentation_iff` on affine opens and translate finite presentation of affine coordinate rings into preservation of morphism sets along affine inverse limits; for the reverse implication, prove injectivity and surjectivity of the colimit comparison for `yoneda.obj (Over.mk f)`: uniqueness via the open `W = union U ×_V U` around the diagonal, noetherian-style nonempty inverse-closed contradiction, finite affine reduction, and finite presentation; existence by finite affine covers of the limit, descent of local maps using finite presentation, uniqueness on overlaps, and gluing.
- Prover notes:
  - Start by unfolding `functorOfPointsOver` and the overcategory Yoneda functor.
  - Use the affine-open characterization `AlgebraicGeometry.locallyOfFinitePresentation_iff` for the forward direction.
  - Expect missing Mathlib infrastructure for the full Stacks-style inverse-limit argument; helper lemmas may be needed for converting affine filtered colimits of rings into limits of affine schemes and for the topological point compactness argument used to force eventual containment in an open subset.
  - Keep the representation bridge `yoneda.obj (Over.mk f)` unchanged unless an independent statement/source review requests a different functor-of-points encoding.

## Statement/Source Verification Gate

- Source document and manifest were read.
- Local project facts and Mathlib names were searched before drafting.
- Blueprint source inventory contains entries for `line-17` and `line-20`.
- Definition construction gaps avoided: `functorOfPointsOver` is implemented as a Prop, not as an omitted-proof construction.
- The theorem proof is intentionally omitted for a later explicit `/prove` workflow after statement/source review.
- Root module imports already cover `ShadowBench.Source.Main`.
- Independent statement/source verification has not yet approved the inventory entries; this formalizer pass does not self-approve them.
- Proof-ready handoff remains unmarked until independent review accepts the source map and Lean statements.
