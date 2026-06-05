# Formalization Blueprint: `topology/L2/top_gen_L2_018`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Documents and Support Files

- Primary LaTeX source: `docs/source.tex`.
- Companion instructions: `docs/instructions.md`.
- Candidate skeletons inspected: `docs/skeletons/Skeleton1.lean`, `docs/skeletons/Skeleton2.lean`, `docs/skeletons/Skeleton3.lean`, `docs/skeletons/Skeleton4.lean`.
- Formalization manifest: `.epflemma/workflow-state/formalization/docs-source/manifest.json`.
- Extracted text cache: `.epflemma/workflow-state/formalization/docs-source/extracted.txt`.
- Nearby PDFs, figures, bibliography files: none listed by the manifest.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single generated Lean file for the two required named source entries.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the default Lake target covers the generated file.

## Import Plan

Direct imports used by `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.Topology.Sheaves.Flasque
```

`Mathlib.Topology.Sheaves.Flasque` is the direct Mathlib module containing the formal definitions and results for flasque presheaves/sheaves. It transitively imports the starting modules listed in `docs/instructions.md` (`EpiMono`, `AddCommGrpCat`, and `LocallySurjective`).

## Suggested Search Modules

These are search/prover hints only, not direct imports unless a later proof pass needs them:

- `Mathlib.Topology.Sheaves.Flasque`
- `Mathlib.Topology.Sheaves.LocallySurjective`
- `Mathlib.Topology.Sheaves.AddCommGrpCat`
- `Mathlib.CategoryTheory.Sites.EpiMono`

## Required Names

- `epi_of_shortExact`
- `of_shortExact_of_isFlasque`

## Detected Theorem-Like Blocks

1. `line-17` (theorem, lines 17--26) - `epi_of_shortExact`; proof environment lines 28--129.
2. `thm:quotient-flasque` (theorem, lines 131--138) - `of_shortExact_of_isFlasque`; proof environment lines 140--163.

## Source Map

- line-17 -> `epi_of_shortExact` (`docs/source.tex` lines 17--26; proof environment lines 28--129)
- thm:quotient-flasque -> `of_shortExact_of_isFlasque` (`docs/source.tex` lines 131--138; proof environment lines 140--163)

## Compact Source Map Summary

The full reviewed source inventory is the `## Source Statement Inventory` section below. It contains the declaration names, source locators, source qualifiers, Lean coverage, scope changes, complete source proof text, and prover notes for both source entries: `line-17`/`epi_of_shortExact` and `thm:quotient-flasque`/`of_shortExact_of_isFlasque`.

## Candidate Skeleton Review

- `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` propose ad hoc definitions `isFlasquePresheaf`/`isFlasqueSheaf` and a theorem named `of_shortExact_of_isFlasque`. These skeletons capture the informal idea but use non-Mathlib sheaf types and morphisms (`Presheaf (OpenSet X) (AddCommGroup)`, `→ₗ`) and do not match the actual Mathlib topology/sheaf API.
- `Skeleton2.lean` and `Skeleton3.lean` add a trivial `epi_of_shortExact : True`; that does not cover the proof-backed source lemma and is rejected.
- `Skeleton4.lean` is syntactically malformed around the quotient-flasque theorem and is rejected.
- The final draft instead follows Mathlib's existing `TopCat.Presheaf.IsFlasque`, `TopCat.Sheaf.IsFlasque`, `TopCat.Sheaf.IsFlasque.epi_of_shortExact`, and `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`, with local required names wrapping the same statement shapes.

## Source Statement Inventory

### line-17

- Source inventory entry `line-17`: theorem `[epi_of_shortExact]` in `docs/source.tex`.
- Source label: `line-17`
- Source inventory entry: `line-17`
- Source inventory label: `line-17`
- Source block label: `line-17`
- Detected source block label: `line-17`
- Planned Lean declaration: `epi_of_shortExact`.
- Lean kind: theorem.
- Source locator: `docs/source.tex`, theorem block lines 17--26 with proof environment lines 28--129.
- Skeleton candidate used: none directly; skeleton `epi_of_shortExact : True` was rejected. The declaration is shaped by Mathlib search result `TopCat.Sheaf.IsFlasque.epi_of_shortExact`.
- Dependencies: `ShortComplex (TopCat.Sheaf AddCommGrpCat X)`, `S.ShortExact`, `TopCat.Sheaf.IsFlasque S.X₁`, `Epi`, `op`, `Opens`; proof dependency on local surjectivity of epimorphisms and exactness of sections as in `Mathlib.Topology.Sheaves.Flasque`.
- Source statement: “Let \(X\) be a topological space. A presheaf \(F\) on \(X\) is called \emph{flasque} if for every inclusion of open sets \(V \subseteq U\), the restriction map \(F(U)\to F(V)\) is an epimorphism. A sheaf is called \emph{flasque} if its underlying presheaf is flasque.”
- Source/proof ambiguity note: the displayed theorem statement is a definition of flasque, but the following proof is not a proof of that definition. The proof proves the standard lemma used by the second theorem: in a short exact sequence of sheaves of abelian groups, if the left sheaf is flasque, then the quotient morphism is epi on sections over every open set. This matches the required name `epi_of_shortExact` and the Mathlib theorem with the same base name.
- Formal Lean statement:

```lean
theorem epi_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)}
    (U : Opens X) (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁] :
    Epi (S.g.1.app (op U))
```

- Source qualifiers:
  - Displayed-definition object class: presheaves and sheaves on a topological space `X`.
  - Displayed-definition quantifiers/parameter domain: an arbitrary presheaf `F` on `X`; every inclusion of open sets `V ⊆ U`.
  - Displayed-definition output codomain/equality condition: the restriction morphism `F(U) -> F(V)` is an epimorphism; a sheaf is flasque exactly when its underlying presheaf is flasque.
  - Proof-backed lemma object class: sheaves of abelian groups on a topological space in a short exact sequence `0 -> F -> G -> H -> 0`.
  - Proof-backed lemma quantifier order: topological space `X`, short exact complex `S`, open set `U`, exactness proof `hS`, and flasque hypothesis on the left sheaf.
  - Proof-backed lemma output codomain/equality condition: the component `S.g.1.app (op U)` is an epimorphism in `AddCommGrpCat`; by `AddCommGrpCat.epi_iff_surjective`, this is the source proof's surjectivity of sections `G(U) -> H(U)`.
  - Side conditions: `S.ShortExact` encodes exactness of `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0`; `[TopCat.Sheaf.IsFlasque S.X₁]` encodes flasqueness of the left sheaf.
  - Follow-on claim: this lemma supplies the local section-surjectivity used in `of_shortExact_of_isFlasque`.
- Lean coverage: the displayed definition is covered by imported Mathlib declarations `TopCat.Presheaf.IsFlasque` and `TopCat.Sheaf.IsFlasque` from the direct import `Mathlib.Topology.Sheaves.Flasque`; these direct imported declarations are the companion declarations for the source definition, so no local definition stub is needed. The local theorem `epi_of_shortExact` covers the proof-backed lemma and its intended use in the second theorem.
- Scope changes: the source block is internally inconsistent: the displayed theorem text is a definition, while the following proof proves the named short-exact lemma. The reviewed draft records this split explicitly. Representation is Mathlib-native: “topological space” is encoded as `TopCat`; “short exact sequence” is encoded as `ShortComplex` plus `S.ShortExact`; “surjective restriction/component map” is encoded by categorical `Epi`, equivalent to function-surjectivity in `AddCommGrpCat`.
- Formal statement review: source-fidelity review required because the LaTeX theorem block contains a definition while its proof proves a separate lemma. The Lean theorem follows the proof text and the dependency of the second theorem, not the malformed displayed statement alone.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof (complete):

```text
Fix an open set U subset X and a section s in H(U). Consider the set
S = {(V,t) | V subset U is an open subset and t in F(V) such that g(t) = s|_V}.
partially ordered as follows: an element (V',t') is said to dominate (V,t) if V subset V' and t'|_V = t. We call an element of S a partial lift of s. Then every chain of S has an upper bound. Indeed, let {(V_alpha,t_alpha)} be a chain of partial lifts of s. Because the open sets V_alpha are linearly ordered by inclusion, the sections t_alpha agree on overlaps. Hence, by the sheaf gluing axiom, they glue to a section t in F(bigcup_alpha V_alpha). This glued section still maps to s restricted to bigcup_alpha V_alpha, so it defines a partial lift over bigcup_alpha V_alpha. By construction, this partial lift dominates every member of the chain.

Since (U,s) in S, by Zorn's lemma, there exists a maximal partial lift t in G(V), V subset U, such that g(t) = s|_V.

We claim that V=U. Let x in U. Since g : G -> H is an epimorphism of sheaves, it is locally surjective, so there exists an open neighborhood W containing x and a section t_1 in G(W) such that g(t_1)=s|_W.

On the overlap V cap W, both t|_{V cap W} and t_1|_{V cap W} map to the same section of H(V cap W). Hence their difference t_2 := t|_{V cap W} - t_1|_{V cap W} lies in the kernel of g(V cap W) : G(V cap W) -> H(V cap W). By exactness, there exists t_3 in F(V cap W) such that f(t_3)=t_2.

Since F is flasque, the section t_3 extends to a section t_4 in F(W). Define t_1' := t_1 + f(t_4) in G(W). Then on V cap W we have t_1'|_{V cap W} = t_1|_{V cap W} + f(t_4)|_{V cap W} = t_1|_{V cap W} + f(t_3) = t_1|_{V cap W} + t_2 = t|_{V cap W}.

Thus t on V and t_1' on W glue to a section t_5 in G(V cup W) such that g(t_5)=s|_{V cup W}. So (V cup W, t_5) is a partial lift of s dominating (V,t).

By maximality of (V,t), this is only possible if W subset V. Since x in W, we conclude that x in V. As x was arbitrary, U subset V. But already V subset U, so V=U.

Therefore s lifts to a section of G(U), proving that g(U) : G(U) -> H(U) is surjective.
```

- Prover notes: Mathlib already contains the theorem as `TopCat.Sheaf.IsFlasque.epi_of_shortExact`. A later proof pass can close the local required-name wrapper by applying that theorem with `(U := U)` and `hS`. The source proof corresponds to the Mathlib implementation using `exists_maximal_of_chains_bounded`, local surjectivity of epi sheaf morphisms, exactness on sections, flasque extension, gluing, and maximality.

### thm:quotient-flasque

- Source inventory entry `thm:quotient-flasque`: theorem `[of_shortExact_of_isFlasque]` in `docs/source.tex`.
- Source label: `thm:quotient-flasque`
- Source inventory entry: `thm:quotient-flasque`
- Source inventory label: `thm:quotient-flasque`
- Source block label: `thm:quotient-flasque`
- Detected source block label: `thm:quotient-flasque`
- Planned Lean declaration: `of_shortExact_of_isFlasque`.
- Lean kind: theorem.
- Source locator: `docs/source.tex`, theorem block lines 131--138 with proof environment lines 140--163; LaTeX label `thm:quotient-flasque`.
- Skeleton candidate used: only as a naming hint; the final statement is shaped by Mathlib search result `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`.
- Dependencies: `ShortComplex (TopCat.Sheaf AddCommGrpCat X)`, `S.ShortExact`, `TopCat.Sheaf.IsFlasque S.X₁`, `TopCat.Sheaf.IsFlasque S.X₂`, and the lemma `epi_of_shortExact`/Mathlib namespaced theorem for surjectivity of `S.g` on each open set.
- Source statement: “Suppose \(0 \to \mathcal F \to \mathcal G \to \mathcal H \to 0\) is a short exact sequence of sheaves of abelian groups on \(X\). If \(\mathcal F\) and \(\mathcal G\) are flasque, then \(\mathcal H\) is flasque.”
- Formal Lean statement:

```lean
theorem of_shortExact_of_isFlasque {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)}
    (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁]
    [TopCat.Sheaf.IsFlasque S.X₂] :
    TopCat.Sheaf.IsFlasque S.X₃
```

- Source qualifiers:
  - Mathematical object class: sheaves of abelian groups on a topological space.
  - Quantifier order: topological space `X`, short exact sequence `S`, exactness proof `hS`, flasque hypotheses on the first and second sheaves.
  - Parameter domain: all inclusions of opens `V ⊆ U` in `X`, represented implicitly through the `IsFlasque` class on the quotient sheaf.
  - Output codomain/equality condition: `TopCat.Sheaf.IsFlasque S.X₃`, meaning every restriction morphism of the underlying presheaf of the quotient sheaf is epi; in the abelian-group-valued setting this is the source's surjectivity of the maps of sections.
  - Side conditions: exactness of the short complex and flasqueness of the first two terms.
  - Follow-on claims: none beyond quotient flasqueness.
- Lean coverage: exact Mathlib-native coverage of the source theorem. `S.X₁`, `S.X₂`, `S.X₃` correspond respectively to `F`, `G`, `H` in the source short exact sequence.
- Scope changes: none
- Representation notes: no theorem-content weakening, strengthening, omitted assumption, or omitted conclusion; “0 -> F -> G -> H -> 0” is encoded as a `ShortComplex` with `S.ShortExact`; flasqueness uses imported `TopCat.Sheaf.IsFlasque`; categorical epimorphisms of restrictions stand for source surjectivity of maps of sections in the abelian-group-valued setting.
- Formal statement review: the Lean theorem preserves object class, assumptions, and conclusion. Independent statement/source verification should check that using typeclass arguments for flasqueness does not obscure quantifier order.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof (complete):

```text
Let V subset U be an inclusion of open sets. We must prove that the restriction map H(U) -> H(V) is surjective.

By naturality, we have a commutative diagram
    G(U) -> H(U)
     |       |
     v       v
    G(V) -> H(V).
Now since G is flasque, the restriction map G(U) -> G(V) is surjective. Also, by the Lemma, since F is flasque, the map g(V): G(V) -> H(V) is surjective. Hence, the composition G(U) -> G(V) -> H(V) is surjective. Therefore the map H(U) -> H(V) must also be surjective. Thus H is flasque.
```

- Prover notes: Mathlib already contains the theorem as `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`. A later proof pass can either apply that theorem directly or reproduce the source proof by proving each restriction morphism epi: compose flasque restriction on `S.X₂` with section-surjectivity/epi of `S.g` from `epi_of_shortExact`, use naturality of `S.g`, then descend epi along the component `S.g.1.app U`.

## Statement Fidelity Gate

- Source inventory entries present: `line-17`, `thm:quotient-flasque`.
- Direct import plan is aligned with `ShadowBench/Source/Main.lean`.
- Generated file is covered by the root project imports.
- Definitions/structures needed for handoff are provided by Mathlib imports, not by construction stubs.
- The theorem proofs in `ShadowBench/Source/Main.lean` are intentionally left as `by sorry` for the later explicit proof workflow.
- Review checklist:
  - [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
  - [ ] A separate `/prove ShadowBench/Source/Main.lean` run has eliminated the theorem `sorry` proofs.
