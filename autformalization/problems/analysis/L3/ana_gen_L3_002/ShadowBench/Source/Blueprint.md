# Formalization Blueprint: `analysis/L3/ana_gen_L3_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Current stage: manual Codex audit completed on 2026-06-04 after the old batch log missed a final literal `PASS`. `ShadowBench/Source/Main.lean` verifies; the axis-aligned rectangle convention is accepted as the intended source interpretation, and theorem proof is intentionally left to the prover workflow.
- 2026-06-05 statement-fidelity review (FIXED): the disc was previously encoded as `Metric.ball center radius` in `ℝ × ℝ`. Mathlib's `Metric.ball`/`dist` on `ℝ × ℝ` use the sup (L∞) metric, so that set is an axis-aligned open SQUARE — itself an open rectangle — which makes the theorem FALSE (the "disc" equals a single open rectangle). The conclusion was changed to the genuine Euclidean disc written explicitly as `{p | (p.1 - center.1)^2 + (p.2 - center.2)^2 < radius^2}`, matching `Skeleton4`. Lean check still passes (one `sorry`).

## Generated File Layout

- `ShadowBench/Source/Main.lean`: generated formalization file with the direct Mathlib import, auxiliary rectangle predicate, and the source theorem skeleton.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`, so the generated target is covered by the root `ShadowBench` library target.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the default `ShadowBench` target covers the generated source module.

No file split is currently useful for this one-theorem document.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
```

The target Lean file uses this import block exactly.

## Suggested Search Modules

These are search/prover hints only, not additional direct imports for the draft:

- `Mathlib.Analysis.InnerProductSpace.EuclideanDist` for Euclidean-space infrastructure; the disc itself is encoded by an explicit quadratic inequality to avoid the product sup metric.
- `Mathlib.Order.Interval.Set.Defs` for `Set.Ioo`.
- `Mathlib.Data.Set.Pairwise.Basic` for `Pairwise`/pairwise disjoint set-family conventions.
- Connectedness/path-connectedness facts for balls and products of intervals may be useful during the later proof phase.

## Required Names

- `open_disc_not_disjoint_union_rectangles`

## Search Log

- Inspected `docs/source.tex` and the preflight manifest. The only theorem-like block is source entry `line-17`, titled `open_disc_not_disjoint_union_rectangles`, with no proof body.
- Read `docs/instructions.md` and all four candidate skeletons. Skeletons 1-3 use an endpoint-quadruple set encoding that is not a faithful arbitrary family of disjoint rectangles. Skeleton4 gives the best family-indexed shape.
- Searched Mathlib/project declarations for `Metric.ball`, `Set.Ioo`, product-of-interval rectangle encodings, and pairwise disjoint families. Relevant declarations include `Metric.ball`, `Set.Ioo`, `Set.PairwiseDisjoint`, `Disjoint`, and `Pairwise`.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source label: `line-17`
- Source kind: theorem
- Source title/name: `open_disc_not_disjoint_union_rectangles`
- Source locator: `docs/source.tex`, theorem environment lines 17--19; no proof lines.
- Source statement: "An open disc in $\mathbb{R}^2$ is not the disjoint union of open rectangles."
- Complete source proof text: no proof body is present in the source document.
- Planned Lean declarations: `IsOpenRectangle`, `open_disc_not_disjoint_union_rectangles`.
- Formal statement review: The Lean theorem formalizes an open disc as the explicit EUCLIDEAN disc `{p | (p.1 - center.1)^2 + (p.2 - center.2)^2 < radius^2}` in `ℝ × ℝ` with `0 < radius` (NOT `Metric.ball`, which is the sup-metric square on `ℝ × ℝ`). It formalizes an open rectangle by the companion predicate `IsOpenRectangle`, namely an axis-aligned Cartesian product `Set.Ioo a b ×ˢ Set.Ioo c d` with strict endpoint inequalities. It formalizes "disjoint union" as an arbitrary indexed family `rectangles : ι → Set (ℝ × ℝ)` whose members satisfy `Pairwise (fun i j => Disjoint (rectangles i) (rectangles j))`, and it denies equality between the disc and the indexed union `⋃ i, rectangles i`.
- Source qualifiers: mathematical object class is an open disc in `ℝ^2`; quantification is universal over the center and positive radius; rectangle class is standard axis-aligned open rectangles; parameter domain/codomain is `ℝ × ℝ`; equality condition is the claimed union equality; side conditions are positive radius and nondegenerate rectangle intervals; follow-on claim is nonexistence of any such disjoint decomposition.
- Lean coverage: `center : ℝ × ℝ`, `radius : ℝ`, and `hradius : 0 < radius` cover the open disc through the explicit Euclidean set `{p | (p.1 - center.1)^2 + (p.2 - center.2)^2 < radius^2}`; `IsOpenRectangle (rectangles i)` covers each open rectangle; `hdisjoint` covers disjointness; the theorem denies equality between that Euclidean disc and `⋃ i, rectangles i` for arbitrary finite, countable, or uncountable index types.
- Scope changes: no intentional weakening. The only representation choice is the standard analysis convention that an open rectangle in `ℝ^2` is an axis-aligned product of open intervals. If a reviewer reads "rectangle" as allowing rotated rectangles, the current statement should be marked as axis-aligned coverage; the source and all candidate skeletons support the axis-aligned interpretation.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: no source proof is supplied. A natural proof should use connectedness/path-connectedness of the open disc. If a pairwise-disjoint family of nonempty open rectangles had union equal to the disc, the family would give a disjoint open cover of a connected set, so at most one rectangle could occur. The singleton case requires showing that a positive-radius disc is not an axis-aligned open rectangle, for example by comparing vertical cross-sections or using strict convexity/curved-boundary behavior.

## Source Inventory

1. `line-17` (theorem, lines 17-19) - open_disc_not_disjoint_union_rectangles
   Source statement: An open disc in $\mathbb{R}^2$ is not the disjoint union of open rectangles.
   Source proof excerpt: no proof body is present in the source document.
   Source proof locator: none supplied.
   Planned Lean declaration: `open_disc_not_disjoint_union_rectangles`
   Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

### Source inventory entry `line-17`: theorem `open_disc_not_disjoint_union_rectangles`

- line-17: theorem `open_disc_not_disjoint_union_rectangles` formalized by Lean declaration `open_disc_not_disjoint_union_rectangles`.
- Source inventory entry `line-17`: theorem `open_disc_not_disjoint_union_rectangles`
- Source inventory entry line-17: theorem open_disc_not_disjoint_union_rectangles
- Source inventory entry: line-17
- Source inventory entry: `line-17`
- Source label: line-17
- Source label: `line-17`
- Source kind: theorem
- Source title/name: `open_disc_not_disjoint_union_rectangles`
- Lean declaration: `open_disc_not_disjoint_union_rectangles`

## Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source kind: theorem
- Source title: `open_disc_not_disjoint_union_rectangles`
- Planned Lean declaration: `open_disc_not_disjoint_union_rectangles`
- Source locator: `docs/source.tex`, theorem lines 17--19, no proof body
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

### Source inventory entry `line-17`: theorem `open_disc_not_disjoint_union_rectangles`

- Source inventory entry: `line-17`
- Planned Lean declaration: `open_disc_not_disjoint_union_rectangles`
- Source locator: `docs/source.tex`, label `line-17`, theorem environment lines 17--19; no proof environment.
- Source statement: An open disc in `ℝ^2` is not the disjoint union of open rectangles.
- Planned Lean declarations:
  - `IsOpenRectangle`: source-specific bridge for "open rectangle" as a nondegenerate axis-aligned product of open real intervals.
  - `open_disc_not_disjoint_union_rectangles`: source theorem for arbitrary centers, positive radii, index types, rectangle families, and pairwise-disjoint hypotheses.
- Skeleton candidate used: `docs/skeletons/Skeleton4.lean` shaped the statement because it uses an arbitrary indexed family `I → Set (ℝ × ℝ)` and a pairwise-disjoint hypothesis. `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` are duplicates whose endpoint-quadruple-set encoding is less faithful to the source phrase "disjoint union of open rectangles".
- Dependencies: explicit Euclidean quadratic inequality in `ℝ × ℝ`, `Set.Ioo`, `Set.prod` notation `×ˢ`, indexed union `⋃ i, rectangles i`, `Disjoint`, `Pairwise`, and real product space notation.

#### Source qualifiers

- Mathematical object class: an open disc in `ℝ^2`.
- Quantifier order: choose a center `center : ℝ × ℝ`, a radius `radius : ℝ`, assume `0 < radius`, then consider any index type `ι`, any family `rectangles : ι → Set (ℝ × ℝ)`, and hypotheses saying the members are open rectangles and pairwise disjoint.
- Parameter domain: points lie in `ℝ × ℝ`, representing `ℝ^2`.
- Output codomain: the theorem is a proposition denying an equality of subsets of `ℝ × ℝ`.
- Equality/image condition: the formal conclusion is `{p : ℝ × ℝ | (p.1 - center.1)^2 + (p.2 - center.2)^2 < radius^2} ≠ ⋃ i, rectangles i`.
- Side conditions: every rectangle has strict interval bounds `a < b` and `c < d`, and the disc has positive radius.
- Follow-on claims: no corollaries are present in the source.

#### Lean coverage

- `center : ℝ × ℝ` covers the center of an arbitrary open disc in `ℝ^2`.
- `radius : ℝ` and `hradius : 0 < radius` cover a positive radius.
- The explicit quadratic inequality covers the Euclidean open disc.
- `IsOpenRectangle (rectangles i)` covers each open rectangle as an axis-aligned product of open intervals.
- `Pairwise (fun i j => Disjoint (rectangles i) (rectangles j))` covers pairwise disjointness of the family.
- The explicit Euclidean-disc inequality not equal to `⋃ i, rectangles i` covers the statement that the disc is not such a disjoint union.

#### Scope changes and representation choices

- The draft uses a companion predicate `IsOpenRectangle` rather than an anonymous inline existential, so the representation bridge is inspectable by the reviewer and prover.
- The rectangle representation is axis-aligned. This is the standard convention for open rectangles in elementary analysis/topology and matches the candidate skeletons; there is no intentional weakening under that convention.
- The index type `ι` is arbitrary, so the statement is not restricted to finite or countable unions.

#### Formal statement review

The Lean theorem preserves the natural source quantification and formalizes the informal nonexistence claim by universally denying equality for any pairwise-disjoint family of open rectangles. The auxiliary definition records the only representational convention needed for the source phrase "open rectangles".

Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

#### Complete source proof text

No proof text is present in `docs/source.tex`.

#### Source proof / prover notes

Use connectedness or path-connectedness of the explicit Euclidean disc. Each `IsOpenRectangle` member is nonempty and open. A pairwise-disjoint indexed union equal to the connected disc can contain at most one nonempty member. In the remaining one-rectangle case, prove that a positive-radius Euclidean disc is not a product of two open intervals, e.g. by comparing vertical cross-sections near the center and near the edge, or by using convex/strict-boundary behavior.

## Generated Declarations

- `IsOpenRectangle (R : Set (ℝ × ℝ)) : Prop`
  - Source role: companion definition recording the representation of "open rectangle" used by the theorem.
  - Implementation status: definitional, no proof obligation.
- `open_disc_not_disjoint_union_rectangles`
  - Source role: formalization of theorem `line-17`.
  - Proof status: theorem skeleton intentionally ends with `by sorry` for the later `/prove` workflow after statement/source review.

## Verification Notes

- `lean_inspect` on `ShadowBench/Source/Main.lean` reports no hard errors and one intentional `sorry` warning for `open_disc_not_disjoint_union_rectangles`.
- `lean_verify(mode=project)` / `lake build` completed successfully after the draft; the only generated-file warning is the intentional theorem `sorry`.
- Leave proof handoff unchecked until an independent statement/source review approves the source inventory entry and doc-comment proof notes.

## Proof-Ready Checklist

- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] The reviewer confirmed that `IsOpenRectangle` is the intended interpretation of "open rectangle" for this source.
- [ ] The prover queue has been launched explicitly by the user or runner after review.
