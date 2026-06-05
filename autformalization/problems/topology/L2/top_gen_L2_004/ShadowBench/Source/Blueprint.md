# Formalization Blueprint: `topology/L2/top_gen_L2_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single generated Lean entry for this one-theorem source. It imports the Mathlib module containing the exact required declaration `exists_preirreducible`; no split files are needed.
- `ShadowBench/Source.lean`: project aggregator, already imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: root project module, already imports `ShadowBench.Source`, so plain project builds cover the generated entry file.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.

## Import Plan

```lean
import Mathlib.Topology.Irreducible
```

The direct import above matches the import block in `ShadowBench/Source/Main.lean`. The starting import block from `docs/instructions.md` was compared against Mathlib search results; the source statement and exact required declaration live in `Mathlib.Topology.Irreducible`, so the generated file uses that direct import.

## Suggested Search Modules

- `Mathlib.Order.Zorn`: source proof uses Zorn's lemma and chain upper bounds; useful if a local reproving variant is requested later.
- `Mathlib.Order.Minimal`: search hint for maximal/minimal order API.

## Search Log

- `lean_search "IsPreirreducible"` found `IsPreirreducible`, `IsPreirreducible.closure`, `IsPreirreducible.open_subset`, and related topology declarations.
- `lean_search "maximal preirreducible subset"` found Mathlib theorem `exists_preirreducible` in `Mathlib.Topology.Irreducible` and confirmed the theorem statement matches the source theorem.
- `lean_search "preirreducible subset"` confirmed Mathlib's `IsPreirreducible` definition: two open sets meeting the subset have a nonempty intersection with the subset.

## Required Names

- `exists_preirreducible`

## Statement Inventory

### Theorem: maximal preirreducible superset

- Planned Lean declaration: `exists_preirreducible` (the existing top-level Mathlib declaration to be imported by `ShadowBench/Source/Main.lean` from `Mathlib.Topology.Irreducible`).
- Source locator: `docs/source.tex`, lines 17-30; theorem paragraph and following proof.
- Source statement: Let `X` be a topological space. Let `S` be a preirreducible subset of `X`. Then there exists a maximal preirreducible subset `T` of `X` containing `S`.
- Lean statement:

```lean
theorem exists_preirreducible {X : Type*} [TopologicalSpace X]
    (s : Set X) (H : IsPreirreducible s) :
    ∃ t : Set X, IsPreirreducible t ∧ s ⊆ t ∧
      ∀ u, IsPreirreducible u → t ⊆ u → u = t
```

- Skeleton candidate used: `docs/skeletons/Skeleton4.lean` matches the source's maximality condition. `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` were rejected as source-inaccurate because their final clause makes `T` a greatest preirreducible superset of `S` (`S ⊆ U → U ⊆ T`) rather than merely a maximal preirreducible superset.
- Dependencies: `Set`, `TopologicalSpace`, Mathlib predicate `IsPreirreducible`, and the maximality theorem `exists_preirreducible`. The source proof dependency is Zorn's lemma (`zorn_subset_nonempty`) plus the fact that the union of a chain of preirreducible subsets is preirreducible.
- Formal statement review: The source quantifies over a topological space `X`, a subset `S : Set X`, and an assumption that `S` is preirreducible, then returns a subset `T : Set X` that is preirreducible, contains `S`, and is maximal under inclusion among all preirreducible subsets. Mathlib's theorem expresses maximality as `∀ u, IsPreirreducible u → t ⊆ u → u = t`; since the theorem also includes `s ⊆ t`, any such larger `u` automatically contains `s`, so this is equivalent to maximality inside the family of preirreducible supersets of `S`.
- Source qualifiers:
  - Mathematical object class: arbitrary topological space `X`.
  - Parameter domain: arbitrary subset `S : Set X`.
  - Side condition: `S` is preirreducible.
  - Output codomain: subset `T : Set X`.
  - Output properties: `T` is preirreducible and `S ⊆ T`.
  - Maximality/equality condition: every preirreducible `U` with `T ⊆ U` satisfies `U = T`.
  - Quantifier order: choose `X`, topology, `S`, and the preirreducibility proof before the existential `T`.
  - Follow-on claims: none beyond existence and maximality.
- Lean coverage:
  - `X` and `[TopologicalSpace X]` cover the topological-space hypothesis.
  - `(s : Set X)` covers the subset parameter.
  - `(H : IsPreirreducible s)` covers the preirreducibility assumption, using Mathlib's definition matching the source proof's open-set intersection condition.
  - `∃ t : Set X` covers the produced subset.
  - `IsPreirreducible t ∧ s ⊆ t` covers preirreducibility and containment.
  - `∀ u, IsPreirreducible u → t ⊆ u → u = t` covers maximality under inclusion. The equality orientation is definitionally equivalent to `t = u` for maximality purposes.
- Scope changes: none. The Lean statement uses Mathlib's standard `IsPreirreducible` predicate rather than a custom representation, and it is source-equivalent.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```text
We use Zorn's Lemma. Consider the set \mathcal{S} = \{T \subseteq X | T \text{ is preirreducible and } S \subseteq T\}. It is nonempty since S \in \mathcal{S}.
If \mathcal{C} is a chain of \mathcal{S}, we claim that C_0:=\cup_{C \in \mathcal{C}} C is the upper bound of the chain \mathcal{C}.
It suffices to show that C_0 is preirreducible. Suppose U,V are open subsets of X such that C_0 \cap U \ne \emptyset, C_0 \cap V \ne \emptyset.
Pick x \in C_0 \cap U and y \in C_0 \cap V. Then there exist P,Q \in \mathcal{C} such that x \in P \cap U and y \in Q \cap V.
Since \mathcal{C} is a chain, we have P \subseteq Q or Q \subseteq P.
If P \subseteq Q, then Q \cap U \ne \emptyset and Q \cap V \ne \emptyset. Since Q is preirreducible, Q \cap (U \cap V) \ne \emptyset and thus C_0 \cap (U \cap V) \ne \emptyset.
Conversely, if Q \subseteq P, then P \cap U \ne \emptyset and Q \cap V \ne \emptyset. Since P is preirreducible, P \cap (U \cap V) \ne \emptyset and hence C_0 \cap (U \cap V) \ne \emptyset.
Therefore, C_0 is an upper bound of the chain \mathcal{C}. By Zorn's Lemma, \mathcal{S} has the maximal element T which satisfies the desired conditions.
```

- Source proof / prover notes: If reproving locally instead of using Mathlib's existing theorem, apply `zorn_subset_nonempty` to `{T : Set X | IsPreirreducible T}` starting from `S`. For a chain `c`, use `⋃₀ c` as the upper bound. To prove the union is preirreducible, take open `U,V` meeting `⋃₀ c`, choose members `P,Q ∈ c` containing the witnesses, use chain totality to reduce to one member containing both witnesses, and apply that member's preirreducibility. Maximality from Zorn gives the final `∀ u, IsPreirreducible u → t ⊆ u → u = t` clause.

## Formalization Rules

```text
open Set Topology

/-
Formalize in Lean the following named items from Text.

1. Theorem (exists_preirreducible)
   The theorem must be named `exists_preirreducible`.
   Matched text (candidate 1, paragraph): Let $X$ be a topological space. Let $S$ be a preirreducible subset of $X$. Then there exists
                                          a maximal preirreducible subset $T$ of $X$ containing $S$.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
