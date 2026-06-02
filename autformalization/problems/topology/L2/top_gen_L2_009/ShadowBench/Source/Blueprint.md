# Formalization Blueprint: `topology/L2/top_gen_L2_009`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.

## Import Plan

```lean
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Stalks
```

## Required Names

- `stalkToFiber_injective`
- `sheafifyStalkIso`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Skeleton candidate used: _pending_
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

## Formalization Rules

```text
open TopCat Opposite TopologicalSpace CategoryTheory

/-
Formalize in Lean the following named items from Text.

1. Definition (stalkToFiber_injective)
   The definition must be named `stalkToFiber_injective`.
   Matched text (candidate 0, definition, label=stalkToFiber_injective): \begin{definition}[stalkToFiber_injective] Let $X$ be a topological space and $\mathcal{F}$
                                                                         a presheaf of sets on $X$. Let $\widetilde{\mathcal{F}}$ be the presheaf \begin{align*} U
                                                                         \mapsto \{(s_x)_{x \in U} \in \prod_{x \in U} \mathcal{F}_x \text{ such that $(*)$.}\}
                                                                         \end{align*} where $(*)$ is the property that for any $x \in U$, there exists an open
                                                                         neighborhood $V \subseteq U$ of $x$, and a section $s \in \mathc…
2. Theorem (sheafifyStalkIso)
   The theorem must be named `sheafifyStalkIso`.
   Matched text (candidate 1, theorem, label=sheafifyStalkIso): \begin{theorem}[sheafifyStalkIso] Let $X$ be a topological space and $\mathcal{F}$ a
                                                                presheaf of sets on $X$. Let $\widetilde{\mathcal{F}}$ be the sheafification of
                                                                $\mathcal{F}$. For $x \in X$, an obvious map \begin{align*} \phi_x:
                                                                \widetilde{\mathcal{F}}_x \to \mathcal{F}_x, \quad (U,s) \mapsto s(x) \end{align*} is an
                                                                isomorphism of stalks $\widetilde{\mathcal{F}}_x$ and $\mathcal{F}_x$. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
