# Formalization Blueprint: `topology/L2/top_gen_L2_009`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

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

1. Theorem (stalkToFiber_injective)
   The theorem must be named `stalkToFiber_injective`.
   Matched text (candidate 0, definition): \begin{definition} Let $X$ be a topological space and $\mathcal{F}$ a presheaf of sets on
                                           $X$. Let $\widetilde{\mathcal{F}}$ be the presheaf \begin{align*} U \mapsto \{(s_x)_{x \in
                                           U} \in \prod_{x \in U} \mathcal{F}_x \text{ such that $(*)$.}\} \end{align*} where $(*)$ is
                                           the property that for any $x \in U$, there exists an open neighborhood $V \subseteq U$ of
                                           $x$, and a section $s \in \mathcal{F}(V)$ such that $s_y…
2. Definition (sheafifyStalkIso)
   The definition must be named `sheafifyStalkIso`.
   Matched text (candidate 1, definition, label=sheafifyStalkIso): \begin{definition}[sheafifyStalkIso] Let $X$ be a topological space and $\mathcal{F}$ a
                                                                   presheaf of sets on $X$. Let $\widetilde{\mathcal{F}}$ be the sheafification of
                                                                   $\mathcal{F}$. For $x \in X$, an obvious map \begin{align*} \phi_x:
                                                                   \widetilde{\mathcal{F}}_x \to \mathcal{F}_x, \quad (U,s) \mapsto s(x) \end{align*} is an
                                                                   isomorphism of stalks $\widetilde{\mathcal{F}}_x$ and $\mathcal{F}_x$. \end{definition}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
