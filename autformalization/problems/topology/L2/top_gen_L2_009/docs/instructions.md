# ShadowBench Instructions: `topology/L2/top_gen_L2_009`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Stalks
```

## Expected Declaration Names

- `stalkToFiber_injective`
- `sheafifyStalkIso`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
