# ShadowBench Instructions: `topology/L2/top_gen_L2_004`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Order.Minimal
import Mathlib.Order.Zorn
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.StacksAttribute
import Mathlib.Topology.DiscreteSubset
```

## Expected Declaration Names

- `isIrreducible_singleton`
- `isPreirreducible_iff_closure`
- `isIrreducible_iff_closure`
- `exists_preirreducible`

## Formalization Rules

```text
open Set Topology

/-
Formalize in Lean the following named items from Text.

1. Theorem (isIrreducible_singleton)
   The theorem must be named `isIrreducible_singleton`.
   Matched text (candidate 0, paragraph): Theorem
2. Theorem (isPreirreducible_iff_closure)
   The theorem must be named `isPreirreducible_iff_closure`.
   Matched text (candidate 1, paragraph): Let $X$ be a topological space. Let $S$ be a preirreducible subset of $X$. Then there exists
                                          a maximal preirreducible subset $T$ of $X$ containing $S$.
3. Theorem (isIrreducible_iff_closure)
   The theorem must be named `isIrreducible_iff_closure`.
   Matched text (candidate 2, paragraph): Proof
4. Theorem (exists_preirreducible)
   The theorem must be named `exists_preirreducible`.
   Matched text (candidate 3, paragraph): We use Zorn's Lemma. Consider the set $\mathcal{S} = \{T \subseteq X | T \text{ is
                                          preirreducible and } S \subseteq T\}$. It is nonempty since $S \in \mathcal{S}$. If
                                          $\mathcal{C}$ is a chain of $\mathcal{S}$, we claim that $C_0:=\cup_{C \in \mathcal{C}} C$
                                          is the upper bound of the chain $\mathcal{C}$. It suffices to show that $C_0$ is
                                          preirreducible. Suppose $U,V$ are open subsets of $X$ such that $C_0 \cap U \ne…

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
