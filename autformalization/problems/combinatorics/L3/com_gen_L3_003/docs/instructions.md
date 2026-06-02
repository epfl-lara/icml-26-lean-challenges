# ShadowBench Instructions: `combinatorics/L3/com_gen_L3_003`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Candidate Skeletons

Dataset: `Lemmy00/ShadowBench-skeletons-prod`

- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Treat these as candidate statement/definition shapes, not authoritative answers. Prefer the source theorem and formalization rules when candidates disagree.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Combinatorics.Matroid.Minor.Delete
import Mathlib.Tactic.TautoSet
```

## Expected Declaration Names

- `contract_closure_eq_contract_delete`
- `contract_closure_eq`
- `contract_spanning_iff`

## Formalization Rules

```text
open Set

/-
Formalize in Lean the following named items from Text.

1. Lemma (contract_closure_eq_contract_delete)
   The lemma must be named `contract_closure_eq_contract_delete`.
   Matched text (candidate 0, lemma, label=Contracting the closure): \begin{lemma}[Contracting the closure] For any \(C\subseteq E(M)\), \[ M/\mathrm{cl}_M(C)=
                                                                     (M/C)\setminus\bigl(\mathrm{cl}_M(C)\setminus C\bigr). \] \end{lemma}
2. Lemma (contract_closure_eq)
   The lemma must be named `contract_closure_eq`.
   Matched text (candidate 1, lemma, label=Closure in a contraction): \begin{lemma}[Closure in a contraction] For any sets \(C,X\), \[
                                                                      \mathrm{cl}_{M/C}(X)=\mathrm{cl}_M(X\cup C)\setminus C. \] \end{lemma}
3. Lemma (contract_spanning_iff)
   The lemma must be named `contract_spanning_iff`.
   Matched text (candidate 2, theorem, label=contract_spanning_iff): \begin{theorem}[contract_spanning_iff] Assume \(C\subseteq E(M)\). Then \[ X \text{ is
                                                                     spanning in } M/C \;\Longleftrightarrow\; \bigl(X\cup C \text{ is spanning in } M\bigr)\
                                                                     \wedge\ \mathrm{Disjoint}(X,C). \] \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
