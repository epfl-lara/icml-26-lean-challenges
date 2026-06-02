# ShadowBench Instructions: `topology/L2/top_gen_L2_014`

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
import Mathlib.Algebra.Homology.AlternatingConst
import Mathlib.AlgebraicTopology.SingularSet
import CategoryTheory.Limits
import CategoryTheory.Functor.Category
import Topology.Connected
```

## Expected Declaration Names

- `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace`
- `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`
- `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`

## Formalization Rules

```text
open CategoryTheory Limits

/-
Formalize in Lean the following named items from Text.

1. Definition (singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace)
   The definition must be named `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace`.
   Matched text (candidate 0, definition, label=singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace): \begin{definition}[singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace] Given a
                                                                                                                  preadditive category $C$ with coproducts and homology, the singular chain complex functor is
                                                                                                                  the functor \begin{align*} C_\bullet(-;-): C \to \text{Fun}(\textbf{Top}, \textbf{Ch}_{\ge
                                                                                                                  0}(C)),\quad R \mapsto (X \to C_\bullet(X;R)) \end{align*} from $C$ to the category of
                                                                                                                  functors from the category $\textbf{Top}$ of topological…
2. Definition (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace)
   The definition must be named `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`.
   Matched text (candidate 1, definition, label=isZero_singularHomologyFunctor_of_totallyDisconnectedSpace): \begin{definition}[isZero_singularHomologyFunctor_of_totallyDisconnectedSpace] Let $C$ be a
                                                                                                             preadditive category wth coproducts and homology. Then the singular homology functor is the
                                                                                                             functor \begin{align*} H_\bullet(-;-):C \to \text{Fun}(\textbf{Top},\textbf{Ch}_{\ge 0}(C)),
                                                                                                             R \mapsto (X \mapsto H_\bullet(X;R)) \end{align*} where $H_n(X;R)$ is the $n$-th homology of
                                                                                                             the chain complex $C_\bullet(X;R)$. \end{definiti…
3. Definition (singularHomologyFunctorZeroOfTotallyDisconnectedSpace)
   The definition must be named `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`.
   Matched text (candidate 2, definition, label=singularHomologyFunctorZeroOfTotallyDisconnectedSpace): \begin{definition}[singularHomologyFunctorZeroOfTotallyDisconnectedSpace] Let $X$ be a
                                                                                                        totally disconnected topological space, $C$ a preadditive category with coproducts and
                                                                                                        homology, and $R$ an object of $C$. Then the singular homology of $X$ with coefficients in
                                                                                                        $R$ is given by \begin{align*} H_n(X;R) = \begin{cases} \coprod_{x \in X} R, &\text{ if }n =
                                                                                                        0\\ 0, &\text{ if } n > 0 \end{cases} \end{align*} \end{defin…

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
