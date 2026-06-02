# Formalization Blueprint: `topology/L2/top_gen_L2_014`

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
import Mathlib.Algebra.Homology.AlternatingConst
import Mathlib.AlgebraicTopology.SingularSet
import CategoryTheory.Limits
import CategoryTheory.Functor.Category
import Topology.Connected
```

## Required Names

- `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace`
- `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`
- `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`

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
