# ShadowBench Instructions: `algebra/L2/alg_grob_L2_022`

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
import Mathlib.Algebra.MvPolynomial.Basic
```

## Expected Declaration Names

- `monomial_set_union_distrib`

## Formalization Rules

```text
/-
Formalize in Lean the Lemma (monomial_set_union_distrib) from Text.

The lemma must be named `monomial_set_union_distrib`.
   Matched text (candidate 0, lemma, label=monomial_set_union_distrib): Lemma (monomial_set_union_distrib) Commutativity of union and monomial set Let $F, G
                                                                        \subseteq R[\sigma]$ be some finite subsets of multivariate polynomials, where $\sigma$ is a
                                                                        set of variable symbols over which a monomial order $>$ is fixed, and $R$ is a commutative
                                                                        semiring. Let $\mathrm{Mon}(F)$ be the entire set of monomials in some $f \in F$. Then
                                                                        $\mathrm{Mon}(F) \cup \mathrm{Mon}(G) = \mathrm{Mon}(F \cup G)$.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
