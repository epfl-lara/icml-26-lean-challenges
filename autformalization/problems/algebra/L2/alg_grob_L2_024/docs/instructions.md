# ShadowBench Instructions: `algebra/L2/alg_grob_L2_024`

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
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Henselian
```

## Expected Declaration Names

- `mem_monmul_supp_iff`

## Formalization Rules

```text
/-
Formalize in Lean the Lemma (mem_monmul_supp_iff) from Text.

The lemma must be named `mem_monmul_supp_iff`.
   Matched text (candidate 0, lemma, label=mem_monmul_supp_iff): Lemma (mem_monmul_supp_iff) Let $K[\sigma]$ be a ring of multivariate polynomials, where
                                                                 $\sigma$ is a set of variable symbols, and $K$ is a field. For two exponent tuples $\mu, \nu
                                                                 \in \mathbb{Z}_{\ge 0}^{\oplus \sigma}$, $x^\mu$ divides $x^\nu$ if and only if there exists
                                                                 a polynomial $f \in K[\sigma]$ such that $x^\nu$ is in $x^\mu f$.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
