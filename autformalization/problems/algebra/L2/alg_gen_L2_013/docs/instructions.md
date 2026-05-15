# ShadowBench Instructions: `algebra/L2/alg_gen_L2_013`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.RingTheory.Nullstellensatz
```

## Expected Declaration Names

- `zariskiClosure_is_smallest_algebraic_set`

## Formalization Rules

```text
/-
Formalize in Lean the Theorem (zariskiClosure_is_smallest_algebraic_set) from Text.

The theorem must be named `zariskiClosure_is_smallest_algebraic_set`.
   Matched text (candidate 0, theorem, label=zariskiClosure_is_smallest_algebraic_set): \begin{theorem}[zariskiClosure_is_smallest_algebraic_set] If $S \subseteq k^n$, the affine
                                                                                        algebraic set $\mathbf{V}(\mathbf{I}(S))$ is the \emph{smallest algebraic set that contains}
                                                                                        $S$ [in the sense that if $W \subseteq k^n$ is any affine algebraic set containing $S$, then
                                                                                        $\mathbf{V}(\mathbf{I}(S)) \subseteq W$]. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
