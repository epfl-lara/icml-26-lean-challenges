# Formalization Blueprint: `topology/L2/top_gen_L2_007`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Topology.Compactness.Bases
import Mathlib.Topology.NoetherianSpace
```

## Required Names

- `IsQuasiSeparated.image_of_isEmbedding`

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
open Set TopologicalSpace Topology

/-
Formalize in Lean the Theorem (IsQuasiSeparated.image_of_isEmbedding) from Text.

The theorem must be named `IsQuasiSeparated.image_of_isEmbedding`.
   Matched text (candidate 0, theorem, label=IsQuasiSeparated.image_of_isEmbedding): \begin{theorem}[IsQuasiSeparated.image_of_isEmbedding] Let $S \subseteq X$ be a
                                                                                     quasiseparated set and $h:X \to Y$ is a topological embedding. Then, $f(S)$ is
                                                                                     quasiseparated. \end{theorem}
-/
```
