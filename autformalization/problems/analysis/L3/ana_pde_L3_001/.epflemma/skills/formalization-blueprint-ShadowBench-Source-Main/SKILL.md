---
name: formalization-blueprint-ShadowBench-Source-Main
description: Blueprint and source map for `ShadowBench/Source/Main.lean`.
---

# Formalization Blueprint Skill

Before proving declarations in `ShadowBench/Source/Main.lean`, read and use the local formalization blueprint.

- Blueprint: `ShadowBench/Source/Blueprint.md`
- Source document: `docs/source.tex`
- Treat the blueprint as the source map for theorem locators, planned Lean names, dependencies, statement-fidelity caveats, and prover notes.
- If the current proof is unclear, reopen the blueprint first, then the original source document when listed.
- Do not change source-backed theorem statements during proving unless a separate statement/source review explicitly corrected the blueprint and Lean draft.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem lines 17-45; proof lines 45-56.
- Planned Lean declarations: `satisfies_interior_sphere`.
- Lean declaration: `satisfies_interior_sphere` in `ShadowBench/Source/Main.lean`.
- Statement verification status: drafted for independent statement/source review.
- Source proof / prover notes: Use `v = M - u`, the zero set `A = {x ∈ Ω | v x = 0}`, the tangent-ball Hopf lemma contradiction for boundary points of `A`, and connectedness of `Ω` to conclude `A = Ω`.

## Handoff Notes

- `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`, so project-level `lake build` covers the target module.
- The Lean proof of `satisfies_interior_sphere` is intentionally left as the sole later theorem proof obligation.
- The statement/source review approval remains independent and is not self-approved by this drafting pass.
