import Mathlib.Topology.Irreducible

open Set Topology

/-
ShadowBench problem: topology/L2/top_gen_L2_004
Source: docs/source.tex
Instructions: docs/instructions.md
Candidate skeletons: docs/skeletons/
Blueprint: ShadowBench/Source/Blueprint.md

The required source theorem is formalized by Mathlib's top-level declaration
`exists_preirreducible`, imported above from `Mathlib.Topology.Irreducible`.
It is not redeclared here because Lean declaration names are global and the
required exact name already exists in the imported module.

Source proof / prover notes for `exists_preirreducible`: use Zorn's lemma on the
family of preirreducible subsets containing the starting set. The union of a
chain is preirreducible: for two open sets meeting the union, choose witnessing
chain members for the two points; totality of the chain puts both witnesses in
one preirreducible member, whose preirreducibility gives a point in the
intersection. This supplies chain upper bounds, so Zorn gives a maximal
preirreducible superset.
-/
