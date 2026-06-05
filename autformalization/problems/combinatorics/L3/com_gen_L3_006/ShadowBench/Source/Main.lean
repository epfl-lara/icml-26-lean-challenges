import Mathlib

open scoped Finset

/-!
ShadowBench problem `combinatorics/L3/com_gen_L3_006`.
Source: `docs/source.tex`.
-/

/--
Vertex-labeled trees with `n` vertices, represented as simple graphs on the fixed label type
`Fin n` satisfying Mathlib's connected-and-acyclic tree predicate.

This bridges the source label set `{1, 2, ..., n}` to the equivalent fixed `n`-element
label type `Fin n`. Distinct labeled trees are equality-distinct graphs on this fixed
vertex type.
-/
def LabeledTree (n : ℕ) : Type :=
  {G : SimpleGraph (Fin n) // G.IsTree}

/--
Cayley's formula for vertex-labeled trees.

Source proof: The text defines `T_{n,k}` as the number of labeled forests on labels
`{1, ..., n}` with `k` trees and fixed roots `1, ..., k` in distinct components.
Deleting vertex `1` gives the recurrence
`T_{n,k} = ∑_{i=0}^{n-k} (n-k choose i) T_{n-1,k-1+i}`. Induction on `n`, followed
by reindexing and the binomial theorem, proves `T_{n,k} = k * n^(n-k-1)` for
`n ≥ 1` and `0 ≤ k ≤ n`; taking `k = 1` gives `T_n = n^(n-2)`.

Prover notes: The Lean statement counts the subtype of simple graphs on `Fin n` that
satisfy `SimpleGraph.IsTree`. A proof may formalize the source forest recurrence, or
instead construct a Prüfer-code equivalence with `(Fin (n - 2) → Fin n)` and then use
cardinality of function types. The hypothesis `0 < n` records the source proof's
`n ≥ 1` range.
-/
theorem CayleyTreeCount (n : ℕ) (hn : 0 < n) :
    Nat.card (LabeledTree n) = n ^ (n - 2) := by
  sorry
