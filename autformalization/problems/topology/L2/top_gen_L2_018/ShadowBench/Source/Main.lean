import Mathlib.Topology.Sheaves.Flasque

open TopCat TopologicalSpace Opposite CategoryTheory Presheaf Limits
open scoped AlgebraicGeometry

universe u

/--
Source locator: `docs/source.tex`, source entry `line-17` (`epi_of_shortExact`).
Source proof: the proof constructs partial lifts of a section of the quotient sheaf, orders them by
extension, applies Zorn's lemma, then uses local surjectivity of the sheaf epimorphism, exactness,
flasqueness of the left sheaf, and sheaf gluing to enlarge any maximal partial lift; hence the
maximal lift is defined on all of `U`.
Prover notes: this is the proof-backed lemma behind the source's first block. Mathlib already has
`TopCat.Sheaf.IsFlasque.epi_of_shortExact`; the later proof pass can apply it with `(U := U)` and
`hS`.
-/
theorem epi_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)}
    (U : Opens X) (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁] :
    Epi (S.g.1.app (op U)) := by
  sorry

/--
Source locator: `docs/source.tex`, source entry `thm:quotient-flasque`
(`of_shortExact_of_isFlasque`).
Source proof: for an inclusion `V ⊆ U`, use flasqueness of `G` to lift a section from `G(V)` to
`G(U)`, use `epi_of_shortExact` and flasqueness of `F` to lift the target section in `H(V)` through
`G(V)`, then commute the restriction square for `g : G ⟶ H` to show the restriction map of `H` is
surjective.
Prover notes: Mathlib already has `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`; a later
proof pass can apply it directly to `hS`, or replay the source proof using the local
`epi_of_shortExact` wrapper and naturality of `S.g`.
-/
theorem of_shortExact_of_isFlasque {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)}
    (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁]
    [TopCat.Sheaf.IsFlasque S.X₂] :
    TopCat.Sheaf.IsFlasque S.X₃ := by
  sorry
