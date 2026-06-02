import Challenges.Spanner.Def_Spanner

namespace Spanner

/-- (100 pts) Spanner existence. Prove that every connected simple graph
on `n` vertices admits a `(2t - 1)`-spanner with at most `2 * n * n^(1/t)`
edges. This is the classical Althofer, Das, Dobkin, Joseph existence
bound. -/
lemma spanner_exists {n} (G : SimpleGraph (Fin n))
    (hG : G.Connected) (t : ℕ) [NeZero t] :
    ∃ H : SimpleGraph (Fin n), H.IsSpannerOf G (2 * t - 1)
    ∧ H.numEdges ≤ 2 * n * (NNReal.rpow ↑n (1 / (↑t))) := sorry

end Spanner
