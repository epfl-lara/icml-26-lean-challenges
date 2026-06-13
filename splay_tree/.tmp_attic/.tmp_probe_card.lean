import Challenges.ZBK
open Splay
def inBlock (lo hi : ℕ) (k : ℕ) : Bool := decide (lo ≤ k ∧ k ≤ hi)
-- nodup list filtered by interval membership: length ≤ hi+1-lo
example (L : List ℕ) (lo hi : ℕ) (hnd : L.Nodup) :
    (L.filter (inBlock lo hi)).length ≤ hi + 1 - lo := by
  sorry
