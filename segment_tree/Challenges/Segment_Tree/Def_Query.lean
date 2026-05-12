/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carmen Casulli, Fabio Giovanazzi, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Challenges.Segment_Tree.Challenge_CoverageIntervalDefs
import Challenges.Segment_Tree.Def_SegmentTree
import Cslib.Algorithms.Lean.TimeM


namespace Cslib.Algorithms.Lean.TimeM

-- QUERY OPERATION:
-- query function: given an interval [p, q), if we call p1:=max(0, p) and q1:=min(q, st.m)
-- and denote with leaf[] the bottom layer of the tree (= a[m] to a[2m-1]),
-- it returns the result of the computation leaf[p1] * leaf[p1+1] * .... * leaf[q1-2] * leaf[q1-1],
-- or the identity element if q1 ≤ p1

-- the query starts by calling query_aux from the root (j=1) and operates recursively:
-- at each node, if its coverage interval is entirely contained in the query interval, it returns the value stored at that node,
-- otherwise, if the two intervals are disjoint, it returns the identity element,
-- lastly, if the two have a proper intersection, the function will query the children of node j, and aggregate their answers


def query (α : Type) [inst: Monoid α] (n : ℕ) (st : SegmentTree α n) (p q : ℕ) : TimeM α :=
  query_aux 1 0 st.m   where query_aux (j L R: ℕ) (h_j0 : j > 0 := by omega) : TimeM α := do
    if h_j2m : j < 2*st.m then
      if h_sub : p ≤ L ∧ R ≤ q then   -- the coverage interval is a subinterval of the query interval
        ✓ return st.a.get ⟨j, h_j2m⟩
      else if h_disjoint : q ≤ L ∨ R ≤ p then   -- the two intervals are disjoint
        ✓ return inst.one
      else -- if we got to this case, (j is not a leaf and) the two intervals have a proper, non-empty intersection
        let C := (L+R)/2
        let left ← query_aux (2*j) L C
        let right ← query_aux (2*j + 1) C R
        ✓ return left * right
    else ✓ return inst.one

end Cslib.Algorithms.Lean.TimeM
