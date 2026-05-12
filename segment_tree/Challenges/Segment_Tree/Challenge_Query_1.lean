/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carmen Casulli, Fabio Giovanazzi, Sorrachai Yingchareonthawornchai
-/

import Challenges.Segment_Tree.Def_Query

namespace Cslib.Algorithms.Lean.TimeM

set_option autoImplicit false

-- QUERY OPERATION:
-- query function: given an interval [p, q), if we call p1:=max(0, p) and q1:=min(q, st.m)
-- and denote with leaf[] the bottom layer of the tree (= a[m] to a[2m-1]),
-- it returns the result of the computation leaf[p1] * leaf[p1+1] * .... * leaf[q1-2] * leaf[q1-1],
-- or the identity element if q1 ≤ p1

-- the query starts by calling query_aux from the root (j=1) and operates recursively:
-- at each node, if its coverage interval is entirely contained in the query interval, it returns the value stored at that node,
-- otherwise, if the two intervals are disjoint, it returns the identity element,
-- lastly, if the two have a proper intersection, the function will query the children of node j, and aggregate their answers

theorem query_correctness (α : Type) (inst : Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) :
    (query α n st p q).ret =
      (st.a.toArray.extract (st.m + p) (st.m + q)).foldl (fun a b => a * b) 1 := sorry

end Cslib.Algorithms.Lean.TimeM
