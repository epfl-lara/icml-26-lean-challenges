/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Collodel, Sorrachai Yingchareonthawornchai
-/

import Challenges.Treap.Def_TreapComposite

namespace Cslib.Algorithms.Lean.TimeM
namespace TreapLogic
open Tree

variable {Key : Type} [LinearOrder Key]
variable {Prio : Type} [LinearOrder Prio]

/-
  Find correctness

  Find k returns a key-priority pair with key k iff k is present in the treap

-/
theorem find_finds_element (t : Treap Key Prio) (k : Key) :
    get_key (Treap.find t k) = some k ↔ k ∈ t.root.all_keys := sorry

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
