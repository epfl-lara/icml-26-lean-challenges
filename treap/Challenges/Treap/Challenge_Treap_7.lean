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
  Insert correctness

  Inserting an element adds it to the set of keys of the treap, regardless of whether it was already present or not

-/
theorem insert_inserts_element (t : Treap Key Prio) (ins_kp : KeyPrioPair Key Prio) :
    (Treap.insert t ins_kp).root.all_keys = (t.root.all_keys \ {ins_kp.key}) ∪ {ins_kp.key} := sorry

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
