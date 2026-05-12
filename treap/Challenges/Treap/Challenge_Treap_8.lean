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
  Delete correctness

  Deleting an element removes it from the set of keys of the treap, if it was present

-/
theorem delete_deletes_element (t : Treap Key Prio) (del_key : Key) :
    (Treap.delete t del_key).root.all_keys = t.root.all_keys \ {del_key} := sorry

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
