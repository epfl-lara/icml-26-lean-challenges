/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Isabel Haas, Pratyai Mazumder, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false

/--
`ArrayN α n` is a subtype of `Array α` guaranteeing that the array has exactly size `n`.
This is useful for fixed-size collections where the size is known at type-checking time.
-/
abbrev ArrayN (α : Type) (n : ℕ) := { a : Array α // a.size = n }

/--
Get the element at index `i` from an `ArrayN`.
The index `i` is of type `Fin n`, ensuring it is always within bounds.
-/
def ArrayN.get {α n} (a : ArrayN α n) (i : Fin n) : α :=
  a.val[i]'(by simp only [a.property, Fin.is_lt])

/--
Set the element at index `i` to value `v`, returning a new `ArrayN` of the same size.
-/
def ArrayN.set {α n} (a : ArrayN α n) (i : Fin n) (v : α) : ArrayN α n :=
  ⟨a.val.set i v, by simp_all only [Array.size_set, a.property]⟩

/-- Accessing the index we just set returns the new value. -/
lemma ArrayN.get_set_eq {α n} (a : ArrayN α n) (i : Fin n) (v : α) :
    (a.set i v).get i = v := by
  simp [ArrayN.get, ArrayN.set]

/-- Accessing a different index returns the old value. -/
lemma ArrayN.get_set_ne {α n} (a : ArrayN α n) (i j : Fin n) (v : α) (h : i ≠ j) :
    (a.set i v).get j = a.get j := by
  simp_all [ArrayN.get, ArrayN.set]
  apply Array.getElem_set_ne
  exact Fin.val_ne_of_ne h

/-- Setting two different indices commutes. -/
lemma ArrayN.set_comm {α n} (a : ArrayN α n) (i j : Fin n) (vi vj : α) (h : i ≠ j) :
    (a.set i vi).set j vj = (a.set j vj).set i vi := by
  simp_all [ArrayN.set, Array.set_comm, Fin.val_ne_of_ne]
