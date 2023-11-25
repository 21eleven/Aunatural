import Aunatural.Natty
import Aunatural.Tactics
import Aunatural.Addition

-- import needed to recognize `lemma`
import Mathlib.Tactic.Basic

namespace Natty
open Natty

lemma p1 (x y z : Natty) : x * y + z = x * y + z := by
  rfl


lemma p2 (x y : Natty) (h : y = x + 7): 2 * y = 2 * (x + 7) := by

  rw [h]

  rfl

lemma p3 : 2 = succ (succ 0) := by

  rw [← one_eq_succ_zero]

  rw [← two_eq_succ_one]

  rfl

lemma p3dot5 (a b : Natty) (h : (succ a) = b): succ b = succ (succ a) := by

  rw [h]

  rfl


