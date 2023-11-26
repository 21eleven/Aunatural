import Aunatural.Natty
import Aunatural.Tactics
import Aunatural.Addition

-- import needed for nth_rewrite
import Mathlib.Tactic

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

  rw [two_eq_succ_one]

  rw [one_eq_succ_zero]

  rfl

lemma p3dot5 (a b : Natty) (h : (succ a) = b): succ b = succ (succ a) := by

  rw [h]

  rfl


lemma p4 : 2 = succ (succ 0) := by

  rw [← one_eq_succ_zero]

  rw [← two_eq_succ_one]

  rfl

lemma p5 (a b c : ℕ) :
  a + (b + 0) + (c + 0) = a + b + c := by

  -- rw [add_zero]
  --
  -- rw [add_zero]

  repeat rw [add_zero]

  rfl

/- note how we can supply an argument to functions
   passed to `rw` -/
lemma p6 (a b c : ℕ) :
  a + (b + 0) + (c + 0) = a + b + c := by

  rw [add_zero c]

  rw [add_zero]

  rfl

lemma p7 (n : ℕ) : succ n = n + 1 := by

  rw [one_eq_succ_zero]

  rw [add_succ]

  rw [add_zero]

  rfl


lemma p8 : 2 + 2  = (4 : ℕ) := by

  rw [four_eq_succ_three]

  rw [three_eq_succ_two]

  nth_rewrite 3 [← add_zero 2]

  repeat rw [← add_succ]

  rw [← one_eq_succ_zero]

  rw [← two_eq_succ_one]

  rfl

