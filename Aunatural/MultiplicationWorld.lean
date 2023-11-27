import Aunatural.Natty
import Aunatural.Tactics
import Aunatural.Induction
import Aunatural.Addition
-- add_zero : a + 0 = a
-- add_succ : a + (succ b) = succ (a + b)
-- 1-4 eq succ prior theorems
-- succ_eq_add_one
import Aunatural.Multiplication
-- mul_zero : a * 0 = 0
-- mul_succ : a * (succ b) = a * b + a
import Aunatural.AdditionWorld
-- zero_add : 0 + n = n
-- succ_add : succ a + b = succ (a + b)
-- add_comm : a + b = b + a
-- add_assoc : (a + b) + c = a + (b + c)
-- add_right_comm : (a + b) + c = (a + c) + b

import Mathlib.Tactic
import Mathlib.Tactic.Basic

namespace Natty
open Natty

-- p1
theorem mul_one (n: ℕ): n * 1 = n := by
  
  rw [one_eq_succ_zero]
  
  rw [mul_succ]

  rw [mul_zero, zero_add]
  
  rfl

-- p2
theorem zero_mul (n : ℕ): 0 * n = 0 := by

  induction n with x hx

  rw [mul_zero]

  rfl

  rw [mul_succ]

  rw [add_zero, hx]

  rfl

-- p3
theorem succ_mul (a b: ℕ):
  (succ a) * b = a * b + b := by

  induction b with x hx

  rw [add_zero]

  repeat rw [mul_zero]

  rfl

  rw [mul_succ]
  
  nth_rewrite 2 [succ_eq_add_one x]

  rw [← add_assoc]

  rw [mul_succ]

  rw [add_right_comm (a * x) a x]

  rw [hx]

  rw [succ_eq_add_one]

  rw [← add_assoc]

  rfl











