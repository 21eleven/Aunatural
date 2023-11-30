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
-- import Aunatural.MultiplicationWorld
-- mul_one : n * 1 = n
-- zero_mul 0 * n = 0
-- succ_mul : (succ a) * b = a * b + b
-- mul_comm : a * b = b * a
-- one_mul : 1 * n = n


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

theorem mul_comm (a b: ℕ): a * b = b * a := by

  induction b with x hx
  
  rw [zero_mul, mul_zero]

  rfl

  rw [succ_mul, mul_succ, hx]

  rfl

theorem one_mul (n: ℕ): 1 * n = n := by

  induction n with x hx

  rw [mul_zero]

  rfl

  rw [mul_succ]

  rw [succ_eq_add_one]
  
  rw [hx]

  rfl

theorem two_mul (m: ℕ): 2 * m = m + m := by 

  induction m with x hx

  rw [mul_zero, add_zero]

  rfl

  rw [mul_succ]

  rw [succ_add]

  rw [succ_eq_add_one]

  rw [add_succ]

  rw [succ_eq_add_one]

  rw [hx]

  rw [two_eq_succ_one]

  rw [← succ_eq_add_one]

  rw [add_comm, succ_add]

  rw [← add_assoc]

  rw [add_comm 1 x]

  rw [add_right_comm]

  rfl

theorem mul_add (a b c : ℕ) :
  a * (b + c) = a * b + a * c := by

  induction a with x hx

  repeat rw [zero_mul]

  rw [add_zero]

  rfl

  repeat rw [succ_mul]

  rw [hx]

  rw [add_right_comm (x * b) b]

  rw [← add_assoc (x * b)]

  rw [add_assoc _ c]

  rw [add_comm b]

  rfl

-- can be proved w induction or w/o induction
theorem add_mul (a b c : ℕ):
  (a + b) * c = a * c + b * c := by

  rw [mul_comm]

  rw [mul_add]
  
  repeat rw [mul_comm c]

  rfl












  












