import Aunatural.Natty
import Aunatural.Tactics
import Aunatural.Addition
import Aunatural.Induction

import Mathlib.Tactic
import Mathlib.Tactic.Basic

namespace Natty
open Natty

-- p1
theorem zero_add (n :ℕ) : 0 + n = n := by

  induction n with d hd

  rw [add_zero]

  rfl

  rw [add_succ]

  rw [hd]

  rfl

-- p2 
theorem succ_add (a b : ℕ):
  succ a + b = succ (a + b)
    := by

  induction b with x hx

  rw [add_zero, add_zero]

  rfl

  rw [add_succ, add_succ]

  rw [← hx]

  rfl

/- p3
   Addition is commutative. Meaning `a + b`
   is equal to `b + a`. Assuming a and b are 
   natural numbers. Let's show this.
-/
theorem add_comm (a b: ℕ):
  a + b = b + a := by

  induction b with x hx

  rw [add_zero, zero_add]

  rfl

  rw [add_succ, succ_add, hx]

  rfl

/- p4
   Addition is associative. Assuming we're dealing
   with natural numbers then `(a + b) + c` is the
   same as `a + (b + c)`. Ie grouping doen't matter.
-/
theorem add_assoc (a b: ℕ):
  a + b + c = a + (b + c) := by

  induction b with x hx

  rw [zero_add, add_zero]

  rfl

  rw [add_succ]

  repeat rw [succ_add]

  rw [add_succ]

  rw [← hx]

  rfl

-- p5
theorem add_right_comm ( a b c : ℕ ) : 
  (a + b) + c = (a + c) + b := by

  rw [add_assoc]

  rw [add_assoc]

  rw [add_comm b]

  rfl

