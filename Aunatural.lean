-- This module serves as the root of the `Aunatural` library.
-- Import modules here that should be built as part of the library.
import «Aunatural».Basic
import Aunatural.Natty

#eval hello

example (x : Nat) : x = x := by
  rfl

example
  (x y : Nat)
  (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
    rw [h]

#eval Nat.succ 1

theorem one_eq_succ_zero : 1 = Nat.succ 0 := by
  rfl

example : 2 = Nat.succ (Nat.succ 0) := by
  rfl


