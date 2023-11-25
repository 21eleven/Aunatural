import Aunatural.Natty

namespace Natty
open Natty

/--
`add_zero a` is a proof of `a + 0 = a`.

`add_zero` is a `simp` lemma, because if you see `a + 0`
you usually want to simplify it to `a`.
-/
@[simp]
axiom add_zero (a : Natty) : a + 0 = a

/--
If `a` and `d` are natural numbers, then `add_succ a d` is the proof that
`a + succ d = succ (a + d)`.
-/
axiom add_succ (a d : Natty) : a + (Natty.succ d) = succ (a + d)


-- some theorems about succ since succ is like addition
theorem one_eq_succ_zero : 1 = succ 0 := by rfl
theorem two_eq_succ_one : 2 = succ 1 := by rfl
theorem three_eq_succ_two: 3 = succ 2 := by rfl
theorem four_eq_succ_three: 4 = succ 3 := by rfl
