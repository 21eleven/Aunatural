import Aunatural.Natty

-- import needed to recognize `lemma`
import Mathlib.Tactic.Basic

namespace Natty
open Natty
/-
if we don't set the namespace then in p1 we have:
  ▶ 5:28-5:33: error:
  failed to synthesize instance
    HMul Natty Natty ?m.33
-/

lemma p1 (x y z : Natty) : x * y + z = x * y + z := by
  rfl


lemma p2 (x y : Natty) (h : y = x + 7): 2 * y = 2 * (x + 7) := by
  rewrite [h]
  rfl

lemma p3 : 2 = succ (succ 0) := by
  rfl
  /-
    not sure why it don't say:
      equality lhs
        2
      is not definitionally equal to rhs
        succ (succ 0)
      ⊢ 2 = succ (succ 0)
    like it does on the natural number game website
  -/

lemma p3dot5 (a b : Natty) (h : (succ a) = b): succ b = succ (succ a) := by
  rewrite [h]
  rfl


