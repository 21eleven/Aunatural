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
