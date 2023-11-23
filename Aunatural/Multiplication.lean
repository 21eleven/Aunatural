import Aunatural.Natty

namespace Natty

axiom mul_zero (a : Natty) : a * 0 = 0

axiom mul_succ (a b : Natty) : a * (succ b) = a * b + a
