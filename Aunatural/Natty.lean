import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases

namespace NattyOrig
open NattyOrig

inductive Natty where
  | zero : Natty
  | succ : Natty → Natty
  deriving BEq, DecidableEq, Inhabited 
  -- deriving Inhabited 

-- Inhabited:default is the value you get when you try to
-- get a value out of an array of type α but there is no value
-- at the index so it returns some default of type α. Apparently
-- this is required for "consistency" in lean
instance : Inhabited Natty where
  default := Natty.zero

def nattyFromNat (x : Nat) : Natty :=
  match x with
  | Nat.zero => Natty.zero
  -- w preceeds x
  | Nat.succ w => Natty.succ (nattyFromNat w)

def natFromNatty (x : Natty) : Nat :=
  match x with
  | Natty.zero => Nat.zero
  | Natty.succ w => Nat.succ (natFromNatty w)

instance : OfNat Natty n where
  ofNat := nattyFromNat n

instance : ToString Natty where
  toString some_natty := toString (natFromNatty some_natty)

def Natty.add : Natty → Natty → Natty 
  | a, 0 => a
  | a, Natty.succ b => Natty.succ (Natty.add a b)

instance : Add Natty where  
  add := Natty.add

def Natty.mul : Natty → Natty → Natty 
  | _, 0 => 0
  | a, Natty.succ b => Natty.add a (Natty.mul a b)
  -- the following is a redudant alternative:
  -- | a, b + 1 => a + (Natty.mul a b)

instance : Mul Natty where
  mul := Natty.mul

theorem zero_is_0 : Natty.zero = 0 := by rfl 

def one : Natty := Natty.succ 0 

-- commenting out as we named the namespace to Natty orig
-- theorem one_is_1 : Natty.one = 1 := by rfl


