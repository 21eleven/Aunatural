/-- These Natural Numbers are Au Natural 😮-/
inductive Natty where
  | zero : Natty
  | succ : Natty → Natty
-- deriving BEq, DecidableEq, Inhabited

@[inherit_doc]
notation (name := NattyNotation) (priority := 1000000) "ℕ" => Natty

namespace Natty

instance : Inhabited Natty where 
  default := Natty.zero

-- @[Natty_decide] -- see NNG4 Game.Tactic.LabelAttr MyNat_decide attribute
def fromNat (x : Nat) : Natty :=
  -- should call this ofNat maybe
  match x with
  | Nat.zero => Natty.zero
  | Nat.succ w => Natty.succ (fromNat w)

def toNat (x : Natty) : Nat :=
  match x with
  | Natty.zero => Nat.zero
  | Natty.succ w => Nat.succ (toNat w)

instance instOfNat (n : Nat) : OfNat Natty n where
  ofNat := fromNat n

instance : ToString Natty where
  toString n := toString (toNat n)

-- dummy addition
opaque add : Natty → Natty → Natty

instance instAdd : Add Natty where
  add := Natty.add

-- dummy multiplication
opaque mul : Natty → Natty → Natty

instance : Mul Natty where
  mul := Natty.mul

theorem zero_eq_0 : Natty.zero = 0 := rfl

def one : Natty := Natty.succ 0

-- see https://github.com/leanprover-community/NNG4/blob/main/Game/MyNat/Definition.lean#L42
attribute [-simp] Natty.succ.injEq


