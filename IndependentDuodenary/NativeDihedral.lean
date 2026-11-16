import IndependentDuodenary.NativeZMod

/-! Mathlib-free DihedralGroup: inductive type, Group instance, Fintype, card. -/

inductive DihedralGroup (n : Nat) : Type
  | r  : ZMod n → DihedralGroup n
  | sr : ZMod n → DihedralGroup n
  deriving DecidableEq, Repr

namespace DihedralGroup

private def mul' {n : Nat} : DihedralGroup n → DihedralGroup n → DihedralGroup n
  | .r i,  .r j  => .r (i + j)
  | .r i,  .sr j => .sr (j - i)
  | .sr i, .r j  => .sr (i + j)
  | .sr i, .sr j => .r (j - i)

private def inv' {n : Nat} : DihedralGroup n → DihedralGroup n
  | .r i  => .r (-i)
  | .sr i => .sr i

instance (n : Nat) : Mul (DihedralGroup n) := ⟨mul'⟩
instance (n : Nat) : One (DihedralGroup n) := ⟨.r 0⟩
instance (n : Nat) : Inv (DihedralGroup n) := ⟨inv'⟩

@[simp] theorem one_def {n : Nat} : (1 : DihedralGroup n) = DihedralGroup.r 0 := rfl

instance (n : Nat) : Group (DihedralGroup n) where
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;>
      simp only [HMul.hMul, Mul.mul, mul'] <;>
      congr 1 <;> ring
  one_mul a := by
    cases a <;> simp [HMul.hMul, Mul.mul, mul', OfNat.ofNat, One.one]
  mul_one a := by
    cases a <;> simp [HMul.hMul, Mul.mul, mul', OfNat.ofNat, One.one]
  inv_mul_cancel a := by
    cases a <;>
      simp [HMul.hMul, Mul.mul, mul', Inv.inv, inv', OfNat.ofNat, One.one,
            neg_add_cancel, sub_self]

-- Equiv to Bool × Fin n for Fintype/card.
def toEquiv (n : Nat) : DihedralGroup n ≃ Bool × Fin n where
  toFun := fun g => match g with
    | .r  k => (false, k)
    | .sr k => (true,  k)
  invFun := fun ⟨b, k⟩ => if b then .sr k else .r k
  left_inv := by intro g; cases g <;> simp
  right_inv := by intro ⟨b, k⟩; cases b <;> simp

instance (n : Nat) : Fintype (DihedralGroup n) :=
  Fintype.ofEquiv _ (toEquiv n).symm

theorem card (n : Nat) : Fintype.card (DihedralGroup n) = 2 * n := by
  rw [Fintype.card_congr (toEquiv n)]
  simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]

end DihedralGroup
