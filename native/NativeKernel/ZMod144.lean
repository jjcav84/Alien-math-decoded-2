-- native/NativeKernel/ZMod144.lean
-- Core-only modular arithmetic, reduction homomorphisms, and ring-law lemmas for Z/144Z and Z/12Z

namespace NativeKernel

abbrev ZMod12 := Fin 12
abbrev ZMod144 := Fin 144

def add144 (a b : ZMod144) : ZMod144 :=
  ⟨(a.val + b.val) % 144, by
    have ha : a.val < 144 := a.isLt
    have hb : b.val < 144 := b.isLt
    exact Nat.mod_lt _ (by decide)⟩

def mul144 (a b : ZMod144) : ZMod144 :=
  ⟨(a.val * b.val) % 144, by
    have ha : a.val < 144 := a.isLt
    have hb : b.val < 144 := b.isLt
    exact Nat.mod_lt _ (by decide)⟩

-- Reduction mapping from Fin 144 to Fin 12 (mod 12 projection)
def reduce144To12 (a : ZMod144) : ZMod12 :=
  ⟨a.val % 12, by
    have ha : a.val < 144 := a.isLt
    exact Nat.mod_lt _ (by decide)⟩

theorem add144_comm (a b : ZMod144) : add144 a b = add144 b a := by
  ext
  dsimp [add144]
  rw [Nat.add_comm]

theorem reduce_hom_add (a b : ZMod144) :
    (reduce144To12 (add144 a b)).val = ((reduce144To12 a).val + (reduce144To12 b).val) % 12 := by
  dsimp [reduce144To12, add144]
  have h12 : 12 ∣ 144 := by decide
  rw [Nat.mod_mod_of_dvd _ h12]
  exact Nat.add_mod a.val b.val 12

-- Multiplicative reduction lemma for duodenary closure
theorem reduce_hom_mul (a b : ZMod144) :
    (reduce144To12 (mul144 a b)).val = ((reduce144To12 a).val * (reduce144To12 b).val) % 12 := by
  dsimp [reduce144To12, mul144]
  have h12 : 12 ∣ 144 := by decide
  rw [Nat.mod_mod_of_dvd _ h12]
  exact Nat.mul_mod a.val b.val 12

theorem mul144_comm (a b : ZMod144) : mul144 a b = mul144 b a := by
  ext
  dsimp [mul144]
  rw [Nat.mul_comm]

end NativeKernel
