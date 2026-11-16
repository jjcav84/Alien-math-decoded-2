-- native/NativeKernel/ZMod.lean
-- Core-only modular arithmetic for Z/12Z and Z/144Z using native Fin types

namespace NativeKernel

abbrev ZMod12 := Fin 12
abbrev ZMod144 := Fin 144

def add12 (a b : ZMod12) : ZMod12 :=
  ⟨(a.val + b.val) % 12, by
    -- Proof that sum modulo 12 is strictly less than 12
    have ha : a.val < 12 := a.isLt
    have hb : b.val < 12 := b.isLt
    exact Nat.mod_lt _ (by decide)⟩

def mul12 (a b : ZMod12) : ZMod12 :=
  ⟨(a.val * b.val) % 12, by
    have ha : a.val < 12 := a.isLt
    have hb : b.val < 12 := b.isLt
    exact Nat.mod_lt _ (by decide)⟩

theorem add12_comm (a b : ZMod12) : add12 a b = add12 b a := by
  ext
  dsimp [add12]
  rw [Nat.add_comm]

theorem zero_add12 (a : ZMod12) : add12 ⟨0, by decide⟩ a = a := by
  ext
  dsimp [add12]
  rw [Nat.zero_add]
  exact Nat.mod_eq_of_lt a.isLt

theorem add12_assoc (a b c : ZMod12) : add12 (add12 a b) c = add12 a (add12 b c) := by
  ext
  dsimp [add12]
  have ha : a.val < 12 := a.isLt
  have hb : b.val < 12 := b.isLt
  have hc : c.val < 12 := c.isLt
  omega

theorem add12_zero (a : ZMod12) : add12 a ⟨0, by decide⟩ = a := by
  ext
  dsimp [add12]
  have ha : a.val < 12 := a.isLt
  omega

theorem mul12_one (a : ZMod12) : mul12 a ⟨1, by decide⟩ = a := by
  ext
  dsimp [mul12]
  have ha : a.val < 12 := a.isLt
  omega

theorem mul_mod_mod12 (a x : Nat) : a * (x % 12) % 12 = a * x % 12 := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem mul12_add (a b c : ZMod12) : mul12 a (add12 b c) = add12 (mul12 a b) (mul12 a c) := by
  ext
  dsimp [mul12, add12]
  rw [mul_mod_mod12, Nat.left_distrib, Nat.add_mod]

end NativeKernel
