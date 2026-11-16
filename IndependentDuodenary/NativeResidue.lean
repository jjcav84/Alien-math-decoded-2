/-!
# Native residue facts (no Mathlib)

Residue rings are `Fin 12` (Z/12Z) and `Fin 144` (Z/144Z), using core Lean `Fin` arithmetic.
Every statement below is closed (no variables) and proved by `decide` over a finite domain.
Evidence class for each: kernel-proved (finite exhaustive `decide`).
Not covered here: ring-law universals, Z/144 vs Z/12 x Z/12 non-isomorphism (see verification/qwen-jigsaw).
-/
namespace IndependentDuodenary.NativeResidue

theorem twelve_add_wraps : (11 : Fin 12) + 1 = 0 := by decide
theorem twelve_mul_three_four : (3 : Fin 12) * 4 = 0 := by decide
theorem twelve_squared_zero_mod_144 : (12 : Fin 144) * 12 = 0 := by decide
theorem twelve_nonzero_mod_144 : (12 : Fin 144) ≠ 0 := by decide
theorem neg_one_twelve : (11 : Fin 12) = 0 - 1 := by decide

end IndependentDuodenary.NativeResidue
