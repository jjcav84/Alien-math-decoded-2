import IndependentDuodenary.TwelveStateStructure

/-! The complete group of unit-affine permutations on twelve residues. -/
namespace IndependentDuodenary

abbrev AffineStationParameter := (ZMod 12)ˣ × ZMod 12

def affineStationApply (p : AffineStationParameter) (x : ZMod 12) : ZMod 12 :=
  (p.1 : ZMod 12) * x + p.2

def affineStationPermutation (p : AffineStationParameter) : Equiv.Perm (ZMod 12) where
  toFun := affineStationApply p
  invFun x := ((p.1⁻¹ : (ZMod 12)ˣ) : ZMod 12) * (x - p.2)
  left_inv x := by simp [affineStationApply, ← mul_assoc]
  right_inv x := by simp [affineStationApply, ← mul_assoc]

def affineStationCompose (p q : AffineStationParameter) : AffineStationParameter :=
  (p.1 * q.1, (p.1 : ZMod 12) * q.2 + p.2)

def affineStationInverse (p : AffineStationParameter) : AffineStationParameter :=
  (p.1⁻¹, -(((p.1⁻¹ : (ZMod 12)ˣ) : ZMod 12)) * p.2)

theorem affine_station_composition (p q : AffineStationParameter) (x : ZMod 12) :
    affineStationApply (affineStationCompose p q) x =
      affineStationApply p (affineStationApply q x) := by
  simp [affineStationApply, affineStationCompose]
  ring

theorem affine_station_permutation_injective : Function.Injective affineStationPermutation := by
  intro p q h
  have h0 : affineStationApply p 0 = affineStationApply q 0 :=
    congrArg (fun f : Equiv.Perm (ZMod 12) => f 0) h
  have h1 : affineStationApply p 1 = affineStationApply q 1 :=
    congrArg (fun f : Equiv.Perm (ZMod 12) => f 1) h
  have hb : p.2 = q.2 := by simpa [affineStationApply] using h0
  have hv : (p.1 : ZMod 12) + q.2 = (q.1 : ZMod 12) + q.2 := by
    simpa [affineStationApply, hb] using h1
  exact Prod.ext (Units.ext (add_right_cancel hv)) hb

theorem twelve_unit_count : Fintype.card (ZMod 12)ˣ = 4 := by decide

theorem twelve_unit_residues : ∀ u : (ZMod 12)ˣ,
    (u : ZMod 12) = 1 ∨ (u : ZMod 12) = 5 ∨
      (u : ZMod 12) = 7 ∨ (u : ZMod 12) = 11 := by decide

theorem affine_station_parameter_card : Fintype.card AffineStationParameter = 48 := by
  rw [Fintype.card_prod, twelve_unit_count, ZMod.card]

/-- A unit-affine permutation need not preserve polygonal distance. -/
def multiplyFiveParameter : AffineStationParameter :=
  (⟨5, 5, by decide, by decide⟩, 0)

theorem affine_five_changes_cyclic_distance :
    cyclicDistance (affineStationApply multiplyFiveParameter 0)
      (affineStationApply multiplyFiveParameter 1) ≠ cyclicDistance 0 1 := by decide

end IndependentDuodenary
