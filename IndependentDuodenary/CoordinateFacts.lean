/-!--
Ruling 1 (2026-11-16): native Lean core only; no Batteries or Mathlib.
Minimal finite coordinate encodings and arithmetic facts for the 12/144 model.
-/
namespace IndependentDuodenary.CoordinateFacts

def encode144 (s u : Nat) : Nat := 12 * s + u

def cyclic144 (n : Nat) : Nat := n % 144

def product12 (a b : Nat) : Nat × Nat := (a % 12, b % 12)

def productAdd (x y : Nat × Nat) : Nat × Nat :=
  ((x.1 + y.1) % 12, (x.2 + y.2) % 12)

def productScale (n : Nat) (x : Nat × Nat) : Nat × Nat :=
  ((n * x.1) % 12, (n * x.2) % 12)

def label (s u : Nat) : Nat := (7 + 144 - s + u) % 12

theorem encode144_injective_on_coordinates
    {s₁ u₁ s₂ u₂ : Nat}
    (hs₁ : s₁ < 12) (hu₁ : u₁ < 12)
    (hs₂ : s₂ < 12) (hu₂ : u₂ < 12)
    (h : encode144 s₁ u₁ = encode144 s₂ u₂) :
    s₁ = s₂ ∧ u₁ = u₂ := by
  dsimp [encode144] at h
  constructor <;> omega

theorem cyclic144_twelve_ne_zero : cyclic144 12 ≠ 0 := by
  decide

theorem cyclic144_twelve_is_twelve : cyclic144 (12 * 1) = 12 := by
  decide

theorem product12_scale_twelve_zero (a b : Nat) :
    productScale 12 (product12 a b) = (0, 0) := by
  simp [product12, productScale]

theorem label_nat_subtraction_counterexample :
    label 8 0 ≠ (7 - 8 + 0) % 12 := by
  decide

theorem antipode_unbounded_counterexample :
    (label ((200 + 6) % 12) 0 + 6) % 12 ≠ label 200 0 := by
  decide

theorem antipode_coherence {s u : Nat} (hs : s < 12) :
    (label ((s + 6) % 12) u + 6) % 12 = label s u := by
  dsimp [label]
  omega

/-- A corrected subtraction-free form equivalent to label when s < 12. -/
theorem label_corrected_form {s u : Nat} (hs : s < 12) :
    label s u = (7 + 12 - s + u) % 12 := by
  dsimp [label]
  omega

theorem label_periodic_form {s u : Nat} (hs : s < 12) :
    label s u = (7 + u + 12 - s) % 12 := by
  rw [label_corrected_form hs]
  omega

-- Midpoint congruence is expressed explicitly as equality of residues.
def midpointCongruent (x a b : Nat) : Prop := (2 * x) % 12 = (a + b) % 12

theorem midpoint_congruence_implies_even {a b x : Nat}
    (h : midpointCongruent x a b) : (a + b) % 2 = 0 := by
  dsimp [midpointCongruent] at h
  omega

theorem midpoint_two_witnesses_differ_by_six {a b : Nat}
    (he : (a + b) % 2 = 0) :
    midpointCongruent ((a + b) / 2) a b ∧
    midpointCongruent ((a + b) / 2 + 6) a b ∧
    ((a + b) / 2 + 6) ≠ (a + b) / 2 := by
  constructor
  · dsimp [midpointCongruent]
    omega
  constructor
  · dsimp [midpointCongruent]
    omega
  · omega

theorem midpoint_congruence_iff_even {a b : Nat} :
    (∃ x, midpointCongruent x a b) ↔ (a + b) % 2 = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact midpoint_congruence_implies_even hx
  · intro h
    refine ⟨(a + b) / 2, ?_⟩
    dsimp [midpointCongruent]
    omega

end IndependentDuodenary.CoordinateFacts
