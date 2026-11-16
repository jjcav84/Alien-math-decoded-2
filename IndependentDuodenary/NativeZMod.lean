/-! Mathlib-free ZMod: abbrev to Fin, Nat.card, and compatibility shims. -/

abbrev ZMod (n : ℕ) := Fin n

namespace ZMod

@[simp] theorem card (n : ℕ) : Fintype.card (ZMod n) = n := Fintype.card_fin n

end ZMod

-- Fintype is a subsingleton (all instances give the same elems/card).
instance instFintypeSubsingleton {α : Type*} : Subsingleton (Fintype α) :=
  ⟨fun ⟨s1, h1⟩ ⟨s2, h2⟩ => by
    congr 1; ext x; exact ⟨fun _ => h2 x, fun _ => h1 x⟩⟩

noncomputable def Nat.card (α : Type*) : ℕ :=
  if h : Nonempty (Fintype α) then
    haveI : Fintype α := h.some
    Fintype.card α
  else 0

@[simp]
theorem Nat.card_eq_fintype_card {α : Type*} [Fintype α] : Nat.card α = Fintype.card α := by
  simp only [Nat.card, dif_pos ⟨‹Fintype α›⟩]
  congr 1
  exact Subsingleton.elim _ _

theorem Nat.card_congr {α β : Type*} (e : α ≃ β) : Nat.card α = Nat.card β := by
  by_cases hα : Nonempty (Fintype α)
  · have hβ : Nonempty (Fintype β) := ⟨Fintype.ofEquiv α e⟩
    haveI : Fintype α := hα.some
    haveI : Fintype β := hβ.some
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_congr e
  · have hβ : ¬Nonempty (Fintype β) := by
      intro ⟨hb⟩; exact hα ⟨Fintype.ofEquiv β e.symm⟩
    simp [Nat.card, dif_neg hα, dif_neg hβ]

theorem Nat.card_fin (n : ℕ) : Nat.card (Fin n) = n := by
  simp [Nat.card_eq_fintype_card]

@[simp]
theorem Nat.card_fun {α β : Type*} [Fintype α] [Fintype β] :
    Nat.card (α → β) = Nat.card β ^ Nat.card α := by
  simp [Nat.card_eq_fintype_card, Fintype.card_fun]

noncomputable def Equiv.ofBijective {α β : Type*} (f : α → β)
    (hf : Function.Bijective f) : α ≃ β where
  toFun := f
  invFun b := Classical.choose (hf.surjective b)
  left_inv a := hf.injective (Classical.choose_spec (hf.surjective (f a)))
  right_inv b := Classical.choose_spec (hf.surjective b)
