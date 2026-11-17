import IndependentDuodenary.Native.Foundations

/-! Mathlib-free ZMod: Equiv structure, Fintype utilities, Nat.card shims. -/

/-- Equiv structure (not in Lean 4 core Init). -/
structure Equiv (α : Sort u) (β : Sort v) where
  toFun    : α → β
  invFun   : β → α
  left_inv  : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun

infixl:25 " ≃ " => Equiv

namespace Equiv

instance : CoeFun (α ≃ β) (fun _ => α → β) := ⟨Equiv.toFun⟩

@[simp]
theorem coe_mk (f : α → β) (g l r) : (⟨f, g, l, r⟩ : α ≃ β) x = f x := rfl

protected def refl (α : Sort u) : α ≃ α where
  toFun    := id; invFun := id
  left_inv  := fun _ => rfl; right_inv := fun _ => rfl

protected def symm (e : α ≃ β) : β ≃ α where
  toFun    := e.invFun; invFun := e.toFun
  left_inv  := e.right_inv; right_inv := e.left_inv

protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ where
  toFun    := e₂ ∘ e₁; invFun := e₁.invFun ∘ e₂.invFun
  left_inv a := by
    change e₁.invFun (e₂.invFun (e₂ (e₁ a))) = a
    rw [e₂.left_inv, e₁.left_inv]
  right_inv c := by
    change e₂ (e₁ (e₁.invFun (e₂.invFun c))) = c
    rw [e₁.right_inv, e₂.right_inv]

theorem apply_symm_apply (e : α ≃ β) (b : β) : e (e.symm b) = b := e.right_inv b
theorem symm_apply_apply (e : α ≃ β) (a : α) : e.symm (e a) = a := e.left_inv a

@[simp] theorem symm_symm (e : α ≃ β) : e.symm.symm = e := by cases e; rfl

theorem injective (e : α ≃ β) : Function.Injective e := fun a b h => by
  have := congr_arg e.symm h; rwa [e.symm_apply_apply, e.symm_apply_apply] at this

theorem surjective (e : α ≃ β) : Function.Surjective e :=
  fun b => ⟨e.symm b, e.apply_symm_apply b⟩

theorem bijective (e : α ≃ β) : Function.Bijective e := ⟨e.injective, e.surjective⟩

/-- Embedding from an equivalence. -/
def toEmbedding (e : α ≃ β) : α ↪ β := ⟨e, e.injective⟩

noncomputable def ofBijective (f : α → β) (hf : Function.Bijective f) : α ≃ β where
  toFun    := f
  invFun   := fun b => Classical.choose (hf.surjective b)
  left_inv := fun a => hf.injective (Classical.choose_spec (hf.surjective (f a)))
  right_inv := fun b => Classical.choose_spec (hf.surjective b)

end Equiv

abbrev ZMod (n : Nat) := Fin n

namespace ZMod
@[simp] theorem card (n : Nat) : Fintype.card (ZMod n) = n := Fintype.card_fin n
end ZMod

/-- Transfer a Fintype instance along an equivalence. -/
def Fintype.ofEquiv (α : Type*) {β : Type*} [h : Fintype α] (e : α ≃ β) : Fintype β where
  elems    := h.elems.map e.toEmbedding
  complete b := by
    simp only [Finset.mem_map, Equiv.toEmbedding, Function.Embedding.coeFn_mk]
    exact ⟨e.symm b, h.complete _, e.apply_symm_apply b⟩

/-- Equivalent types have equal Fintype.card (uses card_le_of_injective from core). -/
theorem Fintype.card_congr {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    Fintype.card α = Fintype.card β :=
  Nat.le_antisymm
    (Fintype.card_le_of_injective e e.injective)
    (Fintype.card_le_of_injective e.symm e.symm.injective)

/-- A surjection witnesses card β ≤ card α (classical choice picks a right inverse). -/
noncomputable def Fintype.card_le_of_surjective {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Surjective f) : Fintype.card β ≤ Fintype.card α :=
  Fintype.card_le_of_injective (fun b => Classical.choose (hf b)) fun b₁ b₂ h => by
    have h₁ := Classical.choose_spec (hf b₁)
    have h₂ := Classical.choose_spec (hf b₂)
    calc b₁ = f (Classical.choose (hf b₁)) := h₁.symm
      _ = f (Classical.choose (hf b₂)) := by rw [h]
      _ = b₂ := h₂

-- All Fintype instances for the same type give the same elems/card.
instance instFintypeSubsingleton {α : Type*} : Subsingleton (Fintype α) :=
  ⟨fun ⟨s1, h1⟩ ⟨s2, h2⟩ => by
    congr 1; ext x; exact ⟨fun _ => h2 x, fun _ => h1 x⟩⟩

noncomputable def Nat.card (α : Type*) : Nat :=
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

theorem Nat.card_fin (n : Nat) : Nat.card (Fin n) = n := by
  simp [Nat.card_eq_fintype_card]

@[simp]
theorem Nat.card_fun {α β : Type*} [Fintype α] [Fintype β] :
    Nat.card (α → β) = Nat.card β ^ Nat.card α := by
  simp [Nat.card_eq_fintype_card, Fintype.card_fun]
