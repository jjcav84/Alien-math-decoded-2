/-! Mathlib-free ZMod: Equiv structure, Fintype utilities, Nat.card shims. -/

-- =========================================================
-- Section 1: Equiv  (Function.LeftInverse not in Lean 4 core Init)
-- =========================================================

structure Equiv (α : Sort u) (β : Sort v) where
  toFun    : α → β
  invFun   : β → α
  left_inv  : ∀ a : α, invFun (toFun a) = a
  right_inv : ∀ b : β, toFun (invFun b) = b

infixl:25 " ≃ " => Equiv

namespace Equiv

instance : CoeFun (α ≃ β) (fun _ => α → β) := ⟨Equiv.toFun⟩

@[simp]
theorem coe_mk (f : α → β) (g l r) : (⟨f, g, l, r⟩ : α ≃ β) x = f x := rfl

protected def refl (α : Sort*) : α ≃ α where
  toFun := id; invFun := id
  left_inv := fun _ => rfl; right_inv := fun _ => rfl

protected def symm (e : α ≃ β) : β ≃ α where
  toFun := e.invFun; invFun := e.toFun
  left_inv := e.right_inv; right_inv := e.left_inv

protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ where
  toFun := e₂ ∘ e₁; invFun := e₁.invFun ∘ e₂.invFun
  left_inv  a := by simp [Function.comp, e₂.left_inv, e₁.left_inv]
  right_inv c := by simp [Function.comp, e₁.right_inv, e₂.right_inv]

theorem apply_symm_apply (e : α ≃ β) (b : β) : e (e.symm b) = b := e.right_inv b
theorem symm_apply_apply (e : α ≃ β) (a : α) : e.symm (e a) = a := e.left_inv a

@[simp] theorem symm_symm (e : α ≃ β) : e.symm.symm = e := by cases e; rfl

theorem injective (e : α ≃ β) : Function.Injective e := fun a b h => by
  have := congrArg e.symm h; rwa [e.symm_apply_apply, e.symm_apply_apply] at this

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

-- =========================================================
-- Section 2: ZMod abbreviation
-- =========================================================

abbrev ZMod (n : Nat) := Fin n

-- =========================================================
-- Section 3: Fin enumeration helpers
-- =========================================================

/-- The list of all elements of Fin n, in order 0, 1, ..., n-1. -/
private def finElems : (n : Nat) → List (Fin n)
  | 0     => []
  | n + 1 => Fin.last n :: (finElems n).map Fin.castSucc

private theorem fin_castSucc_injective {n : Nat} : Function.Injective (@Fin.castSucc n) :=
  fun a b h => Fin.ext (congrArg Fin.val h)

private theorem fin_castSucc_ne_last {n : Nat} (a : Fin n) : Fin.castSucc a ≠ Fin.last n :=
  fun h => Nat.lt_irrefl n (congrArg Fin.val h ▸ a.isLt)

private theorem finElems_nodup : (n : Nat) → (finElems n).Nodup
  | 0     => List.nodup_nil
  | n + 1 => by
      simp only [finElems, List.nodup_cons, List.mem_map]
      exact ⟨fun ⟨a, _, ha⟩ => fin_castSucc_ne_last a ha.symm,
             List.nodup_map fin_castSucc_injective (finElems_nodup n)⟩

private theorem finElems_complete : (n : Nat) → ∀ (i : Fin n), i ∈ finElems n
  | 0,     ⟨_, h⟩  => absurd h (Nat.not_lt_zero _)
  | n + 1, ⟨i, hi⟩ => by
      simp only [finElems, List.mem_cons, List.mem_map]
      by_cases h : i < n
      · exact Or.inr ⟨⟨i, h⟩, finElems_complete n ⟨i, h⟩, rfl⟩
      · exact Or.inl (Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp hi) (Nat.not_lt.mp h)))

private theorem finElems_length : (n : Nat) → (finElems n).length = n
  | 0     => rfl
  | n + 1 => by simp [finElems, List.length_map, finElems_length n]

-- =========================================================
-- Section 4: Fintype class (not in Lean 4 core Init)
-- =========================================================

/-- A type is Fintype if it has a finite list of all its elements. -/
class Fintype (α : Type*) where
  elems    : Finset α
  complete : ∀ x : α, x ∈ elems

namespace Fintype

/-- The cardinality of a finite type. -/
def card (α : Type*) [h : Fintype α] : Nat := h.elems.card

end Fintype

-- =========================================================
-- Section 5: Finset.univ and related
-- =========================================================

def Finset.univ {α : Type*} [h : Fintype α] : Finset α := h.elems

@[simp]
theorem Finset.mem_univ {α : Type*} [Fintype α] (x : α) : x ∈ (Finset.univ : Finset α) :=
  Fintype.instFintype.complete x

theorem Finset.subset_univ {α : Type*} [Fintype α] (s : Finset α) : s ⊆ Finset.univ :=
  fun _ _ => Finset.mem_univ _

theorem Finset.card_univ {α : Type*} [Fintype α] : (Finset.univ : Finset α).card = Fintype.card α :=
  rfl

theorem Finset.eq_univ_of_card {α : Type*} [Fintype α] (s : Finset α) (h : s.card = Fintype.card α) :
    s = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ s)
  rw [Finset.card_univ]; exact le_of_eq h.symm

-- =========================================================
-- Section 6: Fintype instances
-- =========================================================

/-- Fin n has a Fintype instance; elems is {0, 1, ..., n-1}. -/
instance instFintypeFin (n : Nat) : Fintype (Fin n) where
  elems    := ⟨finElems n, finElems_nodup n⟩
  complete := finElems_complete n

instance instFintypeEmpty : Fintype Empty where
  elems    := ∅
  complete := fun x => x.elim

instance instFintypeUnit : Fintype Unit where
  elems    := {()}
  complete := fun _ => Finset.mem_singleton.mpr rfl

instance instFintypeBool : Fintype Bool where
  elems    := {false, true}
  complete := fun | false => Finset.mem_insert.mpr (Or.inl rfl)
               | true  => Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))

instance instFintypeProd {α β : Type*} [Fintype α] [Fintype β] : Fintype (α × β) where
  elems    := Finset.univ ×ˢ Finset.univ
  complete := fun ⟨a, b⟩ => Finset.mem_product.mpr ⟨Finset.mem_univ a, Finset.mem_univ b⟩

-- =========================================================
-- Section 7: Fintype.card lemmas
-- =========================================================

@[simp]
theorem Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n := by
  simp only [Fintype.card, instFintypeFin, Finset.card]
  exact finElems_length n

@[simp]
theorem Fintype.card_empty : Fintype.card Empty = 0 := rfl

@[simp]
theorem Fintype.card_unit : Fintype.card Unit = 1 := rfl

@[simp]
theorem Fintype.card_bool : Fintype.card Bool = 2 := rfl

@[simp]
theorem Fintype.card_prod {α β : Type*} [Fintype α] [Fintype β] :
    Fintype.card (α × β) = Fintype.card α * Fintype.card β := by
  simp [Fintype.card, instFintypeProd, Finset.card_product, Finset.card_univ]

-- =========================================================
-- Section 8: ZMod.card
-- =========================================================

namespace ZMod
@[simp] theorem card (n : Nat) : Fintype.card (ZMod n) = n := Fintype.card_fin n
end ZMod

-- =========================================================
-- Section 9: Fintype API (from original file, kept as-is or adapted)
-- =========================================================

/-- Transfer a Fintype instance along an equivalence. -/
def Fintype.ofEquiv (α : Type*) {β : Type*} [h : Fintype α] (e : α ≃ β) : Fintype β where
  elems    := h.elems.map e.toEmbedding
  complete b := by
    simp only [Finset.mem_map, Equiv.toEmbedding, Function.Embedding.coeFn_mk]
    exact ⟨e.symm b, h.complete _, e.apply_symm_apply b⟩

/-- Equivalent types have equal Fintype.card. -/
theorem Fintype.card_congr {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    Fintype.card α = Fintype.card β :=
  Nat.le_antisymm
    (Fintype.card_le_of_injective e e.injective)
    (Fintype.card_le_of_injective e.symm e.symm.injective)

/-- A surjection witnesses card β ≤ card α. -/
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

-- =========================================================
-- Section 10: Fintype for function types
-- =========================================================

/-- The number of functions α → β equals (card β)^(card α). -/
theorem Fintype.card_fun {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] :
    Fintype.card (α → β) = Fintype.card β ^ Fintype.card α := by
  simp [Fintype.card, Finset.card_pi_univ]

-- =========================================================
-- Section 11: Nat.card and related
-- =========================================================

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
theorem Nat.card_fun {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] :
    Nat.card (α → β) = Nat.card β ^ Nat.card α := by
  simp [Nat.card_eq_fintype_card, Fintype.card_fun]
