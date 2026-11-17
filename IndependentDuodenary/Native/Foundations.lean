/-!
Native foundations for Ruling 1.  This module supplies function predicates that
are absent from this repository's Lean 4.14 `Init` prelude.
-/

namespace Function

/-- Ruling 1 native replacement for `Function.LeftInverse` from Mathlib. -/
def LeftInverse {α β : Sort _} (g : β → α) (f : α → β) : Prop :=
  ∀ x, g (f x) = x

/-- Ruling 1 native replacement for `Function.RightInverse` from Mathlib. -/
def RightInverse {α β : Sort _} (g : β → α) (f : α → β) : Prop :=
  ∀ y, f (g y) = y

/-- Ruling 1 native replacement for `Function.Injective` from Mathlib. -/
def Injective {α β : Sort _} (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

/-- Ruling 1 native replacement for `Function.Surjective` from Mathlib. -/
def Surjective {α β : Sort _} (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

/-- Ruling 1 native replacement for `Function.Bijective` from Mathlib. -/
def Bijective {α β : Sort _} (f : α → β) : Prop :=
  Injective f ∧ Surjective f

namespace Bijective

/-- Ruling 1 projection replacing the Mathlib bijectivity injective projection. -/
theorem injective {α β : Sort _} {f : α → β} (h : Bijective f) : Injective f := h.1

/-- Ruling 1 projection replacing the Mathlib bijectivity surjective projection. -/
theorem surjective {α β : Sort _} {f : α → β} (h : Bijective f) : Surjective f := h.2

end Bijective

end Function

/-- Ruling 1 native replacement for `congr_arg` from Mathlib; core spells it `congrArg`. -/
abbrev congr_arg {α : Sort _} {β : Sort _} {a b : α} (f : α → β) (h : a = b) :
    f a = f b := congrArg f h

/-- Ruling 1 native replacement for `Function.Embedding` from Mathlib. -/
structure Function.Embedding (α β : Sort _) where
  toFun : α → β
  inj' : Function.Injective toFun

infixr:25 " ↪ " => Function.Embedding

/-- Ruling 1 native coercion replacing the Mathlib embedding coercion. -/
instance {α β : Sort _} : CoeFun (Function.Embedding α β) (fun _ => α → β) :=
  ⟨Function.Embedding.toFun⟩

namespace Function.Embedding

/-- Ruling 1 native replacement for the embedding coercion theorem from Mathlib. -/
@[simp] theorem coe_mk {α β : Sort _} (f : α → β) (h : Function.Injective f) (x : α) :
    (⟨f, h⟩ : Function.Embedding α β) x = f x := rfl

end Function.Embedding
