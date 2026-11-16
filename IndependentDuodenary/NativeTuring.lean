import Batteries

/-! Mathlib-free Turing machine types: Dir, Tape, TM0 structures.
   Also provides finProdFinEquiv and finCongr used by PostMicrocode. -/

namespace Turing

inductive Dir where
  | left | right
  deriving DecidableEq, Repr

structure Tape (Γ : Type*) where
  left  : List Γ
  head  : Γ
  right : List Γ

def Tape.write {Γ : Type*} (a : Γ) (t : Turing.Tape Γ) : Turing.Tape Γ :=
  { t with head := a }

def Tape.move {Γ : Type*} [Inhabited Γ] (d : Dir) (t : Turing.Tape Γ) : Turing.Tape Γ :=
  match d with
  | .left  => ⟨t.left.tail,  t.left.headD default,  t.head :: t.right⟩
  | .right => ⟨t.head :: t.left, t.right.headD default, t.right.tail⟩

@[simp] theorem Tape.write_self {Γ : Type*} (t : Turing.Tape Γ) : t.write t.head = t := rfl

namespace TM0

inductive Stmt (Γ : Type*) where
  | move  (d : Dir)
  | write (a : Γ)

abbrev Machine (Γ Λ : Type*) := Λ → Γ → Option (Λ × Stmt Γ)

structure Cfg (Γ Λ : Type*) where
  q    : Λ
  Tape : Turing.Tape Γ

variable {Γ Λ : Type*} [Inhabited Γ]

def step (M : Machine Γ Λ) (cfg : Cfg Γ Λ) : Option (Cfg Γ Λ) :=
  (M cfg.q cfg.Tape.head).map fun ⟨q', stmt⟩ =>
    match stmt with
    | .write a => ⟨q', cfg.Tape.write a⟩
    | .move  d => ⟨q', cfg.Tape.move d⟩

def init [Inhabited Λ] (l : List Γ) : Cfg Γ Λ :=
  ⟨default, ⟨[], l.headD default, l.tail⟩⟩

end TM0

end Turing

-- Fin product equiv: Fin m × Fin n ≃ Fin (m * n)
def finProdFinEquiv {m n : Nat} : Fin m × Fin n ≃ Fin (m * n) where
  toFun := fun ⟨i, j⟩ => ⟨i.val * n + j.val, by
    have hi := i.isLt; have hj := j.isLt; nlinarith⟩
  invFun := fun k => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd k.isLt (by simp [Nat.mul_zero])
    · exact ⟨⟨k.val / n, (Nat.div_lt_iff_lt_mul hn).mpr k.isLt⟩,
             ⟨k.val % n, Nat.mod_lt _ hn⟩⟩
  left_inv := fun ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd hj (Nat.not_lt_zero _)
    · simp only [Fin.mk.injEq]
      exact ⟨by omega, by omega⟩
  right_inv := fun ⟨k, hk⟩ => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd hk (by simp [Nat.mul_zero])
    · simp only [Fin.mk.injEq]; omega

-- finCongr: Fin m ≃ Fin n given m = n
def finCongr {m n : Nat} (h : m = n) : Fin m ≃ Fin n := by subst h; exact Equiv.refl _
