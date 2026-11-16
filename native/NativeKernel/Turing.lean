/-
Native Turing-machine kernel (deterministic, one tape, two-way infinite).

Core Lean 4 only: no Mathlib, no Batteries, no tactics beyond core.
Replaces the use of `Mathlib.Computability.TuringMachine` in
`IndependentDuodenary/MillenniumBridge.lean`. This module is a fresh
definition, not a proof of equivalence with Mathlib's `TM0`.

Semantics:
- A tape is a head cell plus two lists: `left` (nearest cell first) and
  `right` (nearest cell first). Off-the-end cells read `default`.
- A machine maps (state, head symbol) to `none` (halt) or
  `some (state', written symbol, direction)`.
- `iter M n c` runs `n` steps; once halted, the configuration is fixed.
-/

namespace NativeKernel.Turing

inductive Dir where
  | left
  | right
  | stay
  deriving DecidableEq, Repr

structure Tape (Γ : Type) where
  left : List Γ
  head : Γ
  right : List Γ
  deriving DecidableEq, Repr

structure Machine (Γ Λ : Type) where
  next : Λ → Γ → Option (Λ × Γ × Dir)

structure Cfg (Γ Λ : Type) where
  state : Λ
  tape : Tape Γ
  deriving DecidableEq, Repr

variable {Γ Λ : Type}

/-- Move the head one cell. Off-the-end cells are `default`. -/
def moveTape [Inhabited Γ] (t : Tape Γ) : Dir → Tape Γ
  | .stay => t
  | .left =>
    match t.left with
    | [] => ⟨[], default, t.head :: t.right⟩
    | x :: l => ⟨l, x, t.head :: t.right⟩
  | .right =>
    match t.right with
    | [] => ⟨t.head :: t.left, default, []⟩
    | x :: r => ⟨t.head :: t.left, x, r⟩

/-- One deterministic step; `none` means the machine halts. -/
def step [Inhabited Γ] (M : Machine Γ Λ) (c : Cfg Γ Λ) : Option (Cfg Γ Λ) :=
  match M.next c.state c.tape.head with
  | none => none
  | some (q, g, d) => some ⟨q, moveTape { c.tape with head := g } d⟩

/-- Step if possible, otherwise keep the configuration. -/
def stepOr [Inhabited Γ] (M : Machine Γ Λ) (c : Cfg Γ Λ) : Cfg Γ Λ :=
  (step M c).getD c

/-- Run `n` steps (halted configurations are fixed points). -/
def iter [Inhabited Γ] (M : Machine Γ Λ) : Nat → Cfg Γ Λ → Cfg Γ Λ
  | 0, c => c
  | n + 1, c => iter M n (stepOr M c)

def Halted [Inhabited Γ] (M : Machine Γ Λ) (c : Cfg Γ Λ) : Prop :=
  step M c = none

/-! ## Structural lemmas -/

theorem iter_zero [Inhabited Γ] (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    iter M 0 c = c := rfl

theorem iter_succ_right [Inhabited Γ] (M : Machine Γ Λ) (n : Nat) (c : Cfg Γ Λ) :
    iter M (n + 1) c = stepOr M (iter M n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => exact ih (stepOr M c)

theorem iter_add [Inhabited Γ] (M : Machine Γ Λ) (m n : Nat) (c : Cfg Γ Λ) :
    iter M (m + n) c = iter M n (iter M m c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 from rfl, iter_succ_right, iter_succ_right, ih]

theorem stepOr_of_halted [Inhabited Γ] (M : Machine Γ Λ) (c : Cfg Γ Λ)
    (h : Halted M c) : stepOr M c = c := by
  unfold stepOr Halted at *
  rw [h]
  rfl

theorem iter_of_halted [Inhabited Γ] (M : Machine Γ Λ) (c : Cfg Γ Λ)
    (h : Halted M c) (n : Nat) : iter M n c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iter_succ_right, ih, stepOr_of_halted M c h]

/-! ## Worked example: erase a run of `true` cells moving right -/

inductive Unit1 where
  | run
  deriving DecidableEq, Repr

def eraseRight : Machine Bool Unit1 where
  next _ b := if b then some (.run, false, .right) else none

def exampleStart : Cfg Bool Unit1 :=
  ⟨.run, ⟨[], true, [true, true, false]⟩⟩

/-- Three steps erase the three leading `true` cells. -/
theorem example_three_steps :
    iter eraseRight 3 exampleStart =
      ⟨.run, ⟨[false, false, false], false, []⟩⟩ := by
  rfl

/-- The machine then halts on the blank-like `false` head. -/
theorem example_halts :
    Halted eraseRight (iter eraseRight 3 exampleStart) := by
  rfl

/-- A halted configuration is a fixed point of every further run. -/
theorem example_fixed (n : Nat) :
    iter eraseRight (3 + n) exampleStart = iter eraseRight 3 exampleStart := by
  rw [iter_add]
  exact iter_of_halted eraseRight _ example_halts n

end NativeKernel.Turing

#print axioms NativeKernel.Turing.iter_add
#print axioms NativeKernel.Turing.iter_of_halted
#print axioms NativeKernel.Turing.example_three_steps
#print axioms NativeKernel.Turing.example_fixed
