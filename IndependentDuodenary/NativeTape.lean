/-! Native, mathlib-free single-tape Turing-machine substrate.

This file has no `import` statements: it depends on Lean 4 core (`Init`) only.
It reproduces, without Mathlib, the tape interface consumed by
`IndependentDuodenary.PostMicrocode`: a `List`/`Nat`-indexed head-plus-symbol
tape with `write`, `move`, `head`, the `Tape.write_self` law, a `Machine`/
`Cfg`/`step` layer, and the step-transition lemmas (`step_eq_some_iff`,
`step_none`, `step_some`, `tick` laws, `run` laws) used by the microcode
compiler proofs. Every result is fully proved; the file declares no
`sorry`, no `admit`, and no `native_axiom`. -/

namespace IndependentDuodenary

/-! ## Head movements -/

namespace Native

/-- One-step head motion of a single-tape machine. -/
inductive Move where
  | left | stay | right
  deriving DecidableEq, Inhabited, Repr

/-- The blank symbol is the `Inhabited` default of the alphabet. -/
theorem move_inhabited_left [Inhabited α] : (default : Move) = Move.left := rfl

/-! ## Tapes -/

/-- A one-tape configuration: cells left of the head (nearest first), the
symbol under the head, and cells right of the head (nearest first). The
`List`s are `Nat`-indexed: index `0` is the cell adjacent to the head. -/
structure Tape (α : Type) where
  /-- Cells to the left of the head, nearest first. -/
  left : List α
  /-- The symbol under the head. -/
  head : α
  /-- Cells to the right of the head, nearest first. -/
  right : List α

/-- The tape holding `input` on the right of the head and blank everywhere else. -/
def Tape.blank (blank : α) (input : List α) : Tape α := ⟨[], blank, input⟩

/-- Overwrite the symbol under the head; everything else is unchanged. -/
def Tape.write (a : α) (t : Tape α) : Tape α := ⟨t.left, a, t.right⟩

/-- Move the head one cell. Moving off the represented region extends the
tape with the blank symbol. -/
def Tape.move (blank : α) (m : Move) (t : Tape α) : Tape α :=
  match m with
  | .stay => t
  | .left =>
    match t.left with
    | [] => ⟨[], blank, t.head :: t.right⟩
    | l :: ls => ⟨ls, l, t.head :: t.right⟩
  | .right =>
    match t.right with
    | [] => ⟨t.head :: t.left, blank, []⟩
    | r :: rs => ⟨t.head :: t.left, r, rs⟩

/-! ### Tape laws -/

/-- Writing `a` puts `a` under the head. -/
@[simp] theorem Tape.write_self (t : Tape α) (a : α) : (t.write a).head = a := rfl

/-- A write changes only the head cell. -/
@[simp] theorem Tape.write_eq_mk (t : Tape α) (a : α) : t.write a = ⟨t.left, a, t.right⟩ := rfl

/-- Writes into the blank region start on a blank cell. -/
@[simp] theorem Tape.blank_head (blank : α) (input : List α) :
    (Tape.blank blank input).head = blank := rfl

@[simp] theorem Tape.move_stay (blank : α) (t : Tape α) : Tape.move blank .stay t = t := rfl

@[simp] theorem Tape.move_left_nil (blank : α) (head : α) (right : List α) :
    Tape.move blank .left ⟨[], head, right⟩ = ⟨[], blank, head :: right⟩ := rfl

@[simp] theorem Tape.move_left_cons (blank l : α) (ls : List α) (head : α) (right : List α) :
    Tape.move blank .left ⟨l :: ls, head, right⟩ = ⟨ls, l, head :: right⟩ := rfl

@[simp] theorem Tape.move_right_nil (blank : α) (left : List α) (head : α) :
    Tape.move blank .right ⟨left, head, []⟩ = ⟨head :: left, blank, []⟩ := rfl

@[simp] theorem Tape.move_right_cons (blank : α) (left : List α) (head r : α) (rs : List α) :
    Tape.move blank .right ⟨left, head, r :: rs⟩ = ⟨head :: left, r, rs⟩ := rfl

/-! ## Configurations, machines and single-step transitions -/

/-- One step of instruction output: write at the current cell, or move. -/
inductive Stmt (α : Type) where
  | write (a : α) : Stmt α
  | move : Move → Stmt α

/-- Execute an instruction against a tape. The blank for edge extension is
the `Inhabited` default of the alphabet. -/
def Stmt.act [Inhabited α] (t : Tape α) (s : Stmt α) : Tape α :=
  match s with
  | .write a => t.write a
  | .move m => t.move default m

@[simp] theorem Stmt.act_write [Inhabited α] (t : Tape α) (a : α) :
    Stmt.act t (.write a) = t.write a := rfl

@[simp] theorem Stmt.act_move [Inhabited α] (t : Tape α) (m : Move) :
    Stmt.act t (.move m) = t.move default m := rfl

/-- Deterministic finite control: for each state and scanned symbol, either
halt (`none`) or emit a successor state and one instruction. -/
def Machine (α Λ : Type) := Λ → α → Option (Λ × Stmt α)

/-- A machine configuration: control state plus tape. -/
structure Cfg (α : Type) (Λ : Type) where
  q : Λ
  tape : Tape α

/-- One transition of `M` on configuration `c`. -/
def step [Inhabited α] (M : Machine α Λ) (c : Cfg α Λ) : Option (Cfg α Λ) :=
  (M c.q c.tape.head).map fun p => ⟨p.1, p.2.act c.tape⟩

/-! ### Step-transition lemmas -/

/-- Definitional reduction of `Option.map` on `some`, self-proved to avoid
reliance on core simp-lemma statement forms. -/
theorem option_map_some {β : Type v} {f : α → β} {a : α} :
    Option.map f (some a) = some (f a) := rfl

/-- Halting transition table gives no transition. -/
@[simp] theorem step_none [Inhabited α] {M : Machine α Λ} {c : Cfg α Λ}
    (h : M c.q c.tape.head = none) : step M c = none := by
  simp [step, h]

/-- A table entry emits exactly the instruction applied to the tape. -/
theorem step_some [Inhabited α] {M : Machine α Λ} {c : Cfg α Λ} {q' : Λ} {s : Stmt α}
    (h : M c.q c.tape.head = some (q', s)) :
    step M c = some ⟨q', s.act c.tape⟩ := by
  simp [step, h]

/-- Full characterization of a non-halting transition. -/
theorem step_eq_some_iff [Inhabited α] {M : Machine α Λ} {c : Cfg α Λ} {cfg : Cfg α Λ} :
    step M c = some cfg ↔
      ∃ q' s, M c.q c.tape.head = some (q', s) ∧ cfg = ⟨q', s.act c.tape⟩ := by
  cases h : M c.q c.tape.head with
  | none =>
    have e : step M c = none := step_none h
    rw [e]
    simp [h]
  | some p =>
    rcases p with ⟨p1, p2⟩
    rcases cfg with ⟨cq, ct⟩
    constructor
    · intro hstep
      have h3 := (step_some h).symm.trans hstep
      injection h3 with hc
      injection hc with hq ht
      exact ⟨p1, p2, rfl, by rw [hq, ht]⟩
    · rintro ⟨q', s, hs, heq⟩
      injection heq with hq ht
      subst hq
      subst ht
      exact step_some (h.trans hs)

/-! ### Tick laws -/

/-- One tick: take the step if it exists, otherwise stay. -/
def tick [Inhabited α] (M : Machine α Λ) (c : Cfg α Λ) : Cfg α Λ := (step M c).getD c

/-- A non-halting step is the tick. -/
theorem tick_eq_of_step [Inhabited α] {M : Machine α Λ} {c d : Cfg α Λ}
    (h : step M c = some d) : tick M c = d := by
  simp [tick, h]

/-- A halting step leaves the configuration unchanged. -/
theorem tick_eq_self_of_step_none [Inhabited α] {M : Machine α Λ} {c : Cfg α Λ}
    (h : step M c = none) : tick M c = c := by
  simp [tick, h]

/-- Every tick is the execution of some transition. -/
theorem step_eq_some_of_tick_ne_self [Inhabited α] {M : Machine α Λ} {c : Cfg α Λ}
    (hne : tick M c ≠ c) : step M c = some (tick M c) := by
  cases hs : step M c with
  | none => exact absurd (tick_eq_self_of_step_none hs) hne
  | some e => rw [tick_eq_of_step hs]

/-! ### Iteration and runs -/

/-- Core-only bounded iteration (no `Function.iterate` notation is used, as
that notation lives outside `Init`). -/
def iterate (f : α → α) (n : Nat) (x : α) : α :=
  Nat.rec x (fun _ ih => f ih) n

@[simp] theorem iterate_zero (f : α → α) (x : α) : iterate f 0 x = x := rfl

@[simp] theorem iterate_succ (f : α → α) (n : Nat) (x : α) :
    iterate f (n + 1) x = f (iterate f n x) := rfl

theorem iterate_succ' (f : α → α) (n : Nat) (x : α) :
    iterate f (n + 1) x = iterate f n (f x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [iterate_succ, ih, iterate_succ]

/-- The initial configuration: control state `q0`, input on the tape, blank
under the head. -/
def init [Inhabited α] (q0 : Λ) (input : List α) : Cfg α Λ :=
  ⟨q0, Tape.blank default input⟩

/-- Run `M` for exactly `n` ticks from the initial configuration. -/
def run [Inhabited α] (M : Machine α Λ) (q0 : Λ) (input : List α) (n : Nat) : Cfg α Λ :=
  iterate (tick M) n (init q0 input)

@[simp] theorem run_zero [Inhabited α] (M : Machine α Λ) (q0 : Λ) (input : List α) :
    run M q0 input 0 = init q0 input := rfl

@[simp] theorem run_succ [Inhabited α] (M : Machine α Λ) (q0 : Λ) (input : List α) (n : Nat) :
    run M q0 input (n + 1) = tick M (run M q0 input n) := by
  simp only [run, iterate_succ]

/-- Running one more tick equals stepping once from the shorter run. -/
theorem run_step_some [Inhabited α] {M : Machine α Λ} {q0 : Λ} {input : List α} {n : Nat}
    {d : Cfg α Λ} (h : step M (run M q0 input n) = some d) :
    run M q0 input (n + 1) = d := by
  rw [run_succ, tick_eq_of_step h]

end Native

#print axioms Native.Tape.write_self
#print axioms Native.step_eq_some_iff
#print axioms Native.run_succ

end IndependentDuodenary
