import IndependentDuodenary.NativeZMod

/-! Mathlib-free binary module typeclass: ZMod 2 scalar action.
   Replaces Module (ZMod 2) V from Mathlib for the Source* files. -/

class BinaryModule (V : Type*) extends AddCommMonoid V, SMul (ZMod 2) V where
  protected zero_smul : ∀ v : V, (0 : ZMod 2) • v = 0
  protected one_smul  : ∀ v : V, (1 : ZMod 2) • v = v
  protected smul_add  : ∀ (r : ZMod 2) (a b : V), r • (a + b) = r • a + r • b
  protected add_smul  : ∀ (r s : ZMod 2) (v : V), (r + s) • v = r • v + s • v

export BinaryModule (zero_smul one_smul smul_add add_smul)

attribute [simp] BinaryModule.zero_smul BinaryModule.one_smul

instance instBinaryModuleProd {K W : Type*} [BinaryModule K] [BinaryModule W] :
    BinaryModule (K × W) where
  smul r p := ⟨r • p.1, r • p.2⟩
  zero_smul p := by simp [HSMul.hSMul, SMul.smul, BinaryModule.zero_smul]
  one_smul p := by simp [HSMul.hSMul, SMul.smul, BinaryModule.one_smul]
  smul_add r a b := by
    simp [HSMul.hSMul, SMul.smul, BinaryModule.smul_add]
  add_smul r s p := by
    simp [HSMul.hSMul, SMul.smul, BinaryModule.add_smul]

instance instBinaryModuleFun {ι V : Type*} [BinaryModule V] : BinaryModule (ι → V) where
  smul r f i := r • f i
  zero_smul f := funext fun i => BinaryModule.zero_smul (f i)
  one_smul f := funext fun i => BinaryModule.one_smul (f i)
  smul_add r f g := funext fun i => BinaryModule.smul_add r (f i) (g i)
  add_smul r s f := funext fun i => BinaryModule.add_smul r s (f i)

instance instBinaryModuleZMod2 : BinaryModule (ZMod 2) where
  smul := (· * ·)
  zero_smul v := by decide
  one_smul v := by decide
  smul_add r a b := by decide
  add_smul r s v := by decide

theorem Finset.smul_sum [BinaryModule V] {ι : Type*} (r : ZMod 2)
    (s : Finset ι) (f : ι → V) : r • s.sum f = s.sum (fun i => r • f i) := by
  induction s using Finset.induction_on with
  | empty => simp [BinaryModule.zero_smul]
  | insert ha ih => simp [Finset.sum_insert ha, BinaryModule.smul_add, ih]
