import Lake
open Lake DSL

package independent_duodenary where
  version := v!"0.1.0"

-- No external requirements. Mathlib was removed; the residue foundation is native (see IndependentDuodenary/NativeResidue.lean).
-- NOTE: the modules in IndependentDuodenary/ that still `import Mathlib` (10 direct, plus transitive dependents) are NOT yet ported.

@[default_target]
lean_lib IndependentDuodenary

@[default_target]
lean_exe verifyPipeline where
  root := `PipelineMain

@[default_target]
lean_lib extended_modules
