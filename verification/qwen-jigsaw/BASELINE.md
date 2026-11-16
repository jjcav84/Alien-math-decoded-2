# BASELINE

Source commit: 9fae30e (branch claude/zen-tesla-c2jsvh)
Connected repo: johnstobey/Alien-math-decoded-2. The mission names johnstobey/Alien-Math-Duodenary-Closure; that repo is not connected. Work stays in the connected repo.
Toolchain pin: leanprover/lean4:v4.14.0 (lean-toolchain). Lake manifest pins mathlib 4bbdccd9.

## Lean / Lake availability
- lean, lake, elan: NOT installed. Setup-script elan download failed (release-assets host not allowlisted).
- Allowlist fixed via update_environment (added release-assets.githubusercontent.com). Hand install of elan was denied by the auto-mode classifier. Not retried.
- Result: no Lean build or kernel check was run in this session.

## Inventory (grep, verified)
- .lean files: 248 (IndependentDuodenary 28, examples 16, extended_modules 100, z12z_generated 100, root 4).
- `import Mathlib*`: 110 files total = 100 in z12z_generated/ + 10 in IndependentDuodenary/.
- IndependentDuodenary files importing Mathlib: AffineStations, BinaryStructure, MillenniumBridge, ModularCore, PostMicrocode, SearchBoundary, SourceFactorization, SourceProjection, SourceReduction, TwelveStateStructure.
- Mathlib modules used: Data.ZMod.Basic, Data.Fintype.{Card,Units}, Data.Finset.Powerset, Data.List.FinRange, Logic.Equiv.Fin, Tactic.FinCases, Algebra.Module.Prod, Algebra.BigOperators.{Group.Finset,GroupWithZero.Action}, GroupTheory.SpecificGroups.Dihedral, Computability.TuringMachine.
- extended_modules/ files: 0 Mathlib imports. They import IndependentDuodenary.BinaryBridge.
- `sorry`, `admit`, `axiom` declarations: none found by grep.
- Lakefile requires mathlib from git; lake-manifest pins mathlib plus 8 transitive packages.
- Mission-named files (AlienMath/F2_12_closure.lean, Z144Resolution.lean, UGCRingBridge.lean) do not exist in this repo.

## Core arithmetic
- IndependentDuodenary/ModularCore.lean defines station : ZMod 12 and superstation : ZMod 144 via Mathlib ZMod. Its theorems use `decide` and Nat.cast_add.
- Native replacement target: Fin-based residue arithmetic (Fin n has core Add/Mul; no Mathlib needed).

## Dependency priority (unlock order)
1. Native ZMod-equivalent in IndependentDuodenary (replaces ZMod.Basic in ModularCore, used by 10 IndependentDuodenary files).
2. Remaining Mathlib-using core files (Fintype, Finset, Equiv, BigOperators, Dihedral, TuringMachine).
3. z12z_generated/ (100 files, each `import Mathlib`), regenerate or port.
4. Non-isomorphism Z/144 vs Z/12xZ/12 formalization (see below).

## Finite computation (computationally verified, domain = Z/144 and Z/12 x Z/12)
Script: verification/qwen-jigsaw/nonisomorphism_check.py (run exit 0)
- max element order: Z/144 = 144; Z/12xZ/12 = 12
- elements of order 144: 48 in Z/144; 0 in product
- homomorphisms Z/144 -> product: 144; injective: 0. No isomorphism.
Evidence class 2. Mathematical argument (class 3): exponent of product is 12, so no element of order 144 exists, so no injective hom from cyclic group of order 144.

## Build result
Not run. Lean unavailable.
