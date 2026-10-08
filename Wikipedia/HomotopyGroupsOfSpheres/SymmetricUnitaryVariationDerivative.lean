module

public import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryEndpointVariation
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-! # Smoothness and the actual parameter derivative of the constrained variations -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open ImaginarySymmetricMatrices RealSymmetricMixing
open scoped Matrix.Norms.Operator ContDiff

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem hasDerivAt_exponentialCurve_matrix (A : DirectionSpace N) (t : ℝ) :
    HasDerivAt (fun r : ℝ ↦ (exponentialCurve A r).val.val.val)
      ((exponentialCurve A t).val.val.val * imaginary A.val) t := by
  change HasDerivAt (fun r : ℝ ↦ NormedSpace.exp (imaginary (r • A.val)))
    (NormedSpace.exp (imaginary (t • A.val)) * imaginary A.val) t
  simp only [map_smul]
  exact hasDerivAt_exp_smul_const (imaginary A.val) t

theorem hasDerivAt_exponentialCurve_zero (A : DirectionSpace N) :
    HasDerivAt (fun r : ℝ ↦ (exponentialCurve A r).val.val.val) (imaginary A.val) 0 := by
  have h := hasDerivAt_exponentialCurve_matrix A 0
  rw [exponentialCurve_zero] at h
  change HasDerivAt _ ((1 : Matrix N N ℂ) * imaginary A.val) 0 at h
  simpa only [one_mul] using h



end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
