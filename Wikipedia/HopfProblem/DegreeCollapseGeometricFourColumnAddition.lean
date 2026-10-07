module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseCommonCutFourFamilySlide
public import Wikipedia.HopfProblem.DegreeCollapseFourSectionSpanning
public import Wikipedia.HopfProblem.DegreeCollapseMatrixColumnAlgebra

@[expose] public section

/-!
# A prescribed elementary column addition on the actual native four-handle family

Keep the original common cut and its integral basis. Exactly the chosen
higher column receives the requested signed original central column. The
constructed complete flow retains the whole labelled basin family and all
lower critical basins. Only the actual prefix is constrained in index.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

attribute [local irreducible] canonicalFourMatrix

local notation "S₃" => Hemisphere.Sphere 3

section Matrix

variable {M : Type} [TopologicalSpace M] {f : M → ℝ}

theorem canonicalFourMatrix_family_slide {a : ℝ} {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 3)
    (αq : C(S₃, {y : M // f y = a})) (α Γ : Fin n → C(S₃, {y : M // f y = a}))
    (i : Fin n) (k : ℤ) (hother : ∀ j, j ≠ i → Γ j = α j)
    (hclass : threeSectionClass (Γ i) = threeSectionClass (α i) + k • threeSectionClass αq) :
    canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B (Fin.cases αq Γ) =
      canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B
        (Fin.cases αq α) * Matrix.transvection 0 i.succ k := by
  refine @eq_mul_transvection_of_columns r (n + 1)
    (canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B (Fin.cases αq α))
    (canonicalFourMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B (Fin.cases αq Γ))
    0 i.succ k ?_ ?_
  · intro u
    simp only [canonicalFourMatrix, classCoordinateMatrix, Fin.cases_succ, Fin.cases_zero]
    rw [hclass, map_add, map_zsmul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · intro u j hji
    cases j using Fin.cases with
    | zero => simp only [canonicalFourMatrix, classCoordinateMatrix, Fin.cases_zero]
    | succ j =>
      have hj : j ≠ i := fun h => hji (congrArg Fin.succ h)
      simp only [canonicalFourMatrix, classCoordinateMatrix, Fin.cases_succ, hother j hj]

end Matrix

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
