module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseCommonCutFamilySlide
public import Wikipedia.HopfProblem.DegreeCollapseMatrixColumnAlgebra

@[expose] public section

/-!
# The realized common-cut slide is an actual elementary matrix operation

The old basis is unchanged. Exactly one higher column receives a signed
copy of the retained central column; all others are unchanged. The inverse
transvection proves that surjectivity survives this concrete geometric move.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

-- Keep matching from expanding the homology maps through unknown finite indices.
-- The coefficient calculations below unfold the matrix explicitly.
attribute [local irreducible] canonicalMiddleMatrix

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}

theorem canonicalMiddleMatrix_family_slide {a : ℝ} {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 2)
    (αq : C(S₂, {y : M // f y = a})) (α Γ : Fin n → C(S₂, {y : M // f y = a}))
    (i : Fin n) (k : ℤ) (hother : ∀ j, j ≠ i → Γ j = α j)
    (hclass : middleSectionClass (Γ i) = middleSectionClass (α i) + k • middleSectionClass αq) :
    canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B (Fin.cases αq Γ) =
      canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B
        (Fin.cases αq α) * Matrix.transvection 0 i.succ k := by
  refine @eq_mul_transvection_of_columns r (n + 1)
    (canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B (Fin.cases αq α))
    (canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n + 1) B (Fin.cases αq Γ))
    0 i.succ k ?_ ?_
  · intro u
    simp only [canonicalMiddleMatrix, classCoordinateMatrix, Fin.cases_succ, Fin.cases_zero]
    rw [hclass, map_add, map_zsmul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · intro u j hji
    cases j using Fin.cases with
    | zero => simp only [canonicalMiddleMatrix, classCoordinateMatrix, Fin.cases_zero]
    | succ j =>
      have hj : j ≠ i := fun h => hji (congrArg Fin.succ h)
      simp only [canonicalMiddleMatrix, classCoordinateMatrix, Fin.cases_succ, hother j hj]

variable [PathConnectedSpace M]


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
