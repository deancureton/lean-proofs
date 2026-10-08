module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.NoExoticSixSphere.LowCollaredFillingBoundaryFrame
public import Wikipedia.NoExoticSixSphere.CollaredZeroFramedPath

@[expose] public section

/-!
# Native low-surgery paths reach the literal filling boundary, with the full frame

The comparison uses the original regular-zero atlas and the positive
half's actual boundary diffeomorphism. It adds no axes and retains every
ambient normal column, including the outward time-normal. Composition
with any finite native low-surgery path gives the full framed comparison.
Neither the boundary nor the ambient state is assumed simply connected.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.LowCollaredFillingBoundary

open GLOrthonormalization Stiefel Wikipedia.HopfProblem
open DegreeCollapse SingularMayerVietoris

variable {B : Type} [TopologicalSpace B]

local instance comparisonStateChartedSpace (U : LowCollaredSevenState B) :
    ChartedSpace (Vector (6 + 1)) U.Space := U.atlas

local instance comparisonStateIsManifold (U : LowCollaredSevenState B) :
    IsManifold (𝓡 (6 + 1)) ∞ U.Space := U.smooth

def Comparison (S : LowCollaredSevenState B) (U : LowCollaredSevenState B) (b : B) : Type :=
  letI := S.zeroAtlas; letI := U.halfBoundaryAtlas;
  StabilizedFramedDiffeomorph (CollaredZero.embedding S)
    (CollaredZero.normalFrame S (CollaredZero.referencePoint S b))
    (embedding U) (normalFrame U (U.collar.zeroPoint b).val)

def fillingOfComparison {S : LowCollaredSevenState B} {U : LowCollaredSevenState B} {b : B}
    (F : Comparison S U b) : letI := S.zeroAtlas; FramedSevenFilling (𝓡 6) S.Zero := by
  let := S.zeroAtlas
  let := U.zeroAtlas
  let := U.halfChartedSpace
  let := U.halfBoundaryAtlas
  exact { U.framedFilling with boundaryDiffeomorph := F.diffeomorph }




variable (S : LowCollaredSevenState B)

def boundaryComparison (b : B) : Comparison S S b := by
  let := S.zeroAtlas
  let := S.halfBoundaryAtlas
  let D := S.halfBoundaryDiffeomorph.symm
  refine
    { extra := 0
      ambient := LinearIsometryEquiv.refl ℝ (Vector S.embedding.ambientDimension)
      normal := LinearIsometryEquiv.refl ℝ (Vector (S.embedding.ambientDimension - 6))
      diffeomorph := D
      embedding_eq := ?_
      frame_eq := ?_ }
  · intro p
    change S.embedding.toFun p.val =
      appendZeroMap S.embedding.ambientDimension 0 (S.embedding.toFun p.val)
    exact (FramedBlock.appendZero_zero S.embedding.ambientDimension _).symm
  · intro p v
    change (normalFrame S (S.collar.zeroPoint b).val).ambient (D p) v =
      BlockSum.operator 0
        ((CollaredZero.normalFrame S (CollaredZero.referencePoint S b)).ambient p) v
    rw [BlockSum.operator_zero]
    rfl

theorem boundaryComparison_extra (b : B) :
    letI := S.zeroAtlas; letI := S.halfBoundaryAtlas;
    (boundaryComparison S b).extra = 0 := rfl

theorem boundaryComparison_point (b : B) (p : S.Zero) :
    letI := S.zeroAtlas; letI := S.halfBoundaryAtlas;
    ((boundaryComparison S b).diffeomorph p).val.val = p.val := rfl

theorem comparison_of_reachable {S U : LowCollaredSevenState B}
    (h : S.Reachable U) (b : B) : Nonempty (Comparison S U b) := by
  let := S.zeroAtlas
  let := U.zeroAtlas
  let := U.halfBoundaryAtlas
  obtain ⟨F⟩ := CollaredZero.comparison_of_reachable h b
  exact ⟨F.trans (boundaryComparison U b)⟩

end NoExoticSixSphere.LowCollaredFillingBoundary
