module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseSevenExistingColumnsSmooth

@[expose] public section

/-!
# The retained original seven-manifold maps smoothly into the native boundary

The upper-end map was fixed before choosing the trace atlas. Its native
smoothness follows through the actual unchanged cylinder chart, and every
image point is a boundary point of the globally glued eight-dimensional
manifold. The separate atlas on that boundary and its end diffeomorphism are
not supplied here.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem originalEnd_mem_cylinderOnly (m : M) : originalEnd A m ∈ cylinderOnlyPart A :=
  originalEnd_mem_retainedRegion A m

def originalEndLift (m : M) : cylinderOnlyPart A :=
  ⟨originalEnd A m, originalEnd_mem_cylinderOnly A m⟩

theorem originalEndLift_coordinates (m : M) :
    (unchangedCylinderHomeomorph A (originalEndLift A m)).val.val =
      (m, UnroundedTrace.height A) :=
  HeightCylinder.injective_heightCylinder e
    (unchangedCylinderHomeomorph_ambient A (originalEndLift A m))

theorem contMDiff_originalEndLift : letI := unchangedCylinderChartedSpace A;
    ContMDiff (𝓡 7) (ProductHalfSpace.model (Vector 7)) ∞ (originalEndLift A) := by
  let := unchangedCylinderChartedSpace A
  apply (contMDiff_unchangedCylinder_iff_parameters A _).mpr
  have he : (fun m : M ↦ (unchangedCylinderHomeomorph A (originalEndLift A m)).val.val) =
      (fun m : M ↦ (m, UnroundedTrace.height A)) := funext (originalEndLift_coordinates A)
  rw [he]
  exact contMDiff_id.prodMk contMDiff_const

theorem contMDiff_originalEnd : letI := traceChartedSpace A;
    ContMDiff (𝓡 7) (ProductHalfSpace.model (Vector 7)) ∞ (originalEnd A) := by
  let := traceChartedSpace A
  let := pieceAtlas A .cylinder
  exact ((openCover A).contMDiff_inclusion .cylinder).comp (contMDiff_originalEndLift A)




end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
