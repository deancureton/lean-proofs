module

public import Wikipedia.NoExoticSixSphere.OpenZeroSliceAvoidance
public import Wikipedia.NoExoticSixSphere.PartialGradientLocalData

@[expose] public section

/-!
# Relative avoidance of the partial-critical slice

Within one verified negative-family chart, a compact parameter family of
dimension smaller than the negative-family dimension can be deformed off the
partial-critical slice. The homotopy stays in any prescribed open subset of
the chart source, fixes a compact already-safe parameter set, and preserves
the complementary coordinate.
-/

open Set Module
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {B H M D E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

include I


end NoExoticSixSphere.PartialGradientCoordinates.LocalData
