module

public import Wikipedia.HopfProblem.DegreeCollapseSupportedPathDiskAlignment
public import Wikipedia.HopfProblem.DegreeCollapseClosedImagePathAvoidance

@[expose] public section

/-!
# Whole disk alignment fixing a closed smooth obstacle

Relative general position first makes the center path avoid the entire
closed smooth obstacle. The compact support then stays in its complement,
so every real-time slice fixes every point of the original obstacle.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking

variable {D E V H M Y : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [SecondCountableTopology Y]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]


end Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking
