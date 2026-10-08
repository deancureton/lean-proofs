module

public import Wikipedia.HopfProblem.DegreeCollapseConvexHeightProfiles
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

/-!
# Native scalar profiles separated on the two closed basin sections

Smooth separation of disjoint closed subsets of the actual compact level
manifold gives a weight with full zero and one neighborhoods. Blending
the constructed scalar profiles retains positive height derivative,
all exterior heights, and the prescribed full translation germs on the
two selected section-height sets. No replacement level atlas is used.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N] [CompactSpace N]


end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
