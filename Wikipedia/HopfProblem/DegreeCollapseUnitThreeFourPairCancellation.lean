module

public import Wikipedia.HopfProblem.DegreeCollapseThreeBeltHomologicalReduction
public import Wikipedia.HopfProblem.DegreeCollapseUnitConsecutiveLevelCancellation
public import Wikipedia.HopfProblem.DegreeCollapseCirclePlacementCount
public import Wikipedia.HopfProblem.DegreeCollapseCirclePlacementTransverseSheets

@[expose] public section

/-!
# An actual unit three-handle coordinate cancels the consecutive four-handle

The entire backward basin is represented by the original embedded attaching
three-sphere. Its native collapse coordinate supplies the unit signed count.
Construct transverse preparation, the complete finite Whitney sequence, the
unique whole-level crossing, the realized flow, and transverse ambient basin
tubes. Relative native cancellation removes exactly the original pair while
fixing the full upper germ and literal strict sublevel. No intersection or
Whitney data, and no exclusion of other lower endpoints, are assumed.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
