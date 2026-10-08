module

public import Wikipedia.HopfProblem.DegreeCollapseFiniteFamilyPassage

@[expose] public section

/-!
# Construct both relative preparation and the finite-family passage

Initial disjointness from the crossed belt is constructed, not assumed.
The preparatory isotopy fixes every other original sheet and its ambient
germ. The subsequent passage also fixes those exact original sheets and
crosses the full original target once, with native transversality.
-/

noncomputable section

open Set Function Filter Metric Manifold Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open MorseRearrangement

local notation "D₂" => EuclideanSpace ℝ (Fin 2)

variable {ι E M X Y : Type} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M]
  [TopologicalSpace X] [ChartedSpace D₂ X] [IsManifold (𝓡 2) ∞ X]
  [CompactSpace X] [SecondCountableTopology X] [T2Space X]
  [TopologicalSpace Y] [ChartedSpace D₂ Y] [IsManifold (𝓡 2) ∞ Y]
  [CompactSpace Y] [SecondCountableTopology Y]


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
