module

public import Wikipedia.HopfProblem.DegreeCollapseCancellationFlowSheets

@[expose] public section

/-!
# The constructed native sheets lie in the actual endpoint basins

The signed cubic slice planes give the original endpoint limits. The
finite complete-flow shifts in the actual sheet definitions preserve
those limits throughout a genuine neighborhood of the reference point.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ} {p q : M}



end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
