module

public import Wikipedia.HopfProblem.DegreeCollapseGlobalCrossingDisk

@[expose] public section

/-!
# Constructed embedded disk crossing the whole original middle belt

In every prescribed open neighborhood of an actual index-three belt point,
construct an entire smooth embedded immersive disk and a compactly supported
native isotopy. The full disk trace meets the full belt exactly once and
transversely. No model disk, chart, cutoff, or motion is supplied as input.
-/

noncomputable section

open Set Function Metric Manifold Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
