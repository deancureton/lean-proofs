module

public import Wikipedia.HopfProblem.DegreeCollapseGeneralSurgeryCancellation
public import Wikipedia.HopfProblem.DegreeCollapseRegularBandReplacement
public import Wikipedia.HopfProblem.DegreeCollapseRegularSublevelBody

@[expose] public section

/-!
# Unique adjacent Morse-pair cancellation preserves the native smooth boundary

Use the constructed cancellation of the original Morse function, rather
than the whole-handle quotient homeomorphism. Compactness and native
Fermat retain the original band endpoints after cancellation. Smooth
regular-band transport then gives an ambient diffeomorphism carrying
the original lower sublevel to the original upper sublevel, together
with its actual restriction between their independently native atlases.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
