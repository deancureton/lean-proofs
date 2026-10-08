module

public import Wikipedia.SmoothSixDPoincare.SharedCornerStripPair
public import Wikipedia.SmoothSixDPoincare.TwoSheetTubularBigon

@[expose] public section

/-!
# A fully constructed tubular bigon from original native three-dimensional sheets

The original homotopy equivalence, compact transverse sheet embeddings, two
crossings, joining paths, and nonzero endpoint directions construct the arcs,
corners, strips, clean closed neighborhood, smooth filling, and tubular chart.
No disk, boundary neighborhood, chart, or extension map is an input.

The sheets share their three-dimensional normed model. The resulting tube
does not yet carry a proved Whitney framing or cancel an actual handle pair.
-/

noncomputable section

open Set Function ContinuousMap Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E M D N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [TopologicalSpace P] [ChartedSpace D P] [IsManifold 𝓘(ℝ, D) ∞ P]
  [T2Space N] [CompactSpace N] [T2Space P] [CompactSpace P]


end Wikipedia.SmoothSixDPoincare
