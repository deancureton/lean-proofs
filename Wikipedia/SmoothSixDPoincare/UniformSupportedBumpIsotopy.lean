module

public import Wikipedia.SmoothSixDPoincare.SupportedBumpIsotopy
public import Wikipedia.SmoothSixDPoincare.UniformBumpTranslation

@[expose] public section

/-!
# Uniform supported native isotopies for every spatial time slice

One positive displacement bound works for the whole jointly smooth compact
family. Every step is an actual smooth family of native diffeomorphisms with
the exact endpoint formula, and is supported in its genuine slice support.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞)


end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
