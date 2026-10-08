module

public import Wikipedia.HopfProblem.DegreeCollapseFiniteThreeBeltReduction

@[expose] public section

/-!
# Zero and unit three-belt signed counts give actual geometric reduction

The finite native Whitney sequence removes every intersection for count zero
and leaves exactly one transverse intersection for absolute count one.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  (D : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hdim : Module.finrank ℝ E = 7)
  [Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1)]
  (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 3)
  (hnull : ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
    ∃ q, γ.Homotopic (ContinuousMap.const _ q))
  (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 4)

include hdim hindex hnull



end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
