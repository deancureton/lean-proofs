module

public import Wikipedia.NoExoticSixSphere.SmallCapRelativeRepresentative
public import Wikipedia.NoExoticSixSphere.CompactSupportedCapInclusion

@[expose] public section

/-!
# Localized cap is cap with the actual neighborhood fundamental class

The small-chain decomposition constructs a relative class inside the
open neighborhood. Its original pair-map image is the prescribed
ambient fundamental class. Actual relative excision and preservation
of the constructed fundamental class identify that local class.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.CompactSupportedCapMap

open ModTwoCapProduct (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)
open SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (U : Set M) (hU : IsOpen U) [ChartedSpace E U]


end NoExoticSixSphere.CompactSupportedCapMap
