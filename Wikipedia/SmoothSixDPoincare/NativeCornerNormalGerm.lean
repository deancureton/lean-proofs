module

public import Wikipedia.SmoothSixDPoincare.CornerNormalDerivative
public import Wikipedia.SmoothSixDPoincare.CenteredParametrization

@[expose] public section

/-!
# Normal transversality for the actual native centered corner germs

Specialize the normal derivative theorem to the genuine centered chart of
the complementary sheet. The derivative used is the original sheet map's
native derivative at its original crossing point.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {D B E M A Z N P : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [TopologicalSpace N] [ChartedSpace A N]
  [TopologicalSpace P] [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P]


end Wikipedia.SmoothSixDPoincare
