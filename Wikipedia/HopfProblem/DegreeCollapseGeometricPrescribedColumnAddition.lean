module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseGeometricColumnAddition
public import Wikipedia.HopfProblem.DegreeCollapseCommonCutPrescribedFamilySlide

@[expose] public section

/-!
# Either prescribed elementary column addition is geometrically realized

The old basis is unchanged. Exactly one higher column receives a signed
copy of the retained central column with the requested sign; all others are unchanged. The inverse
transvection proves that surjectivity survives this concrete geometric move.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

-- Keep matching from expanding the homology maps through unknown finite indices.
-- The coefficient calculations below unfold the matrix explicitly.
attribute [local irreducible] canonicalMiddleMatrix

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}

variable [PathConnectedSpace M]


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
