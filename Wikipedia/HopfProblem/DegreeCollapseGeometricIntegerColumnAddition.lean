module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseIntegerColumnSlide

@[expose] public section

/-!
# Every integer column addition is realized by the actual common-cut family

The finite geometric iteration has its exact elementary matrix in the
unchanged basis. Its inverse preserves surjectivity. All cut hypotheses,
protected maps, critical chart germs and lower basin orbit sets are retained.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

attribute [local irreducible] canonicalMiddleMatrix

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M] {f : M → ℝ}


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
