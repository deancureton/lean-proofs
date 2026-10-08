module

public import Wikipedia.HopfProblem.OrbitPairNativeLocalInjectivity

@[expose] public section

/-!
# Saturated two-branch neighborhoods for a closed native map

Two disjoint compact source sets with injective native derivatives and
injective restrictions admit disjoint injectivity neighborhoods. If their
union is saturated and the whole map is closed, shrink a target
neighborhood so its entire preimage lies in these two branches. Both
source and target neighborhoods may be restricted to prescribed open sets.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeImmersion

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]


end Wikipedia.HopfProblem.OrbitPair.NativeImmersion
