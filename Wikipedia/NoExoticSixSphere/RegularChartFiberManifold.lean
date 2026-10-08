module

public import Wikipedia.NoExoticSixSphere.ChartFiberRegularity
public import Wikipedia.NoExoticSixSphere.ChartFiberAtlas

@[expose] public section

/-!
# The actual fiber of a regular manifold-valued map

The zero fiber inside the valid chart preimage is homeomorphic to the original
fiber. Pulling its constructed level atlas back along this subspace
homeomorphism gives the original fiber its smooth structure and smooth
inclusion. This does not modify a pre-existing candidate sphere's atlas.
-/

open scoped Manifold ContDiff
open Set Module

namespace NoExoticSixSphere

variable {B H M C H' N F : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]


end NoExoticSixSphere
