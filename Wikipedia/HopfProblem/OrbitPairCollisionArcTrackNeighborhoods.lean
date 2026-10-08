module

public import Wikipedia.HopfProblem.OrbitPairCollisionArcNeighborhoods
public import Wikipedia.HopfProblem.OrbitPairSaturatedTwoBranchNeighborhood
public import Wikipedia.HopfProblem.OrbitPairNativeFamilyTrack
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-!
# Saturated branch neighborhoods in the full time-retaining track

The track `(t,x) ↦ (t,F(t,x))` is proper when the spatial source is compact:
its projection to time is the proper product projection. The exact slice
fibers along the two arcs determine their complete track fibers because
equality of track values forces equality of times.

The resulting open target neighborhood controls all source times. Its
entire preimage splits into two disjoint injective immersive branches,
contained in any prescribed time band about the selected collision pair.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

theorem track_isProperMap {M N : Type*}
    [TopologicalSpace M] [CompactSpace M] [TopologicalSpace N] [T2Space N]
    {F : ℝ × M → N} (hF : Continuous F) : IsProperMap (track F) := by
  apply isProperMap_of_comp_of_t2 (continuous_fst.prodMk hF)
    (continuous_fst : Continuous (Prod.fst : ℝ × N → ℝ))
  exact isProperMap_fst_of_compactSpace

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [PathConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [T2Space N]


variable [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N] [CompactSpace M]


end Wikipedia.HopfProblem.OrbitPair.NativeFamily
