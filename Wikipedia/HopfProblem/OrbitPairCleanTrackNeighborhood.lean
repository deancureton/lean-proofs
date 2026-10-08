module

public import Wikipedia.HopfProblem.OrbitPairNativeFamilyTrack
public import Wikipedia.HopfProblem.OrbitPairFamilyDoublePoints
public import Mathlib.Order.Interval.Set.Infinite

@[expose] public section

/-!
# Excluding all other branches near an embedded track point

A finite collision locus leaves an injective slice in every nonempty time
interval. At a point of such a slice, compactness of the spatial source
allows a target neighborhood whose entire track preimage lies in any
prescribed source neighborhood. The compactness argument uses a bounded
time band; no properness of the full noncompact track is assumed.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {M N : Type*}


variable [TopologicalSpace M] [CompactSpace M]
  [TopologicalSpace N] [T2Space N]


end Wikipedia.HopfProblem.OrbitPair.NativeFamily
