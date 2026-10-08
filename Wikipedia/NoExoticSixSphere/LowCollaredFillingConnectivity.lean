module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.NoExoticSixSphere.LowCollaredFillingFramedComparison
public import Wikipedia.NoExoticSixSphere.SquareDoubleFundamentalGroup
public import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenPiOneElimination
public import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenH2Elimination

@[expose] public section

/-!
# One-sided two-connected framed fillings with a possibly disconnected boundary

The actual positive half is assumed path connected. Its fundamental group
is proved finitely generated using its actual compact smooth square double.
The boundary's second homology vanishes, but the boundary need not be
connected. Finite native circle and two-sphere surgeries then
make the positive half two-connected, retaining the full original induced
boundary frame through the constructed filling comparison.

No ambient simple connectivity or control of the negative half is needed.
Initial positive-half connectedness remains an explicit input; it is not
deduced for a general disconnected-boundary cylinder here.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.LowCollaredFillingConnectivity

open GLOrthonormalization Wikipedia.HopfProblem
open DegreeCollapse SingularMayerVietoris

variable {B : Type} [TopologicalSpace B] [Subsingleton (SingularHomology B 2)]
  (S : LowCollaredSevenState B) [PathConnectedSpace S.PositiveHalf] (b : B)

theorem exists_twoConnected_positive_state :
    ∃ U : LowCollaredSevenState B, S.Reachable U ∧
      SimplyConnectedSpace U.PositiveHalf ∧
      Subsingleton (SingularHomology U.PositiveHalf 2) ∧
      (∀ w : U.PositiveHalf, Subsingleton (π_ 2 U.PositiveHalf w)) ∧
      Nonempty (LowCollaredFillingBoundary.Comparison S U b) := by
  let : Group.FG (FundamentalGroup S.PositiveHalf (S.positiveBasepoint b)) :=
    S.positiveHalf_fundamentalGroup_finite b (S.positiveBasepoint b)
  obtain ⟨V, hSV, hV⟩ := S.exists_simplyConnected_of_finitelyGenerated b
  let := hV
  obtain ⟨U, hVU, hU, hU2⟩ := V.exists_h2_zero
  let := hU
  let := hU2
  have hSU := hSV.trans hVU
  refine ⟨U, hSU, hU, hU2, ?_, LowCollaredFillingBoundary.comparison_of_reachable hSU b⟩
  intro w
  exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv w).injective.subsingleton


end NoExoticSixSphere.LowCollaredFillingConnectivity
