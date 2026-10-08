module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapsePositiveSixFourTrade

@[expose] public section

/-!
# Only positive middle handles and the unique maximum remain

The supported six-to-four trade contradicts the secondary outer-index
minimum whenever a positive index-six point exists. Combining it with
the already proved low-index elimination and unique positive maximum
leaves only indices two through five below that maximum. The state,
positive half, original zero boundary, and native atlases are unchanged.
A collared state is supplied. This theorem does not construct the original
threefold's initial filling or recognize its positive half as a smooth disk.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}

namespace ExcellentMorsePresentation

theorem no_positive_index_six_of_outer_minimal
    (P : S.ExcellentMorsePresentation)
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (hminimal : ∀ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) P.function).ncard ≤
        (criticalPoints (Vector 7) Q.function).ncard)
    (hcost : ∀ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) Q.function).ncard =
        (criticalPoints (Vector 7) P.function).ncard →
      nativeMorseCount (Vector 7) P.function 1 + nativeMorseCount (Vector 7) P.function 6 ≤
        nativeMorseCount (Vector 7) Q.function 1 + nativeMorseCount (Vector 7) Q.function 6)
    (q : criticalPoints (Vector 7) P.function) (hq : 0 < P.function q) :
    nativeMorseIndex (Vector 7) P.function q ≠ 6 := by
  intro hqsix
  obtain ⟨Q, hcard, hsix, _, hother, _⟩ := P.exists_positive_six_to_four_handle_trade
    horder (P.positive_index_seven_unique_of_minimal hminimal) q hq hqsix
  have hmin := hcost Q hcard
  have hone := hother 1 (by decide) (by decide)
  omega

end ExcellentMorsePresentation


end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
