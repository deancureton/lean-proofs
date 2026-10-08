module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseMiddleSuspensionSurjective
public import Wikipedia.HopfProblem.DegreeCollapseSixthStemFourValues

@[expose] public section

/-!
# The entire original stable sixth stem has two specified possible values

All three required native desuspensions are now surjective. Consequently
the S4 stage covers the full stable sixth stem, and the existing
quaternionic-kernel calculation applies to EVERY stable class.
The alternatives are the identity and the actual third-stem square.
This proves an upper bound of two, not nontriviality or Arf detection.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SixthStemTwoValues

open NoExoticSixSphere CubicalStableSix StableThirdComposition

theorem sphere_five_stable_surjective : Function.Surjective (ofNative (k := 3)) := by
  intro z
  obtain ⟨x, hx⟩ := SixSphereDesuspension.stable_surjective z
  obtain ⟨a, rfl⟩ := MiddleSuspensionSurjective.middle_suspension_surjective x
  exact ⟨a, (ofNative_stepHom 3 a).symm.trans hx⟩

theorem sphere_four_stable_surjective : Function.Surjective (ofNative (k := 2)) := by
  intro z
  obtain ⟨x, hx⟩ := sphere_five_stable_surjective z
  obtain ⟨a, rfl⟩ := FourSphereDesuspension.suspension_surjective x
  exact ⟨a, (ofNative_stepHom 2 a).symm.trans hx⟩

theorem stable_eq_one_or_square (z : CubicalStableSix.Group) :
    z = 1 ∨ z = stableSquare := by
  obtain ⟨x, rfl⟩ := sphere_four_stable_surjective z
  exact SixthSphereFourImage.stable_eq_one_or_square x

theorem stable_pow_two (z : CubicalStableSix.Group) : z ^ 2 = 1 := by
  rcases stable_eq_one_or_square z with h | h
  · rw [h, one_pow]
  · rw [h, stableSquare_pow_two]

def twoValues (b : Bool) : CubicalStableSix.Group := if b then stableSquare else 1

theorem twoValues_surjective : Function.Surjective twoValues := by
  intro z
  rcases stable_eq_one_or_square z with h | h
  · exact ⟨false, h.symm⟩
  · exact ⟨true, h.symm⟩

theorem card_le_two : Nat.card CubicalStableSix.Group ≤ 2 := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using
    Nat.card_le_card_of_surjective twoValues twoValues_surjective

theorem native_card_le_two (k : ℕ) (hk : 6 ≤ k) :
    Nat.card (StableSixSphereMaps.NativeStage k) ≤ 2 :=
  (Nat.card_congr (stableMulEquiv k hk).toEquiv).trans_le card_le_two



theorem polynomial_square_stable :
    ofNative QuaternionicHopf.suspendedSmashClass = stableSquare := by
  rw [QuaternionicHopf.suspendedSmashClass_eq]
  have hi : stableSquare⁻¹ = stableSquare := by
    apply mul_left_cancel (a := stableSquare)
    rw [mul_inv_cancel, ← pow_two, stableSquare_pow_two]
  exact SixthStemSquareComparison.stableClass_eq_inverse.trans hi

theorem stable_eq_one_or_polynomial_square (z : CubicalStableSix.Group) :
    z = 1 ∨ z = ofNative QuaternionicHopf.suspendedSmashClass := by
  rw [polynomial_square_stable]
  exact stable_eq_one_or_square z



end Wikipedia.HopfProblem.DegreeCollapse.SixthStemTwoValues
