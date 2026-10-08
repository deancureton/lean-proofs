module

public import Wikipedia.HopfProblem.OrbitPairDeterminantSignCover
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Scalar orientation weights and endpoint determinant signs

A Boolean orientation choice has weight `1` or `-1`. This translates the
determinant-sign action into strict real inequalities and permits the
source and target orientation factors to be canceled in a comparison of
two actual corner determinants.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.OrientationWeights

open DeterminantSignCover

def weight (b : Bool) : ℝ := if b then -1 else 1



theorem weight_xor (b c : Bool) : weight (Bool.xor b c) = weight b * weight c := by
  cases b <;> cases c <;> norm_num [weight]

theorem action_eq_iff_product_pos (d e : ℝ) (hd : d ≠ 0) (he : e ≠ 0) (b c : Bool) :
    action d b = action e c ↔ 0 < (weight b * d) * (weight c * e) := by
  rcases lt_or_gt_of_ne hd with hd | hd <;> rcases lt_or_gt_of_ne he with he | he <;>
    cases b <;> cases c <;>
    simp [action, weight, mul_pos_iff, hd, he, not_lt_of_ge hd.le, not_lt_of_ge he.le]
  all_goals first
    | exact he.le
    | exact (mul_pos_of_neg_of_neg hd he).le
    | exact mul_neg_of_neg_of_pos hd he
    | exact mul_neg_of_pos_of_neg hd he

theorem action_ne_iff_product_neg (d e : ℝ) (hd : d ≠ 0) (he : e ≠ 0) (b c : Bool) :
    action d b ≠ action e c ↔ (weight b * d) * (weight c * e) < 0 := by
  rcases lt_or_gt_of_ne hd with hd | hd <;> rcases lt_or_gt_of_ne he with he | he <;>
    cases b <;> cases c <;>
    simp [action, weight, mul_neg_iff, hd, he, not_lt_of_ge hd.le, not_lt_of_ge he.le]
  all_goals exact mul_pos_of_neg_of_neg hd he



end Wikipedia.HopfProblem.OrbitPair.OrientationWeights
