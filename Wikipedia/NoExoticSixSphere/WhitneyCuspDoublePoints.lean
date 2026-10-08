module

public import Wikipedia.NoExoticSixSphere.WhitneyCuspSingularLocus
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Exact double-point birth in the cusp family

At nonpositive parameter the map is injective. At positive parameter its
only distinct equal-image pairs are the two orderings of the points on the
last coordinate axis with coordinates `sqrt t` and `-sqrt t`.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.WhitneyCusp

open GLOrthonormalization

theorem axis_ne_neg {z : ℝ} (hz : z ≠ 0) : axis z ≠ axis (-z) := by
  intro h
  have he := axis_injective h
  exact hz (by linarith)

theorem map_eq_iff (t : ℝ) (x y : Vector 3) :
    map t x = map t y ↔ x = y ∨
      ∃ z : ℝ, z ≠ 0 ∧ z ^ 2 = t ∧ x = axis z ∧ y = axis (-z) := by
  constructor
  · intro h
    by_cases hxy : x = y
    · exact Or.inl hxy
    · have h₀ : x 0 = y 0 := congrArg (fun w : Vector 6 ↦ w 0) h
      have h₁ : x 1 = y 1 := congrArg (fun w : Vector 6 ↦ w 1) h
      have h₂ : x 2 ^ 2 = y 2 ^ 2 := congrArg (fun w : Vector 6 ↦ w 2) h
      have h₃ : x 0 * x 2 = y 0 * y 2 := congrArg (fun w : Vector 6 ↦ w 3) h
      have h₄ : x 1 * x 2 = y 1 * y 2 := congrArg (fun w : Vector 6 ↦ w 4) h
      have h₅ : x 2 ^ 3 - t * x 2 = y 2 ^ 3 - t * y 2 :=
        congrArg (fun w : Vector 6 ↦ w 5) h
      have hy₂ : y 2 = -x 2 := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp h₂ with hz | hz
        · exact (hxy (by
            ext i
            fin_cases i
            · exact h₀
            · exact h₁
            · exact hz)).elim
        · linarith
      have hz : x 2 ≠ 0 := by
        intro hx₂
        apply hxy
        ext i
        fin_cases i
        · exact h₀
        · exact h₁
        · change x 2 = y 2
          rw [hy₂, hx₂, neg_zero]
      have hx₀ : x 0 = 0 := by
        rw [← h₀, hy₂] at h₃
        have hp : x 0 * x 2 = 0 := by nlinarith
        exact (mul_eq_zero.mp hp).resolve_right hz
      have hx₁ : x 1 = 0 := by
        rw [← h₁, hy₂] at h₄
        have hp : x 1 * x 2 = 0 := by nlinarith
        exact (mul_eq_zero.mp hp).resolve_right hz
      have ht : x 2 ^ 2 = t := by
        rw [hy₂] at h₅
        have hp : x 2 * (x 2 ^ 2 - t) = 0 := by nlinarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hz)
      refine Or.inr ⟨x 2, hz, ht, ?_, ?_⟩
      · ext i
        fin_cases i
        · exact hx₀
        · exact hx₁
        · rfl
      · ext i
        fin_cases i
        · exact h₀.symm.trans hx₀
        · exact h₁.symm.trans hx₁
        · exact hy₂
  · rintro (rfl | ⟨z, _, ht, rfl, rfl⟩)
    · rfl
    · rw [← ht]
      ext i
      fin_cases i <;> simp [map, axis]
      ring



end NoExoticSixSphere.WhitneyCusp
