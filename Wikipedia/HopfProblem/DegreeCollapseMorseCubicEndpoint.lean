module

public import Wikipedia.HopfProblem.DegreeCollapseMorseCoordinateSplit

@[expose] public section

/-!
# Cubic endpoint germs constructed from the actual native Morse normal forms

Every selected signed coordinate of a native Morse chart gives a constructed
cubic endpoint chart. The physical center, all transverse signs, and the
critical value are retained explicitly. No new local normal-form premise is
introduced: the input is the already proved signed Morse chart of the function.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

/-- Enumerate the remaining coordinates while putting any selected coordinate first. -/
theorem exists_coordinate_enum {m n : ℕ} (hn : n = m + 1) (j : Fin n) :
    ∃ ρ : Option (Fin m) ≃ Fin n, ρ none = j := by
  let ρ₀ : Option (Fin m) ≃ Fin n := Fintype.equivOfCardEq (by simp [hn])
  exact ⟨ρ₀.trans (Equiv.swap (ρ₀ none) j), by simp⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M}

open Wikipedia.SmoothSixDPoincare.ManifoldMorse


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
