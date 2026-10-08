module

public import Wikipedia.HopfProblem.DegreeCollapseCubicTransverseNegation

@[expose] public section

/-!
# Constructing compatible endpoint orientations in odd transverse rank

Invertibility of the actual transition blocks makes their determinants
nonzero. Keep the right endpoint chart if the signs already agree; otherwise
negate its transverse coordinates. This preserves its axis and every signed
cubic equation, while supplying the sign condition for native chart gluing.
-/

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

omit [FiniteDimensional ℝ V] in
theorem det_ne_zero_of_isInvertible (T : V →L[ℝ] V) (hT : T.IsInvertible) :
    T.toLinearMap.det ≠ 0 := by
  obtain ⟨e, he⟩ := hT
  rw [← he]
  exact e.toLinearEquiv.isUnit_det'.ne_zero


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
