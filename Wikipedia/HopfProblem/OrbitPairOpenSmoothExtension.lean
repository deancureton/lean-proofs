module

public import Mathlib.Geometry.Manifold.ContMDiff.Basic

@[expose] public section

/-!
# Smooth extension across the outer edge of a gauge neighborhood

A smooth function on an open set that equals a fixed value off a
closed subset contained in that open set extends smoothly by the
fixed value. The closed subset need not be compact. This distinction
allows a gauge correction to approach a deleted fixed sphere while
remaining supported away from the outer edge of its normal tube.
-/

noncomputable section

open Set Topology Filter
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair

variable {V H M W K N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace K]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
  (I : ModelWithCorners ℝ V H) (J : ModelWithCorners ℝ W K)

def openExtend (U : TopologicalSpace.Opens M) (f : U → N) (c : N) (x : M) : N := by
  classical
  exact if hx : x ∈ U then f ⟨x, hx⟩ else c

@[simp] theorem openExtend_on (U : TopologicalSpace.Opens M) (f : U → N) (c : N) (x : U) :
    openExtend U f c x.val = f x := by
  classical
  simp only [openExtend, dif_pos x.property]

theorem openExtend_off (U : TopologicalSpace.Opens M) (f : U → N) (c : N)
    (x : M) (hx : x ∉ U) : openExtend U f c x = c := by
  classical
  simp only [openExtend, dif_neg hx]


theorem openExtend_eq_const_off (U : TopologicalSpace.Opens M) (f : U → N) (c : N)
    (S : Set M) (hf : ∀ x : U, x.val ∉ S → f x = c) (x : M) (hx : x ∉ S) :
    openExtend U f c x = c := by
  classical
  by_cases hU : x ∈ U
  · exact (openExtend_on U f c ⟨x, hU⟩).trans (hf ⟨x, hU⟩ hx)
  · exact openExtend_off U f c x hU


end Wikipedia.HopfProblem.OrbitPair
