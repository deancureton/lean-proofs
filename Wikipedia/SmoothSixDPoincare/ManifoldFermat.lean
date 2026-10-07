module

public import Wikipedia.SmoothSixDPoincare.ManifoldCriticalPoints
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-!
# Fermat's theorem for the native manifold derivative

An extremum in the original manifold topology remains an extremum in a
genuine smooth chart. Euclidean Fermat then proves that the native
manifold derivative vanishes.
-/

noncomputable section

open Set Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {p : M}

/-- A local minimum is a critical point for the actual native manifold derivative. -/
theorem mem_criticalPoints_of_localMin
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hmin : IsLocalMin f p) :
    p ∈ criticalPoints E f := by
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hp : p ∈ e.source := mem_chart_source E p
  apply (mem_criticalPoints_iff hf he hp).mpr
  have hmin' : IsLocalMin f (e.symm (e p)) := by rw [e.left_inv hp]; exact hmin
  exact (hmin'.comp_continuous (e.continuousAt_symm (e.map_source hp))).fderiv_eq_zero

/-- A local maximum is a critical point for the actual native manifold derivative. -/
theorem mem_criticalPoints_of_localMax
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hmax : IsLocalMax f p) :
    p ∈ criticalPoints E f := by
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hp : p ∈ e.source := mem_chart_source E p
  apply (mem_criticalPoints_iff hf he hp).mpr
  have hmax' : IsLocalMax f (e.symm (e p)) := by rw [e.left_inv hp]; exact hmax
  exact (hmax'.comp_continuous (e.continuousAt_symm (e.map_source hp))).fderiv_eq_zero

variable [CompactSpace M]


end Wikipedia.SmoothSixDPoincare.ManifoldMorse
