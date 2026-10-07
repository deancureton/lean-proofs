module

public import Wikipedia.HopfProblem.DegreeCollapseCubicFlowCylinder
public import Wikipedia.HopfProblem.DegreeCollapseNativeRationalFieldChart
public import Mathlib.Dynamics.Flow

@[expose] public section

/-!
# Endpoint flow coordinates with the original axis clock

The explicit cubic cylinder transports the vertical coordinate field to
the cubic field. Composing it with a clock-normalized native endpoint
chart gives actual regular flow coordinates. The chart's axis agrees
with the original complete orbit on a full germ at the constructed slice.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ}

/-- The actual cubic cylinder derivative sends vertical velocity to the cubic field. -/
theorem cubicFlowCylinder_pushforward_vertical (σ : Fin m → ℝ) (a : ℝ)
    (p : (Fin m → ℝ) × ℝ) :
    fderiv ℝ (cubicFlowCylinder σ a) p (0, 1) =
      cubicDescent σ (-(a ^ 2)) (cubicFlowCylinder σ a p) := by
  have hd := ((contDiff_cubicFlowCylinder σ a).differentiable (by simp) p).hasFDerivAt
    |>.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have hd' := hasDerivAt_cubicFlowCylinder σ a p.1 p.2
  exact hd.unique hd'

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
