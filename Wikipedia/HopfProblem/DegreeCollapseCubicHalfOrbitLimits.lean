module

public import Wikipedia.HopfProblem.DegreeCollapseCubicCurveBox

@[expose] public section

/-!
# Cubic half-orbit limits and endpoint-box invariance

The correct transverse coordinate planes have the actual cubic endpoint
limits. Convergence together with the proved between-endpoints box estimate
keeps every point of the relevant half-orbit inside its endpoint box.
-/

noncomputable section

open Set Function Filter Metric
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ}



/-- A convergent cubic forward half-orbit cannot leave its endpoint box,
by applying the finite-segment estimate to arbitrarily late points. -/
theorem cubicFlowCylinder_forward_stays_box (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (z : Fin m → ℝ) {c r T : ℝ} (hr : 0 < r)
    (hlim : Tendsto (fun t => cubicFlowCylinder σ a (z, t)) atTop
      (𝓝 (c, (0 : Fin m → ℝ))))
    (hT : cubicFlowCylinder σ a (z, T) ∈ closedBall (c, (0 : Fin m → ℝ)) r)
    {t : ℝ} (ht : T ≤ t) :
    cubicFlowCylinder σ a (z, t) ∈ closedBall (c, (0 : Fin m → ℝ)) r := by
  have hnear : ∀ᶠ u in atTop, cubicFlowCylinder σ a (z, u) ∈
      ball (c, (0 : Fin m → ℝ)) r := hlim.eventually (ball_mem_nhds _ hr)
  obtain ⟨u, hu, hut⟩ := (hnear.and (eventually_ge_atTop t)).exists
  exact cubicFlowCylinder_stays_axis_ball σ ha z ⟨ht, hut⟩ hT (ball_subset_closedBall hu)

/-- The same endpoint-box control holds on the backward half-orbit. -/
theorem cubicFlowCylinder_backward_stays_box (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (z : Fin m → ℝ) {c r T : ℝ} (hr : 0 < r)
    (hlim : Tendsto (fun t => cubicFlowCylinder σ a (z, t)) atBot
      (𝓝 (c, (0 : Fin m → ℝ))))
    (hT : cubicFlowCylinder σ a (z, T) ∈ closedBall (c, (0 : Fin m → ℝ)) r)
    {t : ℝ} (ht : t ≤ T) :
    cubicFlowCylinder σ a (z, t) ∈ closedBall (c, (0 : Fin m → ℝ)) r := by
  have hnear : ∀ᶠ u in atBot, cubicFlowCylinder σ a (z, u) ∈
      ball (c, (0 : Fin m → ℝ)) r := hlim.eventually (ball_mem_nhds _ hr)
  obtain ⟨u, hu, hut⟩ := (hnear.and (eventually_le_atBot t)).exists
  exact cubicFlowCylinder_stays_axis_ball σ ha z ⟨hut, ht⟩ (ball_subset_closedBall hu) hT

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
