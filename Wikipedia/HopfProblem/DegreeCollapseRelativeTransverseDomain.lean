module

public import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

@[expose] public section

/-!
# Genuine relative transverse charts in both endpoint slice domains

Restrict the actual relative transverse map at source and target to
prescribed positive-radius balls. Both actual maps are retained, zero
remains in the source and fixed, and every remaining point lies in the
two required endpoint slice domains.
-/

noncomputable section

open Set Function Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A fixed-origin partial diffeomorphism can be restricted inside any
prescribed source and image balls, retaining its actual coordinate map. -/
theorem exists_transverse_chart_in_balls
    (H : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞)
    (h0 : (0 : Z) ∈ H.source) (hfix : H 0 = 0) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∃ G : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞,
      (0 : Z) ∈ G.source ∧ G 0 = 0 ∧ (G : Z → Z) = H ∧ G.source ⊆ H.source ∧
      G.target ⊆ H.target ∧ ∀ z ∈ G.source, ‖z‖ < r ∧ ‖G z‖ < s := by
  let A := PartialChart.restrictTarget H (isOpen_ball : IsOpen (ball (0 : Z) s))
  let G := PartialChart.restrictSource A (isOpen_ball : IsOpen (ball (0 : Z) r))
  have hG0 : (0 : Z) ∈ G.source := by
    change (0 ∈ H.source ∧ H 0 ∈ ball (0 : Z) s) ∧ (0 : Z) ∈ ball 0 r
    exact ⟨⟨h0, hfix.symm ▸ mem_ball_self hs⟩, mem_ball_self hr⟩
  refine ⟨G, hG0, hfix, rfl, fun _ hz => hz.1.1, fun _ hz => hz.1.1, ?_⟩
  intro z hz
  have hzr : z ∈ ball (0 : Z) r := hz.2
  have hzs : G z ∈ ball (0 : Z) s := hz.1.2
  exact ⟨by simpa only [mem_ball, dist_zero_right] using hzr,
    by simpa only [mem_ball, dist_zero_right] using hzs⟩


end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
