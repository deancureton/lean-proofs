module

public import Wikipedia.HopfProblem.DegreeCollapseFlowSheetCoordinates
public import Wikipedia.HopfProblem.DegreeCollapsePhaseCylinderChart

@[expose] public section

/-!
# Native immersions of the actual endpoint flow sheets

The transverse phase chart and original cylinder form a genuine native
partial diffeomorphism. Its restriction along an injective linear sheet
has injective native derivative. The exact flow-coordinate germ transfers
this to the actual complete-flow sheet.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {B D Z E M : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem native_partial_chart_linear_immersion
    (P : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    (h0 : (0 : D) ∈ P.source) (L : B →L[ℝ] D) (hL : Injective L) :
    Injective (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) (fun x => P (L x)) 0) := by
  have hp : L (0 : B) ∈ P.source := by simpa only [map_zero] using h0
  have hd : MDifferentiableAt 𝓘(ℝ, B) 𝓘(ℝ, D) L 0 := L.differentiableAt.mdifferentiableAt
  change Injective (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) (P ∘ L) 0)
  rw [mfderiv_comp 0 (P.mdifferentiableAt (by simp) hp) hd, map_zero,
    mfderiv_eq_fderiv, L.fderiv]
  exact (PartialChart.bijective_mfderiv P h0).injective.comp hL


end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
