module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseExactCubicBirth
public import Wikipedia.HopfProblem.DegreeCollapsePositiveCubicCoordinates
public import Wikipedia.HopfProblem.DegreeCollapseNativeCubicCancellation

@[expose] public section

/-!
# A compact birth template for a linear height function

Global positive-cubic coordinates transport the supported birth to a smooth
function equal to the first coordinate off a compact set. Its critical set
is exactly the transported pair, and both complete negative-cubic endpoint
germs survive. No compatibility between a chosen native chart and a cubic
normal form is assumed.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem fderiv_comp_diffeomorph_symm_zero_iff
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : V ≃ₘ[ℝ] V) {g : V → ℝ} (hg : ContDiff ℝ ∞ g) (p : V) :
    fderiv ℝ (g ∘ D.symm) p = 0 ↔ fderiv ℝ g (D.symm p) = 0 := by
  have h := LocalFunctionReplacement.replace_critical_iff D.toPartialDiffeomorph
    (fun _ => 0) hg (mem_univ p)
  have heq : LocalFunctionReplacement.replace D.toPartialDiffeomorph (fun _ => 0) g =
      g ∘ D.symm := by
    funext x
    exact LocalFunctionReplacement.replace_of_mem D.toPartialDiffeomorph
      (fun _ => 0) g (mem_univ x)
  rw [heq, mfderiv_eq_fderiv] at h
  exact h


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
