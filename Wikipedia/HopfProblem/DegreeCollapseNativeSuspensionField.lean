module

public import Wikipedia.HopfProblem.DegreeCollapseCompactIsotopySuspension
public import Wikipedia.HopfProblem.DegreeCollapseNativeVerticalReplacement
public import Wikipedia.SmoothSixDPoincare.PartialChartIntegralCurve

@[expose] public section

/-!
# Inserting a compact suspension field in a native height chart

The actual chart height computes the native directional derivative.
Compact replacement retains the zero set and all exterior field germs,
while a model field of vertical speed one retains height speed minus one.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E B M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace M] [ChartedSpace B M]

theorem mvfderiv_native_height_field
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ f) {b : ℝ}
    (hheight : ∀ p ∈ Φ.source, f (Φ p) = b - p.2)
    (W : (E × ℝ) → E × ℝ) {x : M} (hx : x ∈ Φ.target) :
    mvfderiv 𝓘(ℝ, B) f x (FlowConstruction.partialChartField Φ.symm W x) =
      -(W (Φ.symm x)).2 := by
  let q := Φ.symm x
  have hq : q ∈ Φ.source := Φ.map_target' hx
  have heq : (f ∘ Φ) =ᶠ[𝓝 q] (fun p : E × ℝ => b - p.2) := by
    filter_upwards [Φ.open_source.mem_nhds hq] with p hp
    exact hheight p hp
  have hd : fderiv ℝ (f ∘ Φ) q = fderiv ℝ (fun p : E × ℝ => b - p.2) q :=
    heq.fderiv_eq
  rw [FlowConstruction.mvfderiv_partialChartField hf Φ.symm W hx]
  change fderiv ℝ (f ∘ Φ) q (W q) = -(W q).2
  rw [hd]
  have hh := (hasFDerivAt_const (𝕜 := ℝ) b q).sub
    (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
  have hh' : fderiv ℝ (fun p : E × ℝ => b - p.2) q =
      (0 : (E × ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.snd ℝ E ℝ := hh.fderiv
  rw [hh']
  simp

variable [FiniteDimensional ℝ B] [IsManifold 𝓘(ℝ, B) ∞ M] [T2Space M]


end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
