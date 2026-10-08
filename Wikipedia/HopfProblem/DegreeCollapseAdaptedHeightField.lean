module

public import Mathlib.Geometry.Manifold.Algebra.Structures

public import Wikipedia.SmoothSixDPoincare.RegularBandHeight
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

@[expose] public section

/-!
# Height normalization of a supplied descending field

The field is rescaled, not replaced by unrelated local directions. A smooth
cutoff supported in the regular locus removes the apparent singularity at
critical points. On its unit plateau the exact field is `V / df(V)`.
-/

noncomputable section

open Set Manifold Filter
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The actual directional derivative of a smooth function along a smooth field is smooth. -/
theorem contMDiff_directionalDerivative
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) := by
  have ht := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hV
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp ht

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A quotient with numerator supported where the denominator is nonzero is globally smooth. -/
theorem contMDiff_supported_division {χ D : M → ℝ}
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ)
    (hD : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ D)
    (hsupp : ∀ x ∈ tsupport χ, D x ≠ 0) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => χ x / D x) := by
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact (hχ x).div₀ (hD x) (hsupp x hx)
  · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy, zero_div]


variable [CompactSpace M]


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
