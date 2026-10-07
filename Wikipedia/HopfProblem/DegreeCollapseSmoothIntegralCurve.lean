module

public import Wikipedia.NoExoticSixSphere.LocalInverse
public import Wikipedia.SmoothSixDPoincare.PartialChartIntegralCurve
public import Mathlib.Analysis.ODE.PicardLindelof

@[expose] public section

/-!
# Smoothness of native integral curves

In a genuine partial chart the curve satisfies the pulled-back ordinary ODE.
The regularity theorem for that ODE gives smoothness on a closed time interval
around each time. Composing with the actual inverse chart retains the atlas.
-/

noncomputable section

open Set Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The ordinary vector field in a given native coordinate chart. -/
def coordinateField (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞) (z : E) : E :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm V z

/-- The inverse pullback is exactly the forward chart differential. -/
theorem coordinateField_chart
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞) {x : M} (hx : x ∈ e.source) :
    coordinateField (V := V) e (e x) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (V x) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have h₂ := he.comp_symm_deriv (e'.map_source hx)
  rw [e'.left_inv hx] at h₂
  have hi := ContinuousLinearMap.inverse_eq (he.symm_comp_deriv hx) h₂
  let A : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e'.symm (e' x)
  let B : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e' x
  have hAB : A.inverse = B := hi
  have hvx : (show E from V (e'.symm (e' x))) = V x :=
    congrArg (fun y : M => (show E from V y)) (e'.left_inv hx)
  change A.inverse (V (e'.symm (e' x))) = B (V x)
  rw [hAB]
  exact congrArg B hvx

variable [CompleteSpace E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A smooth native field is smooth in the chosen ordinary coordinates. -/
theorem contDiffOn_coordinateField
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞) :
    ContDiffOn ℝ ∞ (coordinateField (V := V) e) e.target := by
  apply contMDiffOn_vectorSpace_iff_contDiffOn.mp
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  intro z hz
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm z).IsInvertible :=
    ⟨he.symm.mfderiv hz, rfl⟩
  exact ((hV (e.symm z)).mpullback_vectorField_preimage
    ((e.symm.contMDiffOn z hz).contMDiffAt (e.open_target.mem_nhds hz))
    hinv (by simp)).contMDiffWithinAt

omit [CompleteSpace E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A native integral curve satisfies the ordinary coordinate-field equation. -/
theorem hasDerivAt_coordinate_integralCurve
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ V) {t : ℝ} (ht : γ t ∈ e.source) :
    HasDerivAt (e ∘ γ) (coordinateField (V := V) e (e (γ t))) t := by
  have he := ((e.contMDiffOn (γ t) ht).contMDiffAt
    (e.open_source.mem_nhds ht)).mdifferentiableAt (by simp)
  have hd := he.hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (γ t)
    ((NormedSpace.fromTangentSpace t r) • V (γ t)) =
    (NormedSpace.fromTangentSpace t r) • coordinateField (V := V) e (e (γ t))
  rw [map_smul, coordinateField_chart e ht]
  rfl


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
