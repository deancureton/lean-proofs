module

public import Wikipedia.HopfProblem.DegreeCollapseCubicDescent
public import Wikipedia.HopfProblem.DegreeCollapseFlowClockGerm
public import Wikipedia.HopfProblem.DegreeCollapseLongitudinalDiffeomorph

@[expose] public section

/-!
# Native cubic axes agree with the normalized flow

On the scalar axis the cubic descent field is a scalar multiple of the
actual axis velocity. Normalization by its height speed recovers the
inverse cubic height derivative. The local clock theorem therefore proves
agreement of the whole native endpoint-axis germ with the complete flow.
-/

noncomputable section

open Set Manifold Filter
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ} (σ : Fin m → ℝ)

theorem hasDerivAt_cubic_axis_parameter (t s : ℝ) :
    HasDerivAt (fun r => cubic σ t (r, 0)) (s ^ 2 + t) s := by
  convert RegularHeightCoordinates.scalar_derivative (contDiff_cubic σ t) s 0 using 1
  simp [fderiv_cubic, differential_apply]

variable {B M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace M] [ChartedSpace B M]

omit σ in
/-- The native axis velocity is the actual chart differential of the scalar coordinate. -/
theorem hasMFDerivAt_chart_axis
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞)
    {s : ℝ} (hs : (s, (0 : Fin m → ℝ)) ∈ Φ.source) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, B) (fun r => Φ (r, 0)) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (mfderiv 𝓘(ℝ, Model m) 𝓘(ℝ, B) Φ (s, 0) (1, 0))) := by
  have ha : HasDerivAt (fun r : ℝ => (r, (0 : Fin m → ℝ))) (1, 0) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s 0)
  have hd := (Φ.mdifferentiableAt (by simp) hs).hasMFDerivAt.comp s
    ha.hasFDerivAt.hasMFDerivAt
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change mfderiv 𝓘(ℝ, Model m) 𝓘(ℝ, B) Φ (s, 0)
    ((NormedSpace.fromTangentSpace s r) • (1, 0)) =
      (NormedSpace.fromTangentSpace s r) • mfderiv 𝓘(ℝ, Model m) 𝓘(ℝ, B) Φ (s, 0) (1, 0)
  exact map_smul _ _ _

theorem nativeCubicDescent_chart
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞)
    (t : ℝ) {p : Model m} (hp : p ∈ Φ.source) :
    nativeCubicDescent σ Φ t (Φ p) =
      mfderiv 𝓘(ℝ, Model m) 𝓘(ℝ, B) Φ p (cubicDescent σ t p) := by
  have hh := FlowConstruction.partialChartField_eq_mfderiv_symm Φ.symm
    (cubicDescent σ t) (Φ.map_source' hp)
  have hp' : Φ.symm (Φ p) = p := Φ.left_inv' hp
  exact hh.trans (congrArg (fun q : Model m =>
    (show B from mfderiv 𝓘(ℝ, Model m) 𝓘(ℝ, B) Φ q (cubicDescent σ t q))) hp')

theorem nativeCubicDescent_axis
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞)
    (t : ℝ) {s : ℝ} (hs : (s, (0 : Fin m → ℝ)) ∈ Φ.source) :
    nativeCubicDescent σ Φ t (Φ (s, 0)) =
      (-(s ^ 2 + t)) • mfderiv 𝓘(ℝ, Model m) 𝓘(ℝ, B) Φ (s, 0) (1, 0) := by
  rw [nativeCubicDescent_chart σ Φ t hs, cubicDescent_axis]
  exact map_smul _ _ _

/-- Height normalization recovers the native axis velocity at every regular axis point. -/
theorem normalized_cubic_axis_velocity
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ f) {b t s : ℝ}
    (hmodel : ∀ p ∈ Φ.source, f (Φ p) = b + cubic σ t p)
    (hs : (s, (0 : Fin m → ℝ)) ∈ Φ.source) (hd : s ^ 2 + t ≠ 0) :
    (s ^ 2 + t) •
      ((mvfderiv 𝓘(ℝ, B) f (Φ (s, 0)) (nativeCubicDescent σ Φ t (Φ (s, 0))))⁻¹ •
        nativeCubicDescent σ Φ t (Φ (s, 0))) =
      mfderiv 𝓘(ℝ, Model m) 𝓘(ℝ, B) Φ (s, 0) (1, 0) := by
  have hspeed := nativeCubicDescent_speed σ Φ hf hmodel (Φ.map_source' hs)
  have hp : Φ.symm (Φ (s, 0)) = (s, 0) := Φ.left_inv' hs
  simp only [hp, Pi.zero_apply, mul_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, sub_zero] at hspeed
  let v : TangentSpace 𝓘(ℝ, B) (Φ (s, 0)) :=
    mfderiv 𝓘(ℝ, Model m) 𝓘(ℝ, B) Φ (s, 0) (1, 0)
  have hV : nativeCubicDescent σ Φ t (Φ (s, 0)) = (-(s ^ 2 + t)) • v :=
    nativeCubicDescent_axis σ Φ t hs
  change (s ^ 2 + t) •
    ((mvfderiv 𝓘(ℝ, B) f (Φ (s, 0)) (nativeCubicDescent σ Φ t (Φ (s, 0))))⁻¹ •
      nativeCubicDescent σ Φ t (Φ (s, 0))) = v
  rw [hspeed, hV, smul_smul, smul_smul]
  have hscalar : (s ^ 2 + t) * (-(s ^ 2 + t) ^ 2)⁻¹ * (-(s ^ 2 + t)) = 1 := by
    field_simp
  rw [hscalar, one_smul]

variable [IsManifold 𝓘(ℝ, B) ∞ M]


end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
