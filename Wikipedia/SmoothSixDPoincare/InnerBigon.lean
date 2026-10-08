module
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.SmoothSixDPoincare.BigonBallHomeomorph
public import Wikipedia.SmoothSixDPoincare.CenteredParametrization

@[expose] public section

/-!
# Move the whole cornered boundary strictly into the bigon interior

Contract about the actual interior point `(0,h/2)`, rather than the boundary
point `(0,0)`. A factor strictly between zero and one sends the whole disk
into its interior. Factors sufficiently close to one retain the boundary
inside any prescribed open boundary neighborhood.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

/-- Affine contraction about the explicit interior point of the bigon. -/
def innerBigonMap (h r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - r) • (0, h / 2) + r • p

theorem innerBigonMap_one (h : ℝ) (p : ℝ × ℝ) : innerBigonMap h 1 p = p := by
  simp only [innerBigonMap, sub_self, zero_smul, one_smul, zero_add]

theorem contDiff_innerBigonMap (h : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => innerBigonMap h z.1 z.2) := by
  unfold innerBigonMap
  fun_prop

/-- The inward affine map is a genuine global diffeomorphism whenever its factor is nonzero. -/
def innerBigonDiffeomorph (h r : ℝ) (hr : r ≠ 0) :
    Diffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ where
  toEquiv := {
    toFun := innerBigonMap h r
    invFun := fun p => r⁻¹ • (p - (1 - r) • (0, h / 2))
    left_inv := by
      intro p
      simp only [innerBigonMap, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul]
    right_inv := by
      intro p
      simp only [innerBigonMap, smul_smul, mul_inv_cancel₀ hr, one_smul]
      abel }
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (innerBigonMap h r)
    apply ContDiff.contMDiff
    unfold innerBigonMap
    fun_prop
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun p : ℝ × ℝ => r⁻¹ • (p - (1 - r) • (0, h / 2)))
    apply ContDiff.contMDiff
    fun_prop

/-- The actual native derivative of the inward affine map is bijective everywhere. -/
theorem bijective_mfderiv_innerBigonMap (h r : ℝ) (hr : r ≠ 0) (p : ℝ × ℝ) :
    Bijective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (innerBigonMap h r) p) := by
  exact PartialChart.bijective_mfderiv (innerBigonDiffeomorph h r hr).toPartialDiffeomorph
    (mem_univ p)

/-- Every point, including both arcs and both corners, moves into the open bigon. -/
theorem innerBigonMap_mem_interior {h r : ℝ} (hh : 0 < h) (hr : r ∈ Ioo (0 : ℝ) 1)
    {p : ℝ × ℝ} (hp : p ∈ bigon h) : innerBigonMap h r p ∈ interior (bigon h) :=
  (convex_bigon hh.le).combo_interior_self_mem_interior (bigon_center_mem_interior hh)
    hp (sub_pos.mpr hr.2) hr.1.le (by ring)


end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
