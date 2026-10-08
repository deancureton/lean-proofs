module

public import Wikipedia.NoExoticSixSphere.SphereSumNeck

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

@[expose] public section

/-!
# The actual neck inside an original manifold chart

Positive scaling places the entire neck in a prescribed product of balls.
Composition with an actual partial diffeomorphism preserves smoothness,
injectivity, and the injectivity of the native manifold derivative. The
end collars agree exactly with the original sheet parametrizations.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def scaledPair (ε : ℝ) (q : Parameter) : Vector 3 × Vector 3 := ε • pairMap q

theorem contMDiff_scaledPair (ε : ℝ) :
    ContMDiff Model 𝓘(ℝ, Vector 3 × Vector 3) ∞ (scaledPair ε) := by
  have hc : ContMDiff Model 𝓘(ℝ, ℝ) ∞ (fun _ : Parameter ↦ ε) := contMDiff_const
  exact hc.smul contMDiff_pairMap

theorem scaledPair_injective {ε : ℝ} (hε : ε ≠ 0) : Injective (scaledPair ε) := by
  intro q w h
  exact pairMap_injective (smul_right_injective (Vector 3 × Vector 3) hε h)

theorem injective_mfderiv_scaledPair {ε : ℝ} (hε : ε ≠ 0) (q : Parameter) :
    Injective (mfderiv Model 𝓘(ℝ, Vector 3 × Vector 3) (scaledPair ε) q) := by
  let π : Vector 3 × Vector 3 → Vector 3 × Vector 3 := fun z ↦ ε⁻¹ • z
  have hc : ContMDiff 𝓘(ℝ, Vector 3 × Vector 3) 𝓘(ℝ, ℝ) ∞
      (fun _ : Vector 3 × Vector 3 ↦ ε⁻¹) := contMDiff_const
  have hπ : ContMDiff 𝓘(ℝ, Vector 3 × Vector 3) 𝓘(ℝ, Vector 3 × Vector 3) ∞ π :=
    hc.smul contMDiff_id
  have he : pairMap = π ∘ scaledPair ε := by
    funext w
    exact (inv_smul_smul₀ hε (pairMap w)).symm
  have hi := injective_mfderiv_pairMap q
  rw [he, mfderiv_comp q (hπ.mdifferentiableAt (by simp))
    ((contMDiff_scaledPair ε).mdifferentiableAt (by simp))] at hi
  intro v w hvw
  apply hi
  exact congrArg (mfderiv 𝓘(ℝ, Vector 3 × Vector 3)
    𝓘(ℝ, Vector 3 × Vector 3) π (scaledPair ε q)) hvw

theorem scaledPair_mem_product {ε : ℝ} (hε : 0 < ε) (q : Parameter) :
    scaledPair ε q ∈ closedBall (0 : Vector 3) ε ×ˢ closedBall (0 : Vector 3) ε := by
  have hnorm (w : Parameter) : ‖ε • radialMap w‖ ≤ ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε, norm_radialMap]
    nlinarith [profile_lt_one w.1]
  exact ⟨by simpa [scaledPair, pairMap, mem_closedBall, dist_zero_right] using hnorm q,
    by simpa [scaledPair, pairMap, mem_closedBall, dist_zero_right] using hnorm (reverse q)⟩

theorem scaledPair_fst_eq_zero_iff {ε : ℝ} (hε : ε ≠ 0) (q : Parameter) :
    (scaledPair ε q).1 = 0 ↔ q.1 ≤ -1 := by
  change ε • (pairMap q).1 = 0 ↔ _
  rw [smul_eq_zero, or_iff_right hε, pairMap_fst_eq_zero_iff]

theorem scaledPair_snd_eq_zero_iff {ε : ℝ} (hε : ε ≠ 0) (q : Parameter) :
    (scaledPair ε q).2 = 0 ↔ 1 ≤ q.1 := by
  change ε • (pairMap q).2 = 0 ↔ _
  rw [smul_eq_zero, or_iff_right hε, pairMap_snd_eq_zero_iff]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)

def chartNeck (ε : ℝ) (q : Parameter) : M := Φ (scaledPair ε q)

variable {ε : ℝ} (hε : 0 < ε)
  (hprod : closedBall (0 : Vector 3) ε ×ˢ closedBall (0 : Vector 3) ε ⊆ Φ.source)

include hε hprod

theorem scaledPair_mem_source (q : Parameter) : scaledPair ε q ∈ Φ.source :=
  hprod (scaledPair_mem_product hε q)

theorem contMDiff_chartNeck : ContMDiff Model (𝓡 6) ∞ (chartNeck Φ ε) := by
  intro q
  have hlocal : IsLocalDiffeomorphAt 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) ∞ Φ
      (scaledPair ε q) := ⟨Φ, scaledPair_mem_source Φ hε hprod q, fun _ _ ↦ rfl⟩
  exact hlocal.contMDiffAt.comp q (contMDiff_scaledPair ε q)

theorem chartNeck_injective : Injective (chartNeck Φ ε) := by
  intro q w he
  exact scaledPair_injective hε.ne' (Φ.injOn
    (scaledPair_mem_source Φ hε hprod q) (scaledPair_mem_source Φ hε hprod w) he)


theorem chartNeck_mem_target (q : Parameter) : chartNeck Φ ε q ∈ Φ.target :=
  Φ.map_source (scaledPair_mem_source Φ hε hprod q)





end NoExoticSixSphere.SphereSumNeck
