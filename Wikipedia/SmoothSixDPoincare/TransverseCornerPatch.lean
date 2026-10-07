module

public import Wikipedia.SmoothSixDPoincare.CleanTransverseSheetChart

@[expose] public section

/-!
# A constructed clean corner between two transverse embedded sheets

Choose a unit direction in each sheet. The native transverse chart then gives
an actual embedded immersive planar corner. Its two axes agree with the sheet
arcs, and its off-axis points avoid both full sheet patch images. Smoothness
holds on an open ambient neighborhood of a positive-size closed quadrant,
including its corner and both boundary edges.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare.TransverseCoordinates

variable {D Z : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def cornerLinear (u : D) (v : Z) : (ℝ × ℝ) →L[ℝ] (D × Z) :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v)

theorem cornerLinear_apply (u : D) (v : Z) (p : ℝ × ℝ) :
    cornerLinear u v p = (p.1 • u, p.2 • v) := rfl

theorem injective_cornerLinear {u : D} {v : Z} (hu : u ≠ 0) (hv : v ≠ 0) :
    Injective (cornerLinear u v) := by
  intro p q hpq
  exact Prod.ext ((smul_left_injective ℝ hu) (congrArg Prod.fst hpq))
    ((smul_left_injective ℝ hv) (congrArg Prod.snd hpq))

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞)

def cornerMap (u : D) (v : Z) : (ℝ × ℝ) → M := Φ ∘ cornerLinear u v

theorem contMDiffOn_cornerMap (u : D) (v : Z) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (cornerMap Φ u v)
      (cornerLinear u v ⁻¹' Φ.source) :=
  Φ.contMDiffOn_toFun.comp (cornerLinear u v).contDiff.contMDiff.contMDiffOn (fun _ hx => hx)

theorem injOn_cornerMap {u : D} {v : Z} (hu : u ≠ 0) (hv : v ≠ 0) :
    InjOn (cornerMap Φ u v) (cornerLinear u v ⁻¹' Φ.source) := by
  intro p hp q hq heq
  exact injective_cornerLinear hu hv (Φ.toPartialEquiv.injOn hp hq heq)

theorem injective_mfderiv_cornerMap {u : D} {v : Z} (hu : u ≠ 0) (hv : v ≠ 0)
    {p : ℝ × ℝ} (hp : p ∈ cornerLinear u v ⁻¹' Φ.source) :
    Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (cornerMap Φ u v) p) := by
  have hL : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, D × Z) ∞ (cornerLinear u v) :=
    (cornerLinear u v).contDiff.contMDiff
  rw [cornerMap, mfderiv_comp p (Φ.mdifferentiableAt (by simp) hp)
    (hL.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, (cornerLinear u v).fderiv]
  exact (PartialChart.bijective_mfderiv Φ hp).1.comp (injective_cornerLinear hu hv)

end Wikipedia.SmoothSixDPoincare.TransverseCoordinates

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]


end Wikipedia.SmoothSixDPoincare
