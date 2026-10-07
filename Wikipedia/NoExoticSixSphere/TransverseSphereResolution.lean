module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.NoExoticSixSphere.SphereSumOpeningHomotopy
public import Wikipedia.SmoothSixDPoincare.TransverseSheetChart

@[expose] public section

/-!
# A global immersed resolution constructed from actual transverse sphere maps

Native transversality at the common source-chart center constructs the
simultaneous target chart and a sufficient radius. No target straightening
chart is assumed. The resulting globally smooth immersed sphere has the
specified original cap maps and is homotopic to a map collapsing the original
equator to the common value.

Identifying that collapsed map with sphere addition, and comparing actual
double points and frame parity, are still required for the quadratic identity.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem contMDiff_sourceChart : ContMDiff (𝓡 3) (𝓡 3) ∞ sourceChart := by
  rw [← contMDiffOn_univ, ← sourceChart_source]
  exact sourceChart.contMDiffOn_toFun

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (F G : Sphere 3 → M)

theorem sourceChart_transversality (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) F (sourceChart 0)).coprod
      (mfderiv (𝓡 3) (𝓡 6) G (sourceChart 0)))) :
    Surjective ((mfderiv (𝓡 3) (𝓡 6) (F ∘ sourceChart) 0).coprod
      (mfderiv (𝓡 3) (𝓡 6) (G ∘ sourceChart) 0)) := by
  have hlocal : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ sourceChart 0 :=
    ⟨sourceChart, by rw [sourceChart_source]; trivial, fun _ _ ↦ rfl⟩
  have hs := (hlocal.mfderivToContinuousLinearEquiv (by simp)).surjective
  change Surjective (mfderiv (𝓡 3) (𝓡 3) sourceChart 0) at hs
  rw [mfderiv_comp 0 (hF.mdifferentiableAt (by simp)) (hlocal.mdifferentiableAt (by simp)),
    mfderiv_comp 0 (hG.mdifferentiableAt (by simp)) (hlocal.mdifferentiableAt (by simp))]
  intro z
  obtain ⟨⟨u, v⟩, huv⟩ := ht z
  obtain ⟨u', hu⟩ := hs u
  obtain ⟨v', hv⟩ := hs v
  refine ⟨(u', v'), ?_⟩
  change ((mfderiv (𝓡 3) (𝓡 6) F (sourceChart 0)).coprod
    (mfderiv (𝓡 3) (𝓡 6) G (sourceChart 0)))
      (mfderiv (𝓡 3) (𝓡 3) sourceChart 0 u', mfderiv (𝓡 3) (𝓡 3) sourceChart 0 v') = z
  rw [hu, hv]
  exact huv

variable [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]


end NoExoticSixSphere.SphereSumNeck
