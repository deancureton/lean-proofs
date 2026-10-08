module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.HopfProblem.DegreeCollapseMeridianProtectedCap
public import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereEmbedding
public import Wikipedia.HopfProblem.DegreeCollapseSmoothFirstMeridian
public import Wikipedia.HopfProblem.DegreeCollapseNativeLevelRetraction

@[expose] public section

/-!
# An actual embedded transverse meridian at the first positive two-handle

Relative affine perturbation embeds the whole sphere while fixing an
actual pole neighborhood. On the compact region where it can move the
sphere, its entire homotopy avoids the full belt image. The original
native meridian germ, transverse intersection, forward endpoint, and
crossing of the original zero level are retained.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding

theorem exists_embedded_preserving_belt
    {n : ℕ} {N : Type} [TopologicalSpace N] [ChartedSpace (Vector n) N]
    [IsManifold (𝓡 n) ∞ N] [T2Space N] [CompactSpace N]
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (e : EuclideanEmbedding n N) (r : TubularRetraction e) (hdim : 5 < n)
    (f : C(Hemisphere.Sphere 2, N)) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hinj : InjOn f {x | poleCutoff x = 0})
    (hderiv : ∀ x, poleCutoff x = 0 → Injective (mfderiv (𝓡 2) (𝓡 n) f x))
    (β : C(Y, N)) (honly : ∀ x y, f x = β y → x = pole) :
    ∃ g : C(Hemisphere.Sphere 2, N), ContMDiff (𝓡 2) (𝓡 n) ∞ g ∧
      IsClosedEmbedding g ∧ (∀ x, Injective (mfderiv (𝓡 2) (𝓡 n) g x)) ∧
      f.HomotopicRel g {x | poleCutoff x = 0} ∧ ∀ x y, g x = β y ↔ f x = β y := by
  let U : Set N := (range β)ᶜ
  have hU : IsOpen U := (isCompact_range β.continuous).isClosed.isOpen_compl
  have hfU : MapsTo f awayPoleCap U := by
    rintro x hx ⟨y, hy⟩
    exact pole_not_mem_awayPoleCap ((honly x y hy.symm) ▸ hx)
  obtain ⟨g, hg, hgi, hgd, H, hHU⟩ :=
    RelativeTwoSphere.exists_relative_embedding_in_open_on_compact e r hdim f hf
      poleCutoff poleCutoff_smooth poleCutoff_nonneg poleCutoff_norm_le_one hinj hderiv
      awayPoleCap awayPoleCap_compact U hU hfU
  have hrel : f.HomotopicRel g {x | poleCutoff x = 0} := ⟨H⟩
  have hgU : MapsTo g awayPoleCap U := by
    intro x hx
    exact (H.map_one_left x) ▸ hHU 1 x hx
  refine ⟨g, hg, hgi, hgd, hrel, ?_⟩
  intro x y
  by_cases hx : x ∈ awayPoleCap
  · constructor
    · intro hxy
      exact (hgU hx ⟨y, hxy.symm⟩).elim
    · intro hxy
      exact (hfU hx ⟨y, hxy.symm⟩).elim
  · rw [← hrel.fst_eq_snd (poleCutoff_zero_outside x hx)]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation

variable {B : Type} [TopologicalSpace B] [SimplyConnectedSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)


end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
