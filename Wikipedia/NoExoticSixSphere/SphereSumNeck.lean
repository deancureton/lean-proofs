module

public import Wikipedia.NoExoticSixSphere.SphereSumNeckRadialCoordinates

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

@[expose] public section

/-!
# An actual smooth embedded neck between two transverse three-planes

The original parameter space is the real line times the standard two-sphere.
The two radial projections use opposite times. At least one is a genuine
local diffeomorphism, proving immersion of the full map. The exact flat
tails lie in the original coordinate three-planes; the middle avoids both.
Every closed bounded parameter cylinder is embedded in the literal six-space.
No gluing to arbitrary sphere maps is asserted here.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def reverse (q : Parameter) : Parameter := (-q.1, q.2)

theorem reverse_involutive : Involutive reverse := by
  intro q
  simp [reverse]

theorem contMDiff_reverse : ContMDiff Model Model ∞ reverse :=
  contMDiff_fst.neg.prodMk contMDiff_snd

def reverseCoordinates : PartialDiffeomorph Model Model Parameter Parameter ∞ where
  toFun := reverse
  invFun := reverse
  source := univ
  target := univ
  map_source' _ _ := mem_univ _
  map_target' _ _ := mem_univ _
  left_inv' q _ := reverse_involutive q
  right_inv' q _ := reverse_involutive q
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := contMDiff_reverse.contMDiffOn
  contMDiffOn_invFun := contMDiff_reverse.contMDiffOn

def pairMap (q : Parameter) : Vector 3 × Vector 3 := (radialMap q, radialMap (reverse q))

def neck (q : Parameter) : Vector 6 := EuclideanSpace.finAddEquivProd.symm (pairMap q)

theorem contMDiff_pairMap : ContMDiff Model 𝓘(ℝ, Vector 3 × Vector 3) ∞ pairMap :=
  contMDiff_radialMap.prodMk_space (contMDiff_radialMap.comp contMDiff_reverse)

theorem contMDiff_neck : ContMDiff Model (𝓡 6) ∞ neck :=
  EuclideanSpace.finAddEquivProd.symm.contDiff.contMDiff.comp contMDiff_pairMap

theorem pairMap_injective : Injective pairMap := by
  intro q w he
  have hleft : radialMap q = radialMap w := congrArg Prod.fst he
  have hright : radialMap (reverse q) = radialMap (reverse w) := congrArg Prod.snd he
  by_cases hq : -1 < q.1
  · have hw : -1 < w.1 := by
      apply (profile_pos_iff w.1).mp
      rw [← norm_radialMap w, ← hleft, norm_radialMap]
      exact (profile_pos_iff q.1).mpr hq
    exact radialCoordinates.injOn hq hw hleft
  · have hq' : -1 < (reverse q).1 := by dsimp [reverse]; linarith
    have hw' : -1 < (reverse w).1 := by
      apply (profile_pos_iff (reverse w).1).mp
      rw [← norm_radialMap (reverse w), ← hright, norm_radialMap]
      exact (profile_pos_iff (reverse q).1).mpr hq'
    exact reverse_involutive.injective (radialCoordinates.injOn hq' hw' hright)

theorem neck_injective : Injective neck :=
  EuclideanSpace.finAddEquivProd.symm.injective.comp pairMap_injective

theorem injective_mfderiv_pairMap (q : Parameter) :
    Injective (mfderiv Model 𝓘(ℝ, Vector 3 × Vector 3) pairMap q) := by
  have hfactor : ∃ π : Vector 3 × Vector 3 → Vector 3,
      ContMDiff 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 3) ∞ π ∧
      IsLocalDiffeomorphAt Model (𝓡 3) ∞ (π ∘ pairMap) q := by
    by_cases hq : -1 < q.1
    · exact ⟨Prod.fst, contDiff_fst.contMDiff,
        ⟨radialCoordinates, hq, fun _ _ ↦ rfl⟩⟩
    · have hq' : -1 < -q.1 := by linarith
      exact ⟨Prod.snd, contDiff_snd.contMDiff,
        ⟨reverseCoordinates.trans radialCoordinates, ⟨mem_univ _, hq'⟩, fun _ _ ↦ rfl⟩⟩
  obtain ⟨π, hπ, hd⟩ := hfactor
  have hinj := (hd.mfderivToContinuousLinearEquiv (by simp)).injective
  change Injective (mfderiv Model (𝓡 3) (π ∘ pairMap) q) at hinj
  rw [mfderiv_comp q (hπ.mdifferentiableAt (by simp))
    (contMDiff_pairMap.mdifferentiableAt (by simp))] at hinj
  intro v w hvw
  apply hinj
  exact congrArg (mfderiv 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 3) π (pairMap q)) hvw


theorem pairMap_left_collar (t : ℝ) (s : Sphere 2) (ht : t ≤ -1) :
    pairMap (t, s) = (0, profile (-t) • s.val) := by
  simp only [pairMap, radialMap, reverse, (profile_zero_iff t).mpr ht, zero_smul]

theorem pairMap_right_collar (t : ℝ) (s : Sphere 2) (ht : 1 ≤ t) :
    pairMap (t, s) = (profile t • s.val, 0) := by
  have hz : profile (-t) = 0 := (profile_zero_iff (-t)).mpr (by linarith)
  simp only [pairMap, radialMap, reverse, hz, zero_smul]

theorem pairMap_fst_eq_zero_iff (q : Parameter) : (pairMap q).1 = 0 ↔ q.1 ≤ -1 := by
  change profile q.1 • q.2.val = 0 ↔ _
  rw [smul_eq_zero, or_iff_left (ne_zero_of_mem_unit_sphere q.2), profile_zero_iff]

theorem pairMap_snd_eq_zero_iff (q : Parameter) : (pairMap q).2 = 0 ↔ 1 ≤ q.1 := by
  change profile (-q.1) • q.2.val = 0 ↔ _
  rw [smul_eq_zero, or_iff_left (ne_zero_of_mem_unit_sphere q.2), profile_zero_iff]
  constructor <;> intro h <;> linarith


end NoExoticSixSphere.SphereSumNeck
