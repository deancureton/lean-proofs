module

import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public import Wikipedia.SmoothSixDPoincare.CompactLocalDiffeomorph
public import Wikipedia.NoExoticSixSphere.LocalInverse
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Actual height coordinates along a compact regular arc

The map `(s,z) ↦ (F(s,z),z)` has invertible derivative whenever its
scalar-direction derivative is nonzero. Injectivity on a compact center
arc gives one partial smooth chart, with all transverse coordinates retained.
This is a step towards joining the two critical-point coordinate germs.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularHeightCoordinates

open Wikipedia.SmoothSixDPoincare NoExoticSixSphere

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def heightMap (F : ℝ × V → ℝ) (p : ℝ × V) : ℝ × V := (F p, p.2)

theorem linear_decomposition (L : ℝ × V →L[ℝ] ℝ) (s : ℝ) (z : V) :
    L (s, z) = s * L (1, 0) + L (0, z) := by
  have he : (s, z) = s • (1, (0 : V)) + (0, z) := by simp
  rw [he, map_add, map_smul]
  rfl

theorem triangular_bijective (L : ℝ × V →L[ℝ] ℝ) (hL : L (1, 0) ≠ 0) :
    Function.Bijective (L.prod (ContinuousLinearMap.snd ℝ ℝ V)) := by
  constructor
  · rintro ⟨s, z⟩ ⟨t, w⟩ h
    have hzw : z = w := congrArg Prod.snd h
    subst w
    have he : L (s, z) = L (t, z) := congrArg Prod.fst h
    rw [linear_decomposition L s z, linear_decomposition L t z] at he
    have hst : s = t := (mul_right_cancel₀ hL) (by linarith)
    exact Prod.ext hst rfl
  · rintro ⟨s, z⟩
    refine ⟨((s - L (0, z)) / L (1, 0), z), ?_⟩
    apply Prod.ext
    · change L ((s - L (0, z)) / L (1, 0), z) = s
      rw [linear_decomposition L, div_mul_cancel₀ _ hL]
      ring
    · rfl

variable [FiniteDimensional ℝ V]

def triangularEquiv (L : ℝ × V →L[ℝ] ℝ) (hL : L (1, 0) ≠ 0) :
    (ℝ × V) ≃L[ℝ] (ℝ × V) :=
  (LinearEquiv.ofBijective (L.prod (ContinuousLinearMap.snd ℝ ℝ V)).toLinearMap
    (triangular_bijective L hL)).toContinuousLinearEquiv

omit [FiniteDimensional ℝ V] in
theorem contDiff_heightMap {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (heightMap F) := hF.prodMk contDiff_snd

omit [FiniteDimensional ℝ V] in
theorem fderiv_heightMap {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F) (p : ℝ × V) :
    fderiv ℝ (heightMap F) p =
      (fderiv ℝ F p).prod (ContinuousLinearMap.snd ℝ ℝ V) :=
  (((hF.differentiable (by simp) p).hasFDerivAt).prodMk
    (ContinuousLinearMap.snd ℝ ℝ V).hasFDerivAt).fderiv

theorem heightMap_localDiffeomorph {F : ℝ × V → ℝ} (hF : ContDiff ℝ ∞ F)
    {p : ℝ × V} (hreg : fderiv ℝ F p (1, 0) ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ (heightMap F) p := by
  have hinv : (fderiv ℝ (heightMap F) p).IsInvertible := by
    refine ⟨triangularEquiv (fderiv ℝ F p) hreg, ?_⟩
    rw [fderiv_heightMap hF]
    rfl
  obtain ⟨Φ, hp, _, hΦ⟩ := exists_partialDiffeomorph_of_contDiffOn
    isOpen_univ (mem_univ p) (contDiff_heightMap hF).contDiffOn hinv
  exact ⟨Φ, hp, fun _ _ => congrFun hΦ.symm _⟩


end Wikipedia.HopfProblem.DegreeCollapse.RegularHeightCoordinates
